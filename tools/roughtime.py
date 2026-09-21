#!/usr/bin/env python3
"""A Roughtime client: the external freshness evidence D10 and FLR-003 ask for.

Roughtime (draft-ietf-ntp-roughtime) is a signed, nonce-bound time statement.
A client picks 32 unpredictable octets, a server answers with an Ed25519
signature over a midpoint and a radius together with a Merkle proof that the
client's own nonce was in the batch that response covers.  A recorded response
is therefore evidence that the recording node existed at or after that time,
and an old snapshot cannot manufacture one.

This client speaks the deployed "RoughTime v1" profile the servers in
`tools/roughtime_servers.json` answer: a little-endian tagged message, PAD to
at least 1024 octets, no outer framing header, a SHA-512 Merkle tree with
64-octet nodes, and the two NUL-terminated signature context strings.

What this module does NOT do: decide anything.  It parses octets, checks the
two signatures and the Merkle path through `tools/crypto_host`, and hands ten
fields to ACL2, which owns the anchor statement, what the signature covers,
the ordering and the restore rule (`books/anchor.lisp`).

The tenth field is ROOT, off the wire.  ACL2 rebuilds the signed octets from
it rather than recomputing it from the nonce, so the message the model reasons
about is the message the host verified, for a batch of any size; and
`fn-anchor-one-nonce-p` then reports the batches the model cannot fold as
uncertain rather than accepting them.  `Anchor.one_nonce` below is the host's
half of that: PATH empty and INDX zero, which is exactly when `merkle_root`
returned `_leaf(nonce)`.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import socket
import struct
import sys

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools import crypto_host  # noqa: E402

SERVERS_PATH = ROOT / "tools" / "roughtime_servers.json"

# The two profile context strings, each NUL-terminated.  ACL2 holds the
# response context too (`*fn-anchor-response-context*`) because it rebuilds the
# signed octets itself; `tests/test_anchor.py` pins the two against each other
# so a divergence is a test failure rather than a second grammar.
DELEGATION_CONTEXT = b"RoughTime v1 delegation signature--\x00"
RESPONSE_CONTEXT = b"RoughTime v1 response signature\x00"

NONCE_OCTETS = 32
ROOT_OCTETS = 64
SIGNATURE_OCTETS = 64
PUBLIC_KEY_OCTETS = 32
MIN_REQUEST_OCTETS = 1024
MAX_RESPONSE_OCTETS = 4096
MAX_TAGS = 32
MAX_PATH_NODES = 32


class RoughtimeError(RuntimeError):
    """The response is not a well-formed, verifiable Roughtime response."""


def _tag(name):
    return name + b"\x00" * (4 - len(name))


def encode_message(fields):
    """Encode a tagged message: tags ascend by their little-endian uint32."""
    items = sorted(((_tag(name), value) for name, value in fields),
                   key=lambda item: struct.unpack("<I", item[0])[0])
    offsets, running = [], 0
    for _, value in items[:-1]:
        running += len(value)
        offsets.append(running)
    out = struct.pack("<I", len(items))
    out += b"".join(struct.pack("<I", offset) for offset in offsets)
    out += b"".join(name for name, _ in items)
    out += b"".join(value for _, value in items)
    return out


def decode_message(message, limit=MAX_TAGS):
    """Parse a tagged message.  Every bound is checked before any traversal."""
    if len(message) < 4:
        raise RoughtimeError("message shorter than its tag count")
    count = struct.unpack_from("<I", message, 0)[0]
    if not 1 <= count <= limit:
        raise RoughtimeError("tag count {} outside 1..{}".format(count, limit))
    header = 4 + 4 * (count - 1) + 4 * count
    if len(message) < header:
        raise RoughtimeError("message shorter than its header")
    offsets = [0] + [struct.unpack_from("<I", message, 4 + 4 * i)[0]
                     for i in range(count - 1)]
    body = len(message) - header
    previous = 0
    for offset in offsets:
        # Offsets are cumulative value lengths, so they never decrease; equal
        # neighbours are a zero-length value, which an empty PATH really is.
        if offset > body or offset < previous:
            raise RoughtimeError("value offset outside the message")
        previous = offset
    names = [message[header - 4 * count + 4 * i:header - 4 * count + 4 * i + 4]
             for i in range(count)]
    if names != sorted(names, key=lambda name: struct.unpack("<I", name)[0]):
        raise RoughtimeError("tags are not in ascending order")
    fields = {}
    for index, name in enumerate(names):
        start = header + offsets[index]
        end = header + (offsets[index + 1] if index + 1 < count else body)
        if end < start:
            raise RoughtimeError("value offsets decrease")
        fields[name] = message[start:end]
    return fields


def request_packet(nonce):
    """The request: the nonce and enough padding to reach 1024 octets."""
    if len(nonce) != NONCE_OCTETS:
        raise RoughtimeError("a nonce is exactly 32 octets")
    bare = encode_message([(b"NONC", nonce), (b"PAD\xff", b"")])
    padding = max(0, MIN_REQUEST_OCTETS - len(bare))
    return encode_message([(b"NONC", nonce), (b"PAD\xff", b"\x00" * padding)])


def _leaf(nonce):
    return hashlib.sha512(b"\x00" + nonce).digest()


def _node(left, right):
    return hashlib.sha512(b"\x01" + left + right).digest()


def merkle_root(nonce, path, index):
    """Recompute the tree root the response claims covered this nonce."""
    if len(path) % ROOT_OCTETS:
        raise RoughtimeError("PATH is not a whole number of nodes")
    nodes = len(path) // ROOT_OCTETS
    if nodes > MAX_PATH_NODES:
        raise RoughtimeError("PATH deeper than {} nodes".format(MAX_PATH_NODES))
    if index >> nodes:
        raise RoughtimeError("INDX does not fit the PATH depth")
    value = _leaf(nonce)
    for step in range(nodes):
        sibling = path[step * ROOT_OCTETS:(step + 1) * ROOT_OCTETS]
        if (index >> step) & 1:
            value = _node(sibling, value)
        else:
            value = _node(value, sibling)
    return value


def _uint(value, width, name):
    if len(value) != width:
        raise RoughtimeError("{} is not {} octets".format(name, width))
    return struct.unpack("<Q" if width == 8 else "<I", value)[0]


class Anchor:
    """The ten fields ACL2 takes, plus the octets they were carried in."""

    __slots__ = ("key_id", "delegate", "mint", "maxt", "delegation_signature",
                 "midpoint", "radius", "nonce", "signature", "srep", "dele",
                 "root", "path", "index", "server")

    def __init__(self, key_id, delegate, mint, maxt, delegation_signature,
                 midpoint, radius, nonce, signature, srep, dele, root,
                 path, index, server):
        self.key_id = key_id
        self.delegate = delegate
        self.mint = mint
        self.maxt = maxt
        self.delegation_signature = delegation_signature
        self.dele = dele
        self.midpoint = midpoint
        self.radius = radius
        self.nonce = nonce
        self.signature = signature
        self.srep = srep
        self.root = root
        self.path = path
        self.index = index
        self.server = server

    @property
    def one_nonce(self):
        """Does this response cover one nonce, and is it ours?

        `parse_response` has already checked `merkle_root(nonce, path, index)
        == root`, and `merkle_root` with an empty PATH and INDX 0 is exactly
        `_leaf(nonce)`.  So an empty path and a zero index say `root ==
        _leaf(nonce)` -- which is `fn-anchor-one-nonce-p` of the record ACL2
        admits, under the same A-CRYPTO reading that makes this module's
        Ed25519 the constrained `fn-anchor-sig-verify`: that `_leaf` realises
        `fn-anchor-leaf-digest`.  That reading is named in specs/anchor.md's
        trust section; nothing here proves it.

        A non-empty PATH makes this False, and `run_store` hands ACL2 a False
        `one_nonce` alongside its Ed25519 verdict; the model then answers
        `:uncertain :unmodelled-tree`.  Uncertain and not refused: every
        signature in such a response is good and fn simply cannot tell
        whether it covers this node's nonce.
        `tests/vectors/roughtime-int08h-2026-09-19-later2.json` is a real
        int08h capture of exactly this shape, so batching is what the servers
        fn queries actually do, not a hypothetical.
        """
        return len(self.path) == 0 and self.index == 0

    def as_json(self):
        return {
            "format": "fn-anchor-1",
            "server": self.server,
            "key_id_hex": self.key_id.hex(),
            "delegate_hex": self.delegate.hex(),
            "mint_us": self.mint,
            "maxt_us": self.maxt,
            "delegation_signature_hex": self.delegation_signature.hex(),
            "dele_hex": self.dele.hex(),
            "midpoint_us": self.midpoint,
            "radius_us": self.radius,
            "nonce_hex": self.nonce.hex(),
            "signature_hex": self.signature.hex(),
            "root_hex": self.root.hex(),
            "path_hex": self.path.hex(),
            "index": self.index,
            "srep_hex": self.srep.hex(),
        }

    @classmethod
    def from_json(cls, value):
        return cls(bytes.fromhex(value["key_id_hex"]),
                   bytes.fromhex(value["delegate_hex"]),
                   value["mint_us"], value["maxt_us"],
                   bytes.fromhex(value["delegation_signature_hex"]),
                   value["midpoint_us"], value["radius_us"],
                   bytes.fromhex(value["nonce_hex"]),
                   bytes.fromhex(value["signature_hex"]),
                   bytes.fromhex(value["srep_hex"]),
                   bytes.fromhex(value["dele_hex"]),
                   bytes.fromhex(value["root_hex"]),
                   bytes.fromhex(value["path_hex"]), value["index"],
                   value["server"])

    def fields(self):
        """The ten fields `books/anchor.lisp` takes, in its own order."""
        return (self.key_id, self.delegate, self.mint, self.maxt,
                self.delegation_signature, self.midpoint, self.radius,
                self.nonce, self.signature, self.root)


def parse_response(packet, nonce, long_term_key, server="unknown"):
    """Parse and fully check one response.  Raises unless every check passes.

    Checked here: the tagged structure and its bounds, the delegation
    certificate under the pinned long-term key, the delegation validity window
    around the midpoint, the response signature under the delegated key, and
    the Merkle path from this client's own nonce to the signed root.
    """
    if not 4 <= len(packet) <= MAX_RESPONSE_OCTETS:
        raise RoughtimeError("response length {} out of range".format(len(packet)))
    if len(long_term_key) != PUBLIC_KEY_OCTETS:
        raise RoughtimeError("a pinned long-term key is exactly 32 octets")
    top = decode_message(packet)
    for name in (b"SIG\x00", b"SREP", b"CERT", b"INDX", b"PATH"):
        if name not in top:
            raise RoughtimeError("response has no {} tag".format(name))
    cert = decode_message(top[b"CERT"])
    if b"DELE" not in cert or b"SIG\x00" not in cert:
        raise RoughtimeError("CERT has no DELE or SIG")
    if not crypto_host.verify(long_term_key, DELEGATION_CONTEXT + cert[b"DELE"],
                              cert[b"SIG\x00"]):
        raise RoughtimeError("delegation certificate does not verify under the pinned key")
    dele = decode_message(cert[b"DELE"])
    for name in (b"PUBK", b"MINT", b"MAXT"):
        if name not in dele:
            raise RoughtimeError("DELE has no {} tag".format(name))
    if len(dele[b"PUBK"]) != PUBLIC_KEY_OCTETS:
        raise RoughtimeError("delegated key is not 32 octets")
    srep_octets = top[b"SREP"]
    if not crypto_host.verify(dele[b"PUBK"], RESPONSE_CONTEXT + srep_octets,
                              top[b"SIG\x00"]):
        raise RoughtimeError("response signature does not verify under the delegated key")
    srep = decode_message(srep_octets)
    for name in (b"MIDP", b"RADI", b"ROOT"):
        if name not in srep:
            raise RoughtimeError("SREP has no {} tag".format(name))
    midpoint = _uint(srep[b"MIDP"], 8, "MIDP")
    radius = _uint(srep[b"RADI"], 4, "RADI")
    mint = _uint(dele[b"MINT"], 8, "MINT")
    maxt = _uint(dele[b"MAXT"], 8, "MAXT")
    # A preflight, and no longer half of anything.  `books/anchor.lisp`
    # applies this window itself, inside `fn-anchor-verifiedp-observed` --
    # the entry `tools/run_store.py` calls -- so the discharge of
    # `fn-anchor-node-accept-observed-is-node-accept`'s hypothesis no longer
    # depends on this line agreeing with books/anchor.lisp.  It stays because
    # `parse_response` is also the capture tool's only check; it goes when
    # the ordering item of HANDOFF-w11-one-owner s 3 step 4 lands.
    if not mint <= midpoint <= maxt:
        raise RoughtimeError("midpoint outside the delegation validity window")
    root = srep[b"ROOT"]
    if len(root) != ROOT_OCTETS:
        raise RoughtimeError("ROOT is not 64 octets")
    index = _uint(top[b"INDX"], 4, "INDX")
    if merkle_root(nonce, top[b"PATH"], index) != root:
        raise RoughtimeError("the Merkle path does not carry this nonce to the signed root")
    if len(top[b"SIG\x00"]) != SIGNATURE_OCTETS:
        raise RoughtimeError("SIG is not 64 octets")
    return Anchor(long_term_key, dele[b"PUBK"], mint, maxt, cert[b"SIG\x00"],
                  midpoint, radius, nonce, top[b"SIG\x00"], srep_octets,
                  cert[b"DELE"], root, top[b"PATH"], index, server)


def load_servers(path=SERVERS_PATH):
    value = json.loads(Path(path).read_bytes())
    if value.get("format") != "fn-roughtime-servers-1":
        raise RoughtimeError("unrecognized pinned-server file format")
    return {entry["name"]: entry for entry in value["servers"]}


def query(server, timeout=5.0, nonce=None):
    """One UDP exchange with one pinned server.  Network, and only network."""
    nonce = os.urandom(NONCE_OCTETS) if nonce is None else nonce
    key = base64.b64decode(server["public_key_base64"])
    infos = socket.getaddrinfo(server["host"], server["port"],
                               type=socket.SOCK_DGRAM)
    family, socktype, proto, _, address = infos[0]
    sock = socket.socket(family, socktype, proto)
    sock.settimeout(timeout)
    try:
        sock.sendto(request_packet(nonce), address)
        packet, _ = sock.recvfrom(MAX_RESPONSE_OCTETS)
    finally:
        sock.close()
    return parse_response(packet, nonce, key, server["name"]), packet


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--server", default="int08h")
    parser.add_argument("--timeout", type=float, default=5.0)
    parser.add_argument("--capture", help="write the raw response and anchor here")
    args = parser.parse_args(argv)
    servers = load_servers()
    if args.server not in servers:
        print("roughtime: no pinned server named {}".format(args.server), file=sys.stderr)
        return 5
    try:
        anchor, packet = query(servers[args.server], args.timeout)
    except (RoughtimeError, OSError, crypto_host.CryptoUnavailable) as error:
        print("roughtime: {}".format(error), file=sys.stderr)
        return 4
    if args.capture:
        record = anchor.as_json()
        record["response_hex"] = packet.hex()
        Path(args.capture).write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print("midpoint_us={} radius_us={} server={}".format(
        anchor.midpoint, anchor.radius, anchor.server))
    return 0


if __name__ == "__main__":
    sys.exit(main())
