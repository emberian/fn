#!/usr/bin/env python3
"""Check an fn node's signature verdict without trusting fn.

    fn_verify.py --node HOST[:PORT] --cafile NODE-CERT.pem --keyring KEYRING.json '<id@host>'
    fn_verify.py --node 127.0.0.1:1119 --plain --keyring KEYRING.json '<id@host>' --json
    fn_verify.py keyring-entry PRINCIPAL.bin ED-PUBLIC.bin ML-PUBLIC.pem [--generation N]

The node answers two things about an article: its bytes (`ARTICLE`) and its
own recorded verdict (`HDR :fn-verified`, specs/substrate-transport.md §5).
This tool recomputes the verdict from the bytes alone and compares.  It
imports nothing from fn and runs none of fn's binaries: the carrier layout,
the authored-source projection and the signed preimage are written here from
the specification (specs/identity.md, "Portable FN-Authorship v1 carrier"
and "The signed bytes", which gives the v1 and v2 preimages;
books/hybrid-signature.lisp and books/hybrid-carrier.lisp name the bytes),
and the signatures are checked by libraries fn does not use for them:

    Ed25519    pyca/cryptography (its bundled OpenSSL); PyNaCl (libsodium)
               as a second opinion when installed.  The node uses libsodium.
    ML-DSA-65  dilithium-py (pure-Python FIPS 204); pyca/cryptography's
               MLDSA65PublicKey as a second opinion when present.  The node
               uses OpenSSL 3.5.

Both components must verify (no classical-only fallback), and every
implementation consulted must agree, or the tool cannot decide.

Whose key is it?  The node does not publish its keyring over NNTP, so the
verifier takes a keyring file: the principals it has pinned, each with its
exact Ed25519 and ML-DSA-65 public keys.  A carrier whose principal is pinned
with other keys does not verify.  A principal that is not pinned cannot be
decided: its signature may be sound under the keys it carries, but nothing
independent says those are the principal's.

Exit codes:

    0  the node says verified by P, and the independent check verifies P
    1  the node says not verified (unverified or absent), and so does the check
    2  disagreement: the node says verified and the check fails (or names
       another principal), or the node says not verified and the check verifies
    3  cannot decide: connection, TLS or login failure, no such article, an
       unpinned principal, a malformed answer, a missing library, two
       implementations of one primitive that disagree, or a node that says
       `carried P': it holds and relays the article for a neighbour whose
       boundary allowlists P and verified nothing itself (D23).  Ask a node
       that enrolled P; the independent check is still run and reported.
    64 usage (argparse's own 2 is remapped so it never reads as disagreement)

Credentials come from FN_CLIENT_USER and FN_CLIENT_PASSWORD or from
`--credentials PATH` (mode 0600, `user password` on one line).  The password
is sent only after STARTTLS; `--plain` never logs in and is for a loopback
development node.
"""
from __future__ import annotations

import argparse
import base64
import binascii
import json
import os
from pathlib import Path
import re
import socket
import ssl
import stat
import sys

AGREE_VERIFIED, AGREE_UNVERIFIED, DISAGREE, UNDECIDED = 0, 1, 2, 3
EXIT_USAGE = 64
DEFAULT_PORT = 119

# books/hybrid-signature.lisp and books/hybrid-carrier.lisp, restated.
DOMAIN_TAG = b"fn-authored-source-hybrid-v1"     # *fn-hsig-domain-tag*
DOMAIN_TAG_V2 = b"fn-authored-source-hybrid-v2"  # *fn-hsig-v2-domain-tag*
ED_PK, ED_SIG, ML_PK, ML_SIG = 32, 64, 1952, 3309
# Carrier item 1 names the version, and each version's length field has its
# own width (fn-hsig-source-version): v1 is a u16, for sources up to 65535
# octets; v2 is a u32, for the sources above that.  Codec widths, not
# policy: how large an article a node accepts is the node's profile.
SOURCE_MAX_V1 = 65535               # *fn-hsig-v1-max-source*
SOURCE_MAX_V2 = 4294967295          # *fn-hsig-v2-max-source*
VERSIONS = {1: (DOMAIN_TAG, 2), 2: (DOMAIN_TAG_V2, 4)}  # tag, length octets
CARRIER_FIELD_MAX = 8192            # *fn-hc-max-field-octets*
CARRIER_BINARY_MAX = 5405           # *fn-hc-max-binary-octets*
CARRIER_NAME = b"fn-authorship"
# Projected out of the authored source (fn-hc-reserved-namep).  The first
# five may appear in a received article; the last two may not.
RELAY_FIELDS = {b"fn-authorship", b"path", b"xref", b"injection-date",
                b"injection-info"}
FORBIDDEN_FIELDS = {b"fn-statement", b"fn-policy"}
REQUIRED_SINGLE = (b"from", b"subject", b"date", b"message-id", b"newsgroups")
# DER SubjectPublicKeyInfo prefix for id-ml-dsa-65 (2.16.840.1.101.3.4.3.18),
# RFC 9881: SEQUENCE { SEQUENCE { OID }, BIT STRING (1952 octets) }.
ML_SPKI_PREFIX = bytes.fromhex("308207b2300b0609608648016503040312038207a100")
MAX_LINE = 16384
# This tool's own read bound: the largest v2 source plus a carrier and
# relay fields.  It bounds the work of one ARTICLE, not what fn may hold.
MAX_ARTICLE_WIRE = SOURCE_MAX_V2 + 65536


class Undecided(Exception):
    """The verifier cannot reach a verdict; the message says why."""


# ---------------------------------------------------------------- primitives

def _ed25519_implementations():
    impls = []
    try:
        from cryptography.hazmat.primitives.asymmetric import ed25519
        from cryptography.exceptions import InvalidSignature

        def pyca(pk, msg, sig):
            try:
                ed25519.Ed25519PublicKey.from_public_bytes(pk).verify(sig, msg)
                return True
            except InvalidSignature:
                return False
        impls.append(("pyca/cryptography Ed25519", pyca))
    except ImportError:
        pass
    try:
        import nacl.signing
        import nacl.exceptions

        def pynacl(pk, msg, sig):
            try:
                nacl.signing.VerifyKey(pk).verify(msg, sig)
                return True
            except nacl.exceptions.BadSignatureError:
                return False
        impls.append(("PyNaCl (libsodium) Ed25519", pynacl))
    except ImportError:
        pass
    return impls


def _ml_dsa_65_implementations():
    impls = []
    try:
        from dilithium_py.ml_dsa import ML_DSA_65

        def pure(pk, msg, sig):
            return bool(ML_DSA_65.verify(pk, msg, sig, ctx=b""))
        impls.append(("dilithium-py ML-DSA-65 (pure Python FIPS 204)", pure))
    except ImportError:
        pass
    try:
        from cryptography.hazmat.primitives.asymmetric import mldsa
        from cryptography.exceptions import InvalidSignature

        def pyca(pk, msg, sig):
            try:
                mldsa.MLDSA65PublicKey.from_public_bytes(pk).verify(sig, msg)
                return True
            except InvalidSignature:
                return False
        mldsa.MLDSA65PrivateKey.generate()       # raises if the backend lacks it
        impls.append(("pyca/cryptography ML-DSA-65", pyca))
    except Exception:           # ImportError, UnsupportedAlgorithm, old wheels
        pass
    return impls


def observe(component, impls, pk, msg, sig):
    """Every available implementation must agree; none available is undecided."""
    if not impls:
        raise Undecided("no independent {} implementation is installed".format(component))
    results = {}
    for name, verify in impls:
        try:
            results[name] = bool(verify(pk, msg, sig))
        except Exception as error:      # a malformed key is a library refusal
            results[name] = "error: {}".format(error)
    values = set(v for v in results.values())
    if len(values) != 1 or not isinstance(next(iter(values)), bool):
        raise Undecided("{} implementations disagree: {}".format(component, results))
    return next(iter(values)), sorted(results)


# ---------------------------------------------------------------- CBOR items

def _cbor_item(data, pos):
    """One canonical uint or byte-string item; returns (major, value, pos)."""
    if pos >= len(data):
        raise ValueError("truncated")
    head = data[pos]
    major, info = head >> 5, head & 31
    pos += 1
    if info < 24:
        arg = info
    elif info in (24, 25, 26, 27):
        width = 1 << (info - 24)
        if pos + width > len(data):
            raise ValueError("truncated")
        arg = int.from_bytes(data[pos:pos + width], "big")
        pos += width
        if arg < (24 if width == 1 else 1 << (4 * width)):
            raise ValueError("noncanonical")
    else:
        raise ValueError("indefinite or reserved")
    if major == 0:
        return 0, arg, pos
    if major == 2:
        if pos + arg > len(data):
            raise ValueError("truncated")
        return 2, data[pos:pos + arg], pos + arg
    raise ValueError("unexpected major type {}".format(major))


def cbor_bytes_head(n):
    if n < 24:
        return bytes([0x40 | n])
    if n < 256:
        return bytes([0x58, n])
    return bytes([0x59]) + n.to_bytes(2, "big")


def decode_carrier(binary):
    """The nine ordered items of FN-Authorship (specs/identity.md).  Item 1
    is the version, 1 or 2; the other eight have one shape in both."""
    if len(binary) > CARRIER_BINARY_MAX:
        raise ValueError("binary-limit")
    shape = [(0, tuple(VERSIONS)), (0, 1), (2, 32), (0, 1), (2, ED_PK), (0, 2),
             (2, ML_PK), (2, ED_SIG), (2, ML_SIG)]
    values, pos = [], 0
    for major, expect in shape:
        got_major, value, pos = _cbor_item(binary, pos)
        if got_major != major:
            raise ValueError("profile")
        if major == 0 and value not in (expect if isinstance(expect, tuple)
                                        else (expect,)):
            raise ValueError("profile")
        if major == 2 and len(value) != expect:
            raise ValueError("profile")
        values.append(value)
    if pos != len(binary):
        raise ValueError("trailing octets")
    return {"version": values[0],
            "principal": values[2], "ed25519": values[4], "ml-dsa-65": values[6],
            "ed25519-signature": values[7], "ml-dsa-65-signature": values[8]}


# ---------------------------------------------------------------- the article

def parse_fields(article):
    """Split an article at its first blank line into raw header lines and body.

    Returns ([(lower-name, [physical lines without CRLF])], body).  Only CRLF
    line endings are accepted, as books/article.lisp requires.
    """
    if len(article) > MAX_ARTICLE_WIRE:
        raise ValueError("article over {} octets".format(MAX_ARTICLE_WIRE))
    fields, pos = [], 0
    while True:
        end = article.find(b"\r\n", pos)
        if end < 0:
            raise ValueError("no blank line ends the header")
        line = article[pos:end]
        pos = end + 2
        if b"\n" in line or b"\r" in line:
            raise ValueError("bare CR or LF in the header")
        if line == b"":
            break
        if line[:1] in (b" ", b"\t"):
            if not fields:
                raise ValueError("continuation before any field")
            fields[-1][1].append(line)
            continue
        name, colon, _ = line.partition(b":")
        if not colon or not name or not re.fullmatch(rb"[!-9;-~]+", name):
            raise ValueError("malformed field line")
        fields.append((name.lower(), [line]))
    body = article[pos:]
    if re.search(rb"\r(?!\n)|(?<!\r)\n", body):
        raise ValueError("bare CR or LF in the body")
    return fields, body


def field_value(lines):
    first = lines[0].partition(b":")[2]
    return b"".join([first] + lines[1:])


def signed_preimage(version, principal, ed_public, ml_public, source):
    """specs/identity.md "The signed bytes": the tagged preimage of VERSION."""
    tag, length_octets = VERSIONS[version]
    return (cbor_bytes_head(len(tag)) + tag
            + bytes([version, 1]) + principal
            + bytes([1]) + ed_public
            + bytes([2]) + ml_public
            + len(source).to_bytes(length_octets, "big") + source)


def independent_check(article, msgid, keyring):
    """The verdict recomputed from the bytes.  Returns a dict with 'outcome'
    in {'verified', 'unverified'}; raises Undecided."""
    fields, body = parse_fields(article)
    names = [name for name, _ in fields]
    carriers = [lines for name, lines in fields if name == CARRIER_NAME]
    if not carriers:
        return {"outcome": "unverified", "reason": "no-carrier",
                "detail": "the article carries no FN-Authorship field"}
    if len(carriers) != 1:
        return {"outcome": "unverified", "reason": "carrier-count"}
    if any(name in FORBIDDEN_FIELDS for name in names):
        return {"outcome": "unverified", "reason": "carrier-count",
                "detail": "another reserved fn field is present"}
    value = field_value(carriers[0])
    if len(value) > CARRIER_FIELD_MAX:
        return {"outcome": "unverified", "reason": "field-limit"}
    try:
        binary = base64.b64decode(re.sub(rb"[ \t]", b"", value), validate=True)
        carrier = decode_carrier(binary)
    except (binascii.Error, ValueError) as error:
        return {"outcome": "unverified", "reason": "carrier", "detail": str(error)}

    kept = [lines for name, lines in fields if name not in RELAY_FIELDS]
    source = b"".join(line + b"\r\n" for lines in kept for line in lines) + b"\r\n" + body
    source_names = [name for name, lines in fields if name not in RELAY_FIELDS]
    if any(source_names.count(name) != 1 for name in REQUIRED_SINGLE):
        return {"outcome": "unverified", "reason": "source-profile"}
    # The version item decides the preimage, and a version carries exactly
    # the sources its length field is for: a v1 carrier on a source over
    # 65535 octets, or a v2 carrier on one that fits v1, is not fn's.
    version = carrier["version"]
    fits_v1 = len(source) <= SOURCE_MAX_V1
    if (version == 1) != fits_v1 or len(source) > SOURCE_MAX_V2:
        return {"outcome": "unverified", "reason": "carrier",
                "detail": "a version {} carrier on a {}-octet source".format(
                    version, len(source))}
    # The signed source names its own Message-ID.  A node that answered this
    # request with another signed article is not vouching for this one.
    signed_ids = [field_value(lines).strip() for name, lines in fields
                  if name == b"message-id"]
    if signed_ids != [msgid.encode("ascii")]:
        return {"outcome": "unverified", "reason": "message-id",
                "detail": "the signed source is {!r}, not {}".format(signed_ids, msgid)}

    principal = carrier["principal"]
    preimage = signed_preimage(version, principal, carrier["ed25519"],
                               carrier["ml-dsa-65"], source)
    ed_ok, ed_impls = observe("Ed25519", _ed25519_implementations(), carrier["ed25519"],
                              preimage, carrier["ed25519-signature"])
    ml_ok, ml_impls = observe("ML-DSA-65", _ml_dsa_65_implementations(),
                              carrier["ml-dsa-65"], preimage,
                              carrier["ml-dsa-65-signature"])
    result = {"principal": principal.hex(), "ed25519": ed_ok, "ml-dsa-65": ml_ok,
              "carrier-version": version,
              "implementations": ed_impls + ml_impls,
              "source-octets": len(source)}
    if not (ed_ok and ml_ok):
        result.update(outcome="unverified", reason="signature")
        return result
    pins = [entry for entry in keyring if entry["principal"] == principal]
    if not pins:
        raise Undecided("principal {} is not in the keyring; its signatures verify "
                        "under the keys it carries, but nothing independent binds "
                        "those keys to it".format(principal.hex()))
    matching = [entry for entry in pins if entry["ed25519"] == carrier["ed25519"]
                and entry["ml-dsa-65"] == carrier["ml-dsa-65"]]
    if not matching:
        result.update(outcome="unverified", reason="key-not-pinned",
                      detail="the carrier's keys are not the keys pinned for this principal")
        return result
    result.update(outcome="verified",
                  generations=[e["generation"] for e in matching if e.get("generation")])
    return result


# ---------------------------------------------------------------- the node's word

def parse_hdr_item(line):
    """`N verified HEX keyring G [policy ...]`, `N verified legacy keyring G`,
    `N unverified REASON keyring G`, `N absent REASON`, `N carried HEX`."""
    parts = line.split()
    if len(parts) < 3 or not parts[0].isdigit():
        raise Undecided("malformed HDR :fn-verified line {!r}".format(line))
    token = parts[1]
    if token == "verified" and len(parts) >= 5 and parts[3] == "keyring":
        if parts[2] == "legacy":
            raise Undecided("the node's verdict is a legacy record naming no principal")
        if not re.fullmatch(r"[0-9a-fA-F]{64}", parts[2]):
            raise Undecided("the node's verified line names no principal: {!r}".format(line))
        return {"outcome": "verified", "principal": parts[2].lower(), "keyring": parts[4]}
    if token == "unverified":
        return {"outcome": "unverified", "reason": parts[2],
                "keyring": parts[4] if len(parts) >= 5 else None}
    if token == "absent":
        return {"outcome": "absent", "reason": parts[2]}
    if token == "carried":
        if not re.fullmatch(r"[0-9a-fA-F]{64}", parts[2]):
            raise Undecided("the node's carried line names no principal: {!r}".format(line))
        return {"outcome": "carried", "principal": parts[2].lower()}
    if token == "revoked" and len(parts) >= 5 and parts[3] == "keyring":
        # SPIKE (spike/peering): the fifth token.  The node holds the article
        # under keys it once enrolled for this principal and has since
        # revoked at keyring generation G; it is not `verified'.
        if not re.fullmatch(r"[0-9a-fA-F]{64}", parts[2]):
            raise Undecided("the node's revoked line names no principal: {!r}".format(line))
        return {"outcome": "revoked", "principal": parts[2].lower(), "keyring": parts[4]}
    raise Undecided("unknown HDR :fn-verified token in {!r}".format(line))


class Node:
    """One NNTP session: greeting, STARTTLS, AUTHINFO, then commands."""

    def __init__(self, host, port, cafile=None, plain=False, credentials=None,
                 timeout=30.0):
        self.transcript = []
        try:
            self.sock = socket.create_connection((host, port), timeout=timeout)
        except OSError as error:
            raise Undecided("cannot connect to {}:{}: {}".format(host, port, error))
        self.reader = self.sock.makefile("rb")
        greeting = self.line()
        if not greeting.startswith(("200", "201")):
            raise Undecided("the node greeted {!r}".format(greeting))
        if plain:
            return
        status = self.command("STARTTLS")
        if not status.startswith("382"):
            raise Undecided("STARTTLS answered {!r}".format(status))
        context = ssl.create_default_context(cafile=cafile)
        try:
            self.sock = context.wrap_socket(self.sock, server_hostname=host)
        except (ssl.SSLError, OSError) as error:
            raise Undecided("TLS handshake failed: {}".format(error))
        self.reader = self.sock.makefile("rb")
        if credentials:
            user, password = credentials
            status = self.command("AUTHINFO USER " + user)
            if status.startswith("381"):
                status = self.command("AUTHINFO PASS " + password, record="AUTHINFO PASS ****")
            if not status.startswith("281"):
                raise Undecided("login refused: {!r}".format(status))

    def line(self):
        raw = self.reader.readline(MAX_LINE + 2)
        if not raw.endswith(b"\r\n"):
            raise Undecided("the connection ended or sent an overlong line")
        text = raw[:-2].decode("utf-8", "replace")
        self.transcript.append("< " + text[:200])
        return text

    def command(self, text, record=None):
        self.transcript.append("> " + (record or text))
        try:
            self.sock.sendall(text.encode("ascii") + b"\r\n")
        except OSError as error:
            raise Undecided("send failed: {}".format(error))
        return self.line()

    def multiline(self):
        """The data block after a 2xx, dot-unstuffed, as CRLF octets."""
        out, total = [], 0
        while True:
            raw = self.reader.readline(MAX_LINE + 2)
            if not raw.endswith(b"\r\n"):
                raise Undecided("the data block ended early or had an overlong line")
            if raw == b".\r\n":
                return b"".join(out)
            if raw.startswith(b"."):
                raw = raw[1:]
            total += len(raw)
            if total > MAX_ARTICLE_WIRE:
                raise Undecided("the data block exceeds {} octets".format(MAX_ARTICLE_WIRE))
            out.append(raw)

    def close(self):
        try:
            self.command("QUIT")
        except Undecided:
            pass
        try:
            self.sock.close()
        except OSError:
            pass


def ask_node(node, msgid):
    """(article octets or None, parsed HDR claim or None, raw HDR line)."""
    status = node.command("ARTICLE " + msgid)
    if status.startswith("430"):
        article = None
    elif status.startswith("220"):
        article = node.multiline()
    else:
        raise Undecided("ARTICLE answered {!r}".format(status))
    status = node.command("HDR :fn-verified " + msgid)
    if status.startswith("430"):
        return article, None, None
    if not status.startswith("225"):
        raise Undecided("HDR :fn-verified answered {!r}".format(status))
    block = node.multiline().decode("utf-8", "replace").splitlines()
    if len(block) != 1:
        raise Undecided("HDR :fn-verified returned {} lines for one Message-ID".format(len(block)))
    return article, parse_hdr_item(block[0]), block[0]


def compare(claim, check):
    node_verified = claim["outcome"] == "verified"
    check_verified = check["outcome"] == "verified"
    if node_verified and check_verified:
        if claim["principal"] != check["principal"]:
            return DISAGREE, "the node names principal {} but the signature is {}'s".format(
                claim["principal"], check["principal"])
        return AGREE_VERIFIED, "verified by {}: the node and the independent check agree".format(
            check["principal"])
    if not node_verified and not check_verified:
        return AGREE_UNVERIFIED, "not verified: the node says {} and the independent check says {}".format(
            claim["outcome"], check.get("reason"))
    if node_verified:
        return DISAGREE, "the node claims verified by {}, the independent check says {}".format(
            claim["principal"], check.get("reason"))
    return DISAGREE, "the node says {}, but the signature verifies under the pinned keys of {}".format(
        claim["outcome"], check["principal"])


# ---------------------------------------------------------------- keyring

def ml_public_from_pem(text):
    body = re.sub(r"-----[^-]+-----|\s", "", text)
    der = base64.b64decode(body, validate=True)
    if len(der) != len(ML_SPKI_PREFIX) + ML_PK or not der.startswith(ML_SPKI_PREFIX):
        raise ValueError("not an ML-DSA-65 SubjectPublicKeyInfo")
    return der[len(ML_SPKI_PREFIX):]


def load_keyring(path):
    """{"format": "fn-verify-keyring-v1", "principals": [{"principal": HEX64,
    "ed25519": HEX64, "ml-dsa-65": HEX3904, "generation": N?}, ...]}"""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if data.get("format") != "fn-verify-keyring-v1":
        raise ValueError("keyring format must be fn-verify-keyring-v1")
    entries = []
    for item in data.get("principals", []):
        entry = {"principal": bytes.fromhex(item["principal"]),
                 "ed25519": bytes.fromhex(item["ed25519"]),
                 "ml-dsa-65": bytes.fromhex(item["ml-dsa-65"]),
                 "generation": item.get("generation")}
        if (len(entry["principal"]), len(entry["ed25519"]), len(entry["ml-dsa-65"])) != (32, ED_PK, ML_PK):
            raise ValueError("keyring entry has wrong key widths")
        entries.append(entry)
    return entries


def keyring_entry(principal_path, ed_path, ml_pem_path, generation):
    principal = Path(principal_path).read_bytes()
    ed = Path(ed_path).read_bytes()
    ml = ml_public_from_pem(Path(ml_pem_path).read_text(encoding="ascii"))
    if len(principal) != 32 or len(ed) != ED_PK:
        raise ValueError("principal must be 32 octets and the Ed25519 key 32 octets")
    entry = {"principal": principal.hex(), "ed25519": ed.hex(), "ml-dsa-65": ml.hex()}
    if generation is not None:
        entry["generation"] = generation
    return entry


# ---------------------------------------------------------------- command line

def credentials_from(args):
    if args.credentials:
        path = Path(args.credentials)
        if stat.S_IMODE(path.stat().st_mode) & 0o077:
            raise Undecided("{} must be mode 0600".format(path))
        user, _, password = path.read_text(encoding="utf-8").strip().partition(" ")
        return user, password
    user, password = os.environ.get("FN_CLIENT_USER"), os.environ.get("FN_CLIENT_PASSWORD")
    return (user, password) if user and password else None


def split_node(text):
    """HOST, HOST:PORT, [HOST] or [HOST]:PORT (RFC 3986 section 3.2.2)."""
    match = re.fullmatch(r"\[([^\]]+)\](?::(\d+))?", text)
    if match:
        host, port = match.groups()
    elif text.count(":") == 1:
        host, port = text.split(":")
    else:
        host, port = text, None
    return host, int(port) if port else DEFAULT_PORT


def verify(args):
    report = {"message-id": args.msgid}
    node = None
    try:
        keyring = load_keyring(args.keyring)
        host, port = split_node(args.node)
        node = Node(host, port, cafile=args.cafile, plain=args.plain,
                    credentials=None if args.plain else credentials_from(args),
                    timeout=args.timeout)
        article, claim, raw = ask_node(node, args.msgid)
        report["node-hdr"] = raw
        if article is None or claim is None:
            raise Undecided("the node holds no article {}".format(args.msgid))
        report["article-octets"] = len(article)
        try:
            check = independent_check(article, args.msgid, keyring)
        except ValueError as error:
            raise Undecided("the served article does not parse: {}".format(error))
        except Undecided as error:
            if claim["outcome"] != "carried":
                raise
            check = {"outcome": "undecided", "reason": str(error)}
        report["node"], report["independent"] = claim, check
        if claim["outcome"] == "carried":
            # D23: the node claims nothing about the signature; there is no
            # verdict to agree or disagree with.
            raise Undecided(
                "the node carried this article for a neighbour without verifying it "
                "(it holds no enrollment of {}); ask a node that enrolled the author "
                "(the independent check here says {})".format(
                    claim["principal"],
                    check.get("reason") or check["outcome"]))
        if claim["outcome"] == "revoked":
            # SPIKE (spike/peering): the signature may well check under the
            # pinned keys; the node's word is that the principal is revoked.
            # Agreement is "not verified" (exit 1) when the independent check
            # verifies the same principal (the bytes are the revoked key's);
            # a keyring entry with "revoked": true makes the tool itself say
            # revoked.  A check that fails is a disagreement about the bytes.
            if check["outcome"] == "verified" and check.get("principal") == claim["principal"]:
                code, sentence = AGREE_UNVERIFIED, (
                    "revoked: the node revoked {} at keyring {}; the signature checks "
                    "under the pinned keys, so the bytes are the revoked key's".format(
                        claim["principal"], claim["keyring"]))
            else:
                code, sentence = DISAGREE, "the node says revoked but the check says {}".format(
                    check.get("reason") or check["outcome"])
        else:
            code, sentence = compare(claim, check)
        if code in (AGREE_VERIFIED, AGREE_UNVERIFIED) and claim["outcome"] != "revoked":
            code, sentence = control_report(node, args, article, check, report,
                                            code, sentence)
    except Undecided as error:
        code, sentence = UNDECIDED, str(error)
    except (OSError, ValueError, KeyError) as error:
        code, sentence = UNDECIDED, "{}: {}".format(type(error).__name__, error)
    finally:
        if node is not None:
            report["transcript"] = node.transcript
            node.close()
    report["exit"], report["detail"] = code, sentence
    word = {0: "verified", 1: "unverified", 2: "DISAGREE", 3: "undecided"}[code]
    if args.json:
        print(json.dumps(report, indent=1, sort_keys=True))
    else:
        print("{} {} {}".format(word, args.msgid, sentence))
    return code


def control_report(node, args, article, check, report, code, sentence):
    """spike/control: a cancel article's withdrawal, beside the node's claim.

    The node's HDR :fn-control item is its historical claim.  This checks what
    can be checked independently: the Control line (inside the signed source)
    names the target the claim names, the target is no longer served, and,
    given a copy of the target (--target-copy), that its carrier principal is
    the canceller's when the node says the basis is the author.  The
    authority basis is this node's configuration and cannot be checked here.
    """
    fields, _ = parse_fields(article)
    controls = [field_value(lines).decode("ascii", "replace")
                for name, lines in fields if name == b"control"]
    if len(controls) != 1:
        return code, sentence
    words = controls[0].split()
    if len(words) != 2 or words[0].lower() != "cancel":
        return code, sentence
    target = words[1]
    status = node.command("HDR :fn-control " + args.msgid)
    if not status.startswith("225"):
        raise Undecided("HDR :fn-control answered {!r}".format(status))
    block = node.multiline().decode("utf-8", "replace").splitlines()
    if len(block) != 1:
        raise Undecided("HDR :fn-control returned {} lines".format(len(block)))
    claim = block[0].split(" ", 1)[1] if " " in block[0] else ""
    report["node-control"] = claim
    served = not node.command("STAT " + target).startswith("430")
    report["target-served"] = served
    cw = claim.split()
    if cw[:2] == ["executed", "withdrawal"] and len(cw) == 4:
        if cw[2] != target:
            return DISAGREE, "the node's withdrawal names {} but the signed Control line names {}".format(
                cw[2], target)
        if served:
            return DISAGREE, "the node claims {} withdrawn but still serves it".format(target)
        if cw[3] == "author" and args.target_copy:
            copy = Path(args.target_copy).read_bytes()
            tcheck = independent_check(copy, target, load_keyring(args.keyring))
            if tcheck["outcome"] != "verified" or tcheck.get("principal") != check.get("principal"):
                return DISAGREE, "the node says the author withdrew {}, but the copy's author is {}".format(
                    target, tcheck.get("principal") or tcheck.get("reason"))
        return code, sentence + "; withdrawal: {} withdrawn by {} (node's report{})".format(
            target, cw[3], "" if cw[3] == "author" and args.target_copy else
            ", basis not independently checkable")
    return code, sentence + "; control: {} (node's report; target {})".format(
        claim, "served" if served else "not served")


class Parser(argparse.ArgumentParser):
    def error(self, message):
        self.print_usage(sys.stderr)
        sys.stderr.write("{}: error: {}\n".format(self.prog, message))
        sys.exit(EXIT_USAGE)


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ["keyring-entry"]:
        parser = Parser(prog="fn_verify.py keyring-entry")
        parser.add_argument("principal")
        parser.add_argument("ed_public")
        parser.add_argument("ml_public_pem")
        parser.add_argument("--generation", type=int)
        args = parser.parse_args(argv[1:])
        print(json.dumps(keyring_entry(args.principal, args.ed_public,
                                       args.ml_public_pem, args.generation)))
        return 0
    parser = Parser(prog="fn_verify.py", description=__doc__.split("\n\n")[0])
    parser.add_argument("msgid")
    parser.add_argument("--node", required=True, help="HOST, HOST:PORT or [V6]:PORT")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--cafile", help="the node's certificate (STARTTLS, verified)")
    mode.add_argument("--plain", action="store_true",
                      help="no TLS and no login: a loopback development node only")
    parser.add_argument("--keyring", required=True,
                        help="fn-verify-keyring-v1 JSON of pinned principals")
    parser.add_argument("--credentials", help="mode-0600 file: user password")
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--target-copy",
                        help="a cancel's target as the caller holds it (spike/control)")
    args = parser.parse_args(argv)
    if not re.fullmatch(r"<[!-;=?-~]+>", args.msgid):
        parser.error("the Message-ID must be <...> printable ASCII")
    return verify(args)


if __name__ == "__main__":
    sys.exit(main())
