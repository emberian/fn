#!/usr/bin/env python3
"""Operator, consumer, and NNTP client surface for the certified fn2 node.

Protocol, framing, cursor internals, grant chains, and admission verdicts are
owned exclusively by the ACL2 core (`books/authority-codec.lisp`,
`books/consumer-codec.lisp`, `books/nntp-grammar.lisp`). This module performs
socket I/O and renders the node's own replies while keeping `accepted` (exit 0),
`refused` (exit 1), usage/transport errors (exit 2), and `uncertain` (exit 3)
distinct at every boundary.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import socket
import stat
import subprocess
import sys

EXIT_ACCEPTED = 0
EXIT_REFUSED = 1
EXIT_ERROR = 2
EXIT_UNCERTAIN = 3

# --- Pure BLAKE3-256 (for FNCT frame sealing & verification) ---
_IV = (
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
)
_PERM = (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)
_CHUNK_START, _CHUNK_END, _PARENT, _ROOT = 1, 2, 4, 8
_M32 = 0xFFFFFFFF


def _g(s: list[int], a: int, b: int, c: int, d: int, x: int, y: int) -> None:
    s[a] = (s[a] + s[b] + x) & _M32
    s[d] = ((s[d] ^ s[a]) >> 16 | (s[d] ^ s[a]) << 16) & _M32
    s[c] = (s[c] + s[d]) & _M32
    s[b] = ((s[b] ^ s[c]) >> 12 | (s[b] ^ s[c]) << 20) & _M32
    s[a] = (s[a] + s[b] + y) & _M32
    s[d] = ((s[d] ^ s[a]) >> 8 | (s[d] ^ s[a]) << 24) & _M32
    s[c] = (s[c] + s[d]) & _M32
    s[b] = ((s[b] ^ s[c]) >> 7 | (s[b] ^ s[c]) << 25) & _M32


def _compress(cv: list[int], block: bytes, counter: int, blen: int, flags: int) -> list[int]:
    m = [int.from_bytes(block[4 * i:4 * i + 4], "little") for i in range(16)]
    s = list(cv) + list(_IV[:4]) + [counter & _M32, (counter >> 32) & _M32, blen, flags]
    for r in range(7):
        _g(s, 0, 4, 8, 12, m[0], m[1]); _g(s, 1, 5, 9, 13, m[2], m[3])
        _g(s, 2, 6, 10, 14, m[4], m[5]); _g(s, 3, 7, 11, 15, m[6], m[7])
        _g(s, 0, 5, 10, 15, m[8], m[9]); _g(s, 1, 6, 11, 12, m[10], m[11])
        _g(s, 2, 7, 8, 13, m[12], m[13]); _g(s, 3, 4, 9, 14, m[14], m[15])
        if r < 6:
            m = [m[p] for p in _PERM]
    return [s[i] ^ s[i + 8] for i in range(8)]


def _chunk_output(data: bytes, counter: int):
    cv = list(_IV)
    blocks = [data[i:i + 64] for i in range(0, len(data), 64)] or [b""]
    for i, blk in enumerate(blocks[:-1]):
        cv = _compress(cv, blk.ljust(64, b"\0"), counter, 64, _CHUNK_START if i == 0 else 0)
    last = blocks[-1]
    flags = (_CHUNK_START if len(blocks) == 1 else 0) | _CHUNK_END
    return cv, last.ljust(64, b"\0"), len(last), flags, counter


def blake3(data: bytes) -> bytes:
    data = bytes(data)
    chunks = [data[i:i + 1024] for i in range(0, len(data), 1024)] or [b""]
    outs = [_chunk_output(c, n) for n, c in enumerate(chunks)]
    while len(outs) > 1:
        cvs = [_compress(cv, blk, ctr, ln, fl) for cv, blk, ln, fl, ctr in outs]
        nxt = []
        for i in range(0, len(cvs) - 1, 2):
            block = b"".join(w.to_bytes(4, "little") for w in cvs[i] + cvs[i + 1])
            nxt.append((list(_IV), block, 64, _PARENT, 0))
        if len(cvs) % 2:
            nxt.append(outs[-1])
        outs = nxt
    cv, block, ln, fl, ctr = outs[0]
    words = _compress(cv, block, ctr, ln, fl | _ROOT)
    return b"".join(w.to_bytes(4, "little") for w in words)


# --- FNCT framing & layout codecs (books/layout.lisp, authority-codec.lisp, consumer-codec.lisp) ---
FNCT_MAGIC = b"FNCT"
KIND_CONTROL = 1
KIND_POSTURE = 2
KIND_CNS_REQ = 4
KIND_CNS_REPLY = 28
KIND_AUTH_REQ = 29
KIND_AUTH_REPLY = 30
CMD_STOP = 5

CLASSES = ("accepted", "refused", "uncertain", "fault")
ITEM_TYPES = ("record", "withdrawn", "reference", "gap")
EVIDENCE_TYPES = ("none", "committed", "uncertain", "refused")

AUTH_OPCODES = {
    "principal-create": 0,
    "principal-bind": 1,
    "grant-set": 2,
    "grant-get": 3,
    "stream-resolve": 4,
}
AUTH_RIGHTS = {"consume": 0, "read": 1, "append": 2}
CNS_CODES = {
    "ack": 1,
    "position": 2,
    "append": 11,
    "fetch": 13,
    "register": 14,
    "read": 15,
    "wait": 16,
    "status": 18,
}


class WireError(Exception):
    pass


class UncertainOutcome(Exception):
    def __init__(self, message: str, detail: dict | None = None):
        super().__init__(message)
        self.detail = detail or {}


def leb_encode(v: int) -> bytes:
    if v < 0:
        raise ValueError(f"negative varint: {v}")
    out = bytearray()
    while v >= 128:
        out.append(128 + (v & 0x7F))
        v >>= 7
    out.append(v)
    return bytes(out)


def leb_decode(buf: bytes, offset: int = 0) -> tuple[int, int]:
    acc = 0
    shift = 0
    i = offset
    while True:
        if i >= len(buf):
            raise WireError("truncated varint")
        b = buf[i]
        i += 1
        acc |= (b & 0x7F) << shift
        if b < 128:
            return acc, i
        shift += 7
        if shift > 63:
            raise WireError("varint overflow")


def _take(buf: bytes, offset: int, count: int, what: str) -> tuple[bytes, int]:
    """Take exactly COUNT octets, rejecting truncation before integer conversion."""
    end = offset + count
    if offset < 0 or count < 0 or end > len(buf):
        raise WireError(f"truncated {what}")
    return buf[offset:end], end


def _octets16_at(buf: bytes, offset: int, what: str) -> tuple[bytes, int]:
    raw, offset = _take(buf, offset, 2, f"{what} length")
    return _take(buf, offset, int.from_bytes(raw, "big"), what)


def _octets32_at(buf: bytes, offset: int, what: str) -> tuple[bytes, int]:
    raw, offset = _take(buf, offset, 4, f"{what} length")
    return _take(buf, offset, int.from_bytes(raw, "big"), what)


def u32be(value: int, name: str) -> bytes:
    if not (0 <= value <= 0xFFFFFFFF):
        raise ValueError(f"{name} must be in 0 .. 2^32-1")
    return value.to_bytes(4, "big")


def be_pos(n: int) -> bytes:
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")


def octets_var(b: bytes) -> bytes:
    return leb_encode(len(b)) + b


def octets16(b: bytes) -> bytes:
    if len(b) > 0xFFFF:
        raise ValueError(f"octets16 too long: {len(b)}")
    return len(b).to_bytes(2, "big") + b


def octets32(b: bytes) -> bytes:
    return len(b).to_bytes(4, "big") + b


def fnct_seal(kind: int, payload: bytes) -> bytes:
    prefix = FNCT_MAGIC + bytes([1, kind]) + len(payload).to_bytes(4, "big") + payload
    return prefix + blake3(prefix)


def fnct_open(frame: bytes) -> tuple[int, bytes]:
    if len(frame) < 42 or frame[:5] != FNCT_MAGIC + b"\x01":
        raise WireError("invalid FNCT header")
    n = int.from_bytes(frame[6:10], "big")
    if len(frame) != 42 + n or blake3(frame[:10 + n]) != frame[10 + n:]:
        raise WireError("FNCT length or BLAKE3 trailer mismatch")
    return frame[5], frame[10:10 + n]


def cursor_position(cursor: bytes) -> int:
    if len(cursor) < 21 or cursor[:4] != b"fncu":
        raise WireError("invalid fncu cursor")
    ver = cursor[4]
    if ver == 1:
        return int.from_bytes(cursor[-4:], "big")
    if ver == 2:
        return int.from_bytes(cursor[-8:], "big")
    raise WireError(f"unsupported cursor version {ver}")


def cursor_propose(cursor: bytes, position: int) -> bytes:
    """Re-send the node's issued cursor proposing POSITION (books/consumer-codec.lisp)."""
    if len(cursor) < 21 or cursor[:4] != b"fncu":
        raise WireError("invalid fncu cursor")
    ver = cursor[4]
    if ver == 1:
        if not (0 <= position < (1 << 32)):
            raise ValueError(f"v1 cursor position out of range: {position}")
        return cursor[:-4] + position.to_bytes(4, "big")
    if ver == 2:
        if not (0 <= position < (1 << 64)):
            raise ValueError(f"v2 cursor position out of range: {position}")
        return cursor[:-8] + position.to_bytes(8, "big")
    raise WireError(f"unsupported cursor version {ver}")


def encode_consumer_id(raw: str) -> bytes:
    """Encode a consumer identifier as 1..7 non-zero big-endian bytes (fn2-cns-field-cid)."""
    try:
        val = int(raw, 10)
    except ValueError:
        b = raw.encode("utf-8")
        if not (1 <= len(b) <= 7) or int.from_bytes(b, "big") == 0:
            raise ValueError("consumer name must be a positive integer or 1..7 non-zero UTF-8 bytes")
        return b
    if not (1 <= val < (1 << 56)):
        raise ValueError("consumer id must be in 1 .. 2^56-1")
    return be_pos(val)


def fresh_u60_op() -> int:
    val = int.from_bytes(os.urandom(8), "big") & ((1 << 60) - 1)
    return val if val > 0 else 1


def parse_u60_op(raw: str | None, required: bool = False) -> int:
    if raw is None:
        return fresh_u60_op() if required else 0
    val = int(raw, 0)
    if not (1 <= val < (1 << 60)):
        raise ValueError("--op must be an integer in 1 .. 2^60-1")
    return val


def build_auth_request(verb: str, **kw) -> bytes:
    code = AUTH_OPCODES[verb]
    if verb in ("principal-create", "principal-bind", "stream-resolve"):
        body = bytes([code]) + octets16(kw["name"].encode("utf-8"))
    elif verb == "grant-set":
        op_bytes = be_pos(kw["op"])
        body = (
            bytes([code])
            + leb_encode(kw["grantee"])
            + bytes([kw["right"], kw["scope"]])
            + leb_encode(kw["target"])
            + bytes([1 if kw["enabled"] else 0])
            + leb_encode(kw["expected_head"])
            + octets16(op_bytes)
        )
    elif verb == "grant-get":
        body = (
            bytes([code])
            + leb_encode(kw["grantee"])
            + bytes([kw["right"], kw["scope"]])
            + leb_encode(kw["target"])
        )
    else:
        raise ValueError(f"unknown authority verb {verb}")
    return fnct_seal(KIND_AUTH_REQ, body)


def decode_auth_reply(verb: str, frame: bytes) -> dict:
    kind, p = fnct_open(frame)
    if kind != KIND_AUTH_REPLY:
        raise WireError(f"expected kind 30 authority reply, got kind {kind}")
    if len(p) < 4:
        raise WireError("truncated kind 30 reply")
    opcode = p[0]
    if opcode != AUTH_OPCODES[verb]:
        raise WireError(f"authority reply opcode {opcode} != expected {AUTH_OPCODES[verb]}")
    if p[1] >= len(CLASSES):
        raise WireError(f"invalid FNCT class {p[1]}")
    cls = CLASSES[p[1]]
    rlen_raw, _ = _take(p, 2, 2, "authority reason length")
    rlen = int.from_bytes(rlen_raw, "big")
    reason_raw, i = _take(p, 4, rlen, "authority reason")
    reason = reason_raw.decode("ascii", errors="replace")
    out: dict = {"outcome": cls, "reason": reason or "none"}
    if cls != "accepted":
        if i != len(p):
            raise WireError("non-accepted authority reply has trailing bytes")
        return out
    if verb == "stream-resolve":
        target, i = leb_decode(p, i)
        out["target"] = target
    elif verb == "principal-create":
        pid, i = leb_decode(p, i)
        out["id"] = pid
    elif verb == "principal-bind":
        pid, i = leb_decode(p, i)
        head, i = leb_decode(p, i)
        out.update(id=pid, authority_head=head)
    elif verb == "grant-set":
        grant_id, i = leb_decode(p, i)
        head, i = leb_decode(p, i)
        receipt, i = _octets16_at(p, i, "grant-set receipt")
        out.update(grant=grant_id, authority_head=head, receipt=receipt.hex())
    elif verb == "grant-get":
        found_raw, i = _take(p, i, 1, "grant-get result")
        if found_raw[0] not in (0, 1):
            raise WireError("invalid grant-get found boolean")
        found = bool(found_raw[0])
        head, i = leb_decode(p, i)
        out.update(found=found, enabled=False, authority_head=head)
        if found:
            grant_id, i = leb_decode(p, i)
            grantor, i = leb_decode(p, i)
            enabled_raw, i = _take(p, i, 1, "grant-get-found enabled")
            if enabled_raw[0] not in (0, 1):
                raise WireError("invalid grant-get enabled boolean")
            enabled = bool(enabled_raw[0])
            prev, i = leb_decode(p, i)
            out.update(grant=grant_id, grantor=grantor, enabled=enabled, previous=prev)
    if i != len(p):
        raise WireError("trailing bytes in kind 30 reply")
    return out


def build_cns_request(verb: str, **kw) -> bytes:
    code = CNS_CODES[verb]
    if verb == "register":
        start_byte = 0 if kw.get("start") == "now" else 1
        body = bytes([code]) + octets_var(kw["consumer"]) + octets16(b"") + bytes([start_byte])
    elif verb in ("position", "status"):
        body = bytes([code]) + octets_var(kw["consumer"])
    elif verb == "read":
        body = (
            bytes([code])
            + octets16(kw["cursor"])
            + u32be(kw["max_items"], "max-items")
            + u32be(kw["max_octets"], "max-octets")
        )
    elif verb == "wait":
        body = (
            bytes([code])
            + octets16(kw["cursor"])
            + u32be(kw["max_items"], "max-items")
            + u32be(kw["max_octets"], "max-octets")
            + u32be(kw["seconds"], "seconds")
        )
    elif verb == "ack":
        body = bytes([code]) + cursor_propose(kw["cursor"], kw["position"])
    elif verb == "append":
        op_val = kw.get("op", 0)
        op_bytes = be_pos(op_val) if op_val > 0 else b""
        body = bytes([code]) + octets_var(b"") + octets16(op_bytes) + octets32(kw["article"])
    else:
        raise ValueError(f"unknown consumer verb {verb}")
    return fnct_seal(KIND_CNS_REQ, body)


def parse_cns_items(buf: bytes) -> list[dict]:
    items: list[dict] = []
    i = 0
    while i < len(buf):
        header, i = _take(buf, i, 14, "item header")
        t = header[0]
        if t >= len(ITEM_TYPES):
            raise WireError("invalid page item type")
        dom = int.from_bytes(header[1:5], "big")
        pos = int.from_bytes(header[5:13], "big")
        reasons = header[13]
        streams, i = _octets16_at(buf, i, "item streams")
        mid, i = _octets16_at(buf, i, "item Message-ID")
        body, i = _octets32_at(buf, i, "item body")
        entry: dict = {
            "type": ITEM_TYPES[t],
            "domain": dom,
            "position": pos,
            "reasons": reasons,
            "streams": streams.hex(),
            "message_id": mid.decode("latin-1"),
        }
        if entry["type"] == "reference":
            if len(body) != 41:
                raise WireError(f"reference item body length {len(body)} != 41")
            entry["octets"] = int.from_bytes(body[:8], "big")
            entry["content"] = body[9:].hex()
        elif entry["type"] == "record":
            entry["text"] = body.decode("utf-8", errors="replace")
            entry["octets"] = len(body)
        else:
            entry["body_hex"] = body.hex()
        items.append(entry)
    return items


def decode_cns_reply(verb: str, frame: bytes) -> dict:
    kind, p = fnct_open(frame)
    if kind != KIND_CNS_REPLY:
        raise WireError(f"expected kind 28 reply, got kind {kind}")
    cls_raw, i = _take(p, 0, 1, "kind 28 class")
    if cls_raw[0] >= len(CLASSES):
        raise WireError("malformed kind 28 class")
    cls = CLASSES[cls_raw[0]]
    word_raw, i = _octets16_at(p, i, "kind 28 reason")
    word = word_raw.decode("ascii", errors="replace")
    q, i = _octets32_at(p, i, "kind 28 result")
    if i != len(p):
        raise WireError("kind 28 payload length mismatch")
    out: dict = {"outcome": cls, "reason": word or "none"}
    if cls != "accepted":
        if q:
            raise WireError(f"non-accepted {cls} reply carries result bytes")
        return out
    if verb in ("register", "position"):
        out.update(cursor=q.hex(), position=cursor_position(q))
    elif verb == "ack":
        if len(q) != 12:
            raise WireError(f"ack result length {len(q)} != 12")
        out.update(
            domain=int.from_bytes(q[0:4], "big"),
            position=int.from_bytes(q[4:12], "big"),
        )
    elif verb == "status":
        if len(q) != 28:
            raise WireError(f"status result length {len(q)} != 28")
        out.update(
            domain=int.from_bytes(q[0:4], "big"),
            position=int.from_bytes(q[4:12], "big"),
            frontier=int.from_bytes(q[12:20], "big"),
            gap=int.from_bytes(q[20:28], "big"),
        )
    elif verb in ("read", "wait"):
        more_raw, j = _take(q, 0, 1, "page more flag")
        if more_raw[0] not in (0, 1):
            raise WireError("invalid page more boolean")
        nxt, j = _octets16_at(q, j, "page next cursor")
        count_raw, j = _take(q, j, 4, "page item count")
        count = int.from_bytes(count_raw, "big")
        items_raw, j = _octets32_at(q, j, "page items")
        if j != len(q):
            raise WireError("trailing bytes in page result")
        items = parse_cns_items(items_raw)
        if len(items) != count:
            raise WireError(f"item count mismatch: header {count} vs parsed {len(items)}")
        out.update(
            more=bool(more_raw[0]),
            cursor=nxt.hex(),
            next=cursor_position(nxt),
            count=count,
            items=items,
        )
    elif verb == "append":
        mid_raw, j = _octets16_at(q, 0, "append Message-ID")
        dom_raw, j = _take(q, j, 4, "append domain")
        pos_raw, j = _take(q, j, 8, "append position")
        numbers, j = _octets16_at(q, j, "append numbers")
        receipt, j = _octets16_at(q, j, "append receipt")
        evidence_raw, j = _take(q, j, 1, "append evidence")
        if j != len(q):
            raise WireError("trailing bytes in append result")
        if evidence_raw[0] >= len(EVIDENCE_TYPES):
            raise WireError("invalid append evidence")
        out.update(
            message_id=mid_raw.decode("latin-1"),
            domain=int.from_bytes(dom_raw, "big"),
            position=int.from_bytes(pos_raw, "big"),
            numbers=numbers.hex(),
            receipt=receipt.hex(),
            evidence=EVIDENCE_TYPES[evidence_raw[0]],
        )
    else:
        raise WireError(f"unknown consumer reply verb {verb}")
    return out


class ControlSession:
    """Client session over the owner-only FNCT Unix-domain control socket."""

    def __init__(self, path: str, timeout: float = 30.0):
        self.path = path
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.settimeout(timeout)
        self.sock.connect(path)

    def _read_exact(self, n: int) -> bytes:
        buf = bytearray()
        while len(buf) < n:
            chunk = self.sock.recv(n - len(buf))
            if not chunk:
                break
            buf.extend(chunk)
        return bytes(buf)

    def _recv_frame(self, mutating: bool) -> bytes:
        try:
            head = self._read_exact(10)
            if not head:
                if mutating:
                    raise UncertainOutcome("socket closed before reply header")
                raise WireError("socket closed before reply header")
            if len(head) < 10:
                if mutating:
                    raise UncertainOutcome("truncated reply header on disconnect")
                raise WireError("truncated reply header")
            n = int.from_bytes(head[6:10], "big")
            tail = self._read_exact(n + 32)
            if len(tail) < n + 32:
                if mutating:
                    raise UncertainOutcome("truncated reply frame on disconnect")
                raise WireError("truncated reply frame")
            return head + tail
        except (TimeoutError, socket.timeout, ConnectionResetError, BrokenPipeError) as exc:
            if mutating:
                raise UncertainOutcome(f"transport interrupted after request send: {exc}") from exc
            raise

    def auth(self, verb: str, **kw) -> dict:
        mutating = verb in ("principal-create", "grant-set")
        frame = build_auth_request(verb, **kw)
        try:
            self.sock.sendall(frame)
            reply = self._recv_frame(mutating=mutating)
            return decode_auth_reply(verb, reply)
        except WireError as exc:
            if mutating:
                raise UncertainOutcome(f"invalid reply after request send: {exc}") from exc
            raise

    def cns(self, verb: str, **kw) -> dict:
        mutating = verb in ("register", "ack", "append")
        if verb == "wait":
            self.sock.settimeout(float(kw.get("seconds", 30)) + 30.0)
        frame = build_cns_request(verb, **kw)
        try:
            self.sock.sendall(frame)
            reply = self._recv_frame(mutating=mutating)
            return decode_cns_reply(verb, reply)
        except WireError as exc:
            if mutating:
                raise UncertainOutcome(f"invalid reply after request send: {exc}") from exc
            raise

    def bind_as(self, principal: str | None) -> dict | None:
        if not principal:
            return None
        return self.auth("principal-bind", name=principal)

    def close(self) -> None:
        try:
            self.sock.sendall(fnct_seal(KIND_CONTROL, bytes([CMD_STOP])))
        except OSError:
            pass
        try:
            self.sock.close()
        except OSError:
            pass

    def __enter__(self) -> "ControlSession":
        return self

    def __exit__(self, *_) -> None:
        self.close()


# --- Helpers for group metadata, article formatting, and exit rendering ---
def groups_sidecar_for_image(image: Path) -> Path:
    return Path(f"{image}.groups")


def groups_sidecar_for_sock(sock_path: str) -> Path:
    return Path(f"{sock_path}.groups")


def ctl_sock_marker_for_image(image: Path) -> Path:
    return Path(f"{image}.ctl-sock")


def write_groups_sidecar(path: Path, groups: list[str], mode: int = 0o600) -> None:
    tmp = Path(f"{path}.tmp.{os.getpid()}")
    content = "".join(f"{idx}\t{name}\n" for idx, name in enumerate(groups, 1))
    fd = os.open(str(tmp), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, mode)
    try:
        os.write(fd, content.encode("utf-8"))
    finally:
        os.close(fd)
    os.replace(tmp, path)


def read_groups_sidecar(path: Path) -> list[tuple[int, str]]:
    if not path.is_file():
        return []
    rows: list[tuple[int, str]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line:
            continue
        if "\t" in line:
            idx_s, name = line.split("\t", 1)
            rows.append((int(idx_s), name.strip()))
        else:
            rows.append((len(rows) + 1, line))
    return rows


def resolve_stream_id(raw: str | None, sock_path: str) -> tuple[int, dict | None]:
    """Resolve names using the served ACL2 directory."""
    if raw is None:
        raise ValueError("stream name or numeric stream id is required for read/append grants")
    try:
        return int(raw, 10), None
    except ValueError:
        pass
    with ControlSession(sock_path) as sess:
        result = sess.auth("stream-resolve", name=raw)
    if result["outcome"] != "accepted":
        return 0, result
    return result["target"], None


def resolve_principal_on_node(sock_path: str, raw: str) -> tuple[int, int, dict | None]:
    """Ask ACL2 via a read-only principal-bind probe for (principal_id, authority_head)."""
    try:
        pid = int(raw, 10)
        if pid <= 0:
            raise ValueError("principal id must be positive")
        return pid, 0, None
    except ValueError:
        pass
    with ControlSession(sock_path) as probe:
        res = probe.auth("principal-bind", name=raw)
    if res["outcome"] != "accepted":
        return 0, 0, res
    return res["id"], res["authority_head"], None


def save_cursor_file(path: Path, cursor_hex: str) -> None:
    tmp = Path(f"{path}.tmp.{os.getpid()}")
    fd = os.open(str(tmp), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    try:
        os.write(fd, (cursor_hex.strip() + "\n").encode("ascii"))
    finally:
        os.close(fd)
    os.replace(tmp, path)


def load_cursor_bytes(
    sess: ControlSession,
    cursor_hex: str | None,
    cursor_file: Path | None,
    consumer_bytes: bytes,
) -> tuple[bytes, dict | None]:
    if cursor_hex:
        return bytes.fromhex(cursor_hex.strip()), None
    if cursor_file and cursor_file.is_file():
        return bytes.fromhex(cursor_file.read_text(encoding="ascii").strip()), None
    pos_res = sess.cns("position", consumer=consumer_bytes)
    if pos_res["outcome"] != "accepted":
        return b"", pos_res
    return bytes.fromhex(pos_res["cursor"]), None


def read_article_source(
    group: str | None,
    subject: str | None,
    sender: str | None,
    msgid: str | None,
    body: str | None,
    file_path: Path | None,
) -> list[bytes]:
    """Return raw RFC 5536 article lines (without CR LF or dot-stuffing)."""
    if file_path is not None:
        raw_bytes = file_path.read_bytes()
    elif body is not None:
        raw_bytes = body.encode("utf-8")
    elif not sys.stdin.isatty():
        raw_bytes = sys.stdin.buffer.read()
    else:
        raw_bytes = b""

    # If no --group is supplied and input already begins with RFC 5536 headers, preserve raw lines.
    if group is None and (b"\r\n\r\n" in raw_bytes or b"\n\n" in raw_bytes or raw_bytes.startswith((b"From:", b"Newsgroups:", b"Subject:"))):
        text_lines = raw_bytes.replace(b"\r\n", b"\n").split(b"\n")
        if text_lines and text_lines[-1] == b"":
            text_lines.pop()
        return text_lines

    if not group:
        raise ValueError("specify group (or pass a complete RFC 5536 article via --file / stdin)")
    headers = [
        f"From: {sender or 'operator@fn2.invalid'}".encode("utf-8"),
        f"Newsgroups: {group}".encode("utf-8"),
        f"Subject: {subject or '(no subject)'}".encode("utf-8"),
    ]
    if msgid:
        mid = msgid if msgid.startswith("<") else f"<{msgid}>"
        headers.append(f"Message-ID: {mid}".encode("utf-8"))
    body_lines = raw_bytes.replace(b"\r\n", b"\n").split(b"\n") if raw_bytes else [b""]
    if len(body_lines) > 1 and body_lines[-1] == b"":
        body_lines.pop()
    return headers + [b""] + body_lines


def outcome_exit_code(outcome: str) -> int:
    if outcome == "accepted":
        return EXIT_ACCEPTED
    if outcome == "refused":
        return EXIT_REFUSED
    if outcome == "uncertain":
        return EXIT_UNCERTAIN
    return EXIT_ERROR


def emit(data: dict, as_json: bool, summary: str | None = None) -> int:
    if as_json:
        print(json.dumps(data, sort_keys=True))
    elif summary is not None:
        print(summary)
    else:
        parts = [data.get("outcome", "error")]
        for k, v in data.items():
            if k == "outcome" or v is None:
                continue
            parts.append(f"{k}={v}")
        print(" ".join(parts))
    return outcome_exit_code(data.get("outcome", "error"))


# --- Node Lifecycle Commands (init & serve) ---
def normalize_groups(raw_groups: list[str] | None) -> list[str]:
    if not raw_groups:
        return []
    names: list[str] = []
    seen: set[str] = set()
    for entry in raw_groups:
        for part in entry.split(","):
            g = part.strip()
            if not g:
                continue
            if g not in seen:
                seen.add(g)
                names.append(g)
    return names


def prepare_native_crypto(root: Path) -> None:
    """Build atomically; the Lisp process qualifies the library before any I/O."""
    try:
        subprocess.run(
            ["sh", str(root / "host" / "build-blake3.sh"), str(root / "build" / "lib")],
            cwd=root, check=True, timeout=120,
        )
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise OSError("native BLAKE3 build failed; node was not started") from exc


def cmd_init(args: argparse.Namespace, root: Path) -> int:
    image = args.image.resolve()
    if image.exists():
        print("REFUSED image-exists", flush=True)
        return EXIT_ERROR
    if args.size_mb is not None:
        if args.size_mb <= 0:
            print("REFUSED image-size", flush=True)
            return EXIT_ERROR
        size_bytes = str(args.size_mb * 1024 * 1024)
    else:
        size_bytes = str(args.size)

    prepare_native_crypto(root)
    groups = normalize_groups(args.group)
    image.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(
        FN2_IMAGE=str(image),
        FN2_IMAGE_MODE="init",
        FN2_IMAGE_BYTES=size_bytes,
        FN2_OWNER_UID=env.get("FN2_OWNER_UID", str(os.getuid())),
    )
    if groups:
        env["FN2_GROUPS"] = "\n".join(groups)

    with open(root / "tools" / "image-node.lsp", "rb") as script:
        rc = subprocess.call([str(root / "tools" / "acl2")], cwd=root, stdin=script, env=env)
    if rc == 0:
        effective_groups = groups or ["local.test"]
        write_groups_sidecar(groups_sidecar_for_image(image), effective_groups, mode=0o644)
    return rc


def prepare_control_sock(image: Path, raw_sock: str) -> str:
    sock_path = str(Path(raw_sock).resolve())
    Path(sock_path).parent.mkdir(parents=True, exist_ok=True)
    marker = ctl_sock_marker_for_image(image)
    if os.path.lexists(sock_path):
        st = os.lstat(sock_path)
        owned_prior = marker.is_file() and marker.read_text(encoding="utf-8").strip() == sock_path
        if owned_prior and stat.S_ISSOCK(st.st_mode) and st.st_uid == os.getuid():
            probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            try:
                probe.settimeout(1.0)
                probe.connect(sock_path)
                probe.close()
                raise RuntimeError("control-sock-live")
            except ConnectionRefusedError:
                os.unlink(sock_path)
            finally:
                try:
                    probe.close()
                except OSError:
                    pass
    return sock_path


def cmd_serve(args: argparse.Namespace, root: Path) -> int:
    image = args.image.resolve()
    if not image.is_file():
        print("REFUSED image-missing", flush=True)
        return EXIT_ERROR

    prepare_native_crypto(root)
    groups = normalize_groups(args.group)
    if not groups:
        sidecar_rows = read_groups_sidecar(groups_sidecar_for_image(image))
        groups = [name for _, name in sidecar_rows]

    env = os.environ.copy()
    env.update(
        FN2_IMAGE=str(image),
        FN2_IMAGE_MODE="serve",
        FN2_LISTENER_PORT=str(args.port),
        FN2_OWNER_UID=env.get("FN2_OWNER_UID", str(os.getuid())),
    )
    if args.host:
        env["FN2_LISTENER_ADDRESS"] = args.host
    if groups:
        env["FN2_GROUPS"] = "\n".join(groups)
    for option, variable in ((args.tls_certificate, "FN2_TLS_CERTIFICATE"),
                             (args.tls_key, "FN2_TLS_KEY"),
                             (args.tls_handshakes, "FN2_TLS_HANDSHAKES"),
                             (args.tls_handshake_ms, "FN2_TLS_HANDSHAKE_MS")):
        if option is not None:
            env[variable] = str(option)
    if "FN2_TLS_CERTIFICATE" in env or "FN2_TLS_KEY" in env:
        try:
            subprocess.run(["sh", str(root / "host" / "build-tls.sh"), str(root / "build" / "lib")],
                           cwd=root, check=True, timeout=120)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
            raise OSError("native TLS build failed; node was not started") from exc
    if args.peering:
        env["FN2_PEERING"] = "1"

    if args.control_sock:
        try:
            sock_str = prepare_control_sock(image, args.control_sock)
        except RuntimeError as exc:
            print(f"REFUSED {exc}", flush=True)
            return EXIT_ERROR
        env["FN2_LISTENER_PATH"] = sock_str
        ctl_sock_marker_for_image(image).write_text(sock_str + "\n", encoding="utf-8")
        write_groups_sidecar(groups_sidecar_for_sock(sock_str), groups or ["local.test"], mode=0o600)

    os.chdir(root)
    with open(root / "tools" / "image-node.lsp", "rb") as script:
        os.dup2(script.fileno(), 0)
    os.execve(str(root / "tools" / "acl2"), [str(root / "tools" / "acl2")], env)


# --- Authority Subcommands ---
def require_control_sock(args: argparse.Namespace) -> str:
    sock = getattr(args, "control_sock", None) or os.environ.get("FN_CONTROL_SOCK")
    if not sock:
        raise ValueError("specify --control-sock PATH or set FN_CONTROL_SOCK")
    return str(Path(sock).resolve())


def cmd_principal_create(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    with ControlSession(sock_path) as sess:
        bind_res = sess.bind_as(args.as_principal)
        if bind_res and bind_res["outcome"] != "accepted":
            return emit(bind_res, args.json)
        res = sess.auth("principal-create", name=args.name)
    res["principal"] = args.name
    return emit(res, args.json)


def cmd_grant_set(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    right = AUTH_RIGHTS[args.right]
    if args.right == "consume":
        if args.stream not in (None, "0"):
            raise ValueError("consume right applies to own-consumers scope; omit [stream]")
        scope, target = 0, 0
    else:
        scope = 1
        target, err = resolve_stream_id(args.stream, sock_path)
        if err is not None:
            return emit(err, args.json)

    pid, head, err = resolve_principal_on_node(sock_path, args.principal)
    if err is not None:
        return emit(err, args.json)
    expected_head = args.expected_head if args.expected_head is not None else head
    op_id = parse_u60_op(args.op, required=True)
    enabled = not args.revoke

    try:
        with ControlSession(sock_path) as sess:
            bind_res = sess.bind_as(args.as_principal)
            if bind_res and bind_res["outcome"] != "accepted":
                return emit(bind_res, args.json)
            res = sess.auth(
                "grant-set",
                grantee=pid,
                right=right,
                scope=scope,
                target=target,
                enabled=enabled,
                expected_head=expected_head,
                op=op_id,
            )
    except UncertainOutcome as unc:
        return emit({"outcome": "uncertain", "reason": str(unc), "op": op_id}, args.json)

    res.update(principal=args.principal, principal_id=pid, right=args.right, target=target, enabled=enabled, op=op_id)
    return emit(res, args.json)


def cmd_grant_get(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    right = AUTH_RIGHTS[args.right]
    if args.right == "consume":
        if args.stream not in (None, "0"):
            raise ValueError("consume right applies to own-consumers scope; omit [stream]")
        scope, target = 0, 0
    else:
        scope = 1
        target, err = resolve_stream_id(args.stream, sock_path)
        if err is not None:
            return emit(err, args.json)

    pid, _, err = resolve_principal_on_node(sock_path, args.principal)
    if err is not None:
        return emit(err, args.json)

    with ControlSession(sock_path) as sess:
        bind_res = sess.bind_as(args.as_principal)
        if bind_res and bind_res["outcome"] != "accepted":
            return emit(bind_res, args.json)
        res = sess.auth("grant-get", grantee=pid, right=right, scope=scope, target=target)
    res.update(principal=args.principal, principal_id=pid, right=args.right, target=target)
    return emit(res, args.json)


# --- Stream / Consumer Subcommands ---
def cmd_stream_register(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    cbytes = encode_consumer_id(args.consumer)
    with ControlSession(sock_path) as sess:
        bind_res = sess.bind_as(args.as_principal)
        if bind_res and bind_res["outcome"] != "accepted":
            return emit(bind_res, args.json)
        res = sess.cns("register", consumer=cbytes, start=args.start)
    if res["outcome"] == "accepted" and args.cursor_file:
        save_cursor_file(args.cursor_file, res["cursor"])
    return emit(res, args.json)


def cmd_stream_append(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    lines = read_article_source(args.group, args.subject, args.sender, args.msgid, args.body, args.file)
    article_bytes = b"".join(line + b"\r\n" for line in lines)
    op_id = parse_u60_op(args.op, required=False)
    try:
        with ControlSession(sock_path) as sess:
            bind_res = sess.bind_as(args.as_principal)
            if bind_res and bind_res["outcome"] != "accepted":
                return emit(bind_res, args.json)
            res = sess.cns("append", op=op_id, article=article_bytes)
    except UncertainOutcome as unc:
        return emit({"outcome": "uncertain", "reason": str(unc), "op": op_id}, args.json)
    if op_id:
        res["op"] = op_id
    return emit(res, args.json)


def _render_page_human(res: dict) -> str:
    if res["outcome"] != "accepted":
        return f"{res['outcome']} reason={res.get('reason', 'none')}"
    lines = [
        f"accepted count={res['count']} next={res['next']} more={str(res['more']).lower()} cursor={res['cursor']}"
    ]
    for item in res["items"]:
        extra = ""
        if item["type"] == "reference":
            extra = f" octets={item['octets']} content={item['content']}"
        elif item["type"] == "record":
            extra = f" octets={item['octets']}"
        lines.append(
            f"item position={item['position']} type={item['type']} message_id={item['message_id']}{extra}"
        )
    return "\n".join(lines)


def cmd_stream_read(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    cbytes = encode_consumer_id(args.consumer)
    with ControlSession(sock_path) as sess:
        bind_res = sess.bind_as(args.as_principal)
        if bind_res and bind_res["outcome"] != "accepted":
            return emit(bind_res, args.json)
        cur, err = load_cursor_bytes(sess, args.cursor, args.cursor_file, cbytes)
        if err is not None:
            return emit(err, args.json)
        res = sess.cns("read", cursor=cur, max_items=args.max_items, max_octets=args.max_octets)
    return emit(res, args.json, summary=None if args.json else _render_page_human(res))


def cmd_stream_wait(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    cbytes = encode_consumer_id(args.consumer)
    with ControlSession(sock_path) as sess:
        bind_res = sess.bind_as(args.as_principal)
        if bind_res and bind_res["outcome"] != "accepted":
            return emit(bind_res, args.json)
        cur, err = load_cursor_bytes(sess, args.cursor, args.cursor_file, cbytes)
        if err is not None:
            return emit(err, args.json)
        res = sess.cns(
            "wait",
            cursor=cur,
            max_items=args.max_items,
            max_octets=args.max_octets,
            seconds=args.seconds,
        )
    return emit(res, args.json, summary=None if args.json else _render_page_human(res))


def cmd_stream_ack(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    cbytes = encode_consumer_id(args.consumer)
    with ControlSession(sock_path) as sess:
        bind_res = sess.bind_as(args.as_principal)
        if bind_res and bind_res["outcome"] != "accepted":
            return emit(bind_res, args.json)
        cur, err = load_cursor_bytes(sess, args.cursor, args.cursor_file, cbytes)
        if err is not None:
            return emit(err, args.json)
        res = sess.cns("ack", cursor=cur, position=args.position)
        if res["outcome"] == "accepted" and args.cursor_file:
            try:
                pos_res = sess.cns("position", consumer=cbytes)
            except (WireError, OSError) as exc:
                # The accepted durable ack is already known; only its optional
                # cursor-file refresh failed.
                res["cursor_refresh_error"] = str(exc)
            else:
                if pos_res["outcome"] == "accepted":
                    save_cursor_file(args.cursor_file, pos_res["cursor"])
                    res["cursor"] = pos_res["cursor"]
                else:
                    res["cursor_refresh_error"] = pos_res.get("reason", pos_res["outcome"])
    return emit(res, args.json)


def cmd_stream_status(args: argparse.Namespace) -> int:
    sock_path = require_control_sock(args)
    cbytes = encode_consumer_id(args.consumer)
    with ControlSession(sock_path) as sess:
        bind_res = sess.bind_as(args.as_principal)
        if bind_res and bind_res["outcome"] != "accepted":
            return emit(bind_res, args.json)
        res = sess.cns("status", consumer=cbytes)
    return emit(res, args.json)


# --- NNTP Reader / Poster Subcommands ---
def nntp_endpoint(args: argparse.Namespace) -> tuple[str, int]:
    host = args.host or os.environ.get("FN_HOST") or "127.0.0.1"
    raw_port = args.port if args.port is not None else os.environ.get("FN_PORT")
    if not raw_port:
        raise ValueError("specify --port PORT or set FN_PORT")
    port = int(raw_port)
    if not (1 <= port <= 65535):
        raise ValueError("NNTP port must be in 1 .. 65535")
    return host, port


def nntp_connect(host: str, port: int) -> tuple[socket.socket, object, str]:
    sock = socket.create_connection((host, port), timeout=30.0)
    reader = sock.makefile("rb")
    banner = reader.readline()
    if not banner or not banner.startswith((b"200 ", b"201 ")):
        reader.close()
        sock.close()
        raise WireError(f"unexpected NNTP greeting: {banner!r}")
    return sock, reader, banner.decode("latin-1").rstrip("\r\n")


def nntp_read_multiline(reader) -> list[bytes]:
    out: list[bytes] = []
    while True:
        line = reader.readline()
        if not line:
            raise WireError("EOF inside NNTP multiline response")
        if line == b".\r\n":
            return out
        raw = line[:-2] if line.endswith(b"\r\n") else line.rstrip(b"\n")
        if raw.startswith(b".."):
            raw = raw[1:]
        out.append(raw)


def nntp_quit(sock: socket.socket, reader) -> None:
    try:
        sock.sendall(b"QUIT\r\n")
        reader.readline()
    except OSError:
        pass
    finally:
        try:
            reader.close()
        except OSError:
            pass
        try:
            sock.close()
        except OSError:
            pass


def cmd_groups(args: argparse.Namespace) -> int:
    host, port = nntp_endpoint(args)
    sock, reader, _ = nntp_connect(host, port)
    try:
        sock.sendall(b"LIST ACTIVE\r\n")
        status = reader.readline().decode("latin-1").rstrip("\r\n")
        if not status.startswith("215 "):
            return emit({"outcome": "refused", "status": status}, args.json)
        raw_lines = nntp_read_multiline(reader)
        groups = []
        for raw in raw_lines:
            parts = raw.decode("latin-1").split()
            if len(parts) >= 4:
                groups.append(
                    {"name": parts[0], "high": int(parts[1]), "low": int(parts[2]), "status": parts[3]}
                )
            elif parts:
                groups.append({"name": parts[0], "raw": raw.decode("latin-1")})
        if args.json:
            return emit({"outcome": "accepted", "groups": groups}, True)
        for g in groups:
            if "high" in g:
                print(f"{g['name']} {g['high']} {g['low']} {g['status']}")
            else:
                print(g["raw"])
        return EXIT_ACCEPTED
    finally:
        nntp_quit(sock, reader)


def cmd_post(args: argparse.Namespace) -> int:
    host, port = nntp_endpoint(args)
    lines = read_article_source(args.group, args.subject, args.sender, args.msgid, args.body, args.file)
    stuffed = [(b"." + ln if ln.startswith(b".") else ln) for ln in lines] + [b"."]
    wire_body = b"".join(ln + b"\r\n" for ln in stuffed)

    sock, reader, _ = nntp_connect(host, port)
    sent_body = False
    try:
        sock.sendall(b"POST\r\n")
        stage = reader.readline()
        if not stage:
            return emit({"outcome": "refused", "reason": "eof-before-340"}, args.json)
        stage_s = stage.decode("latin-1").rstrip("\r\n")
        if not stage_s.startswith("340 "):
            outcome = "uncertain" if stage_s.startswith("403 ") else "refused"
            return emit({"outcome": outcome, "status": stage_s}, args.json)
        sent_body = True
        sock.sendall(wire_body)
        reply = reader.readline()
        if not reply:
            return emit({"outcome": "uncertain", "reason": "eof-after-post-send"}, args.json)
        reply_s = reply.decode("latin-1").rstrip("\r\n")
        if reply_s.startswith("240 "):
            return emit({"outcome": "accepted", "status": reply_s}, args.json)
        if reply_s.startswith("403 ") or reply_s.startswith("441 ") and "outcome is uncertain" in reply_s:
            return emit({"outcome": "uncertain", "status": reply_s}, args.json)
        return emit({"outcome": "refused", "status": reply_s}, args.json)
    except (TimeoutError, socket.timeout, ConnectionResetError, BrokenPipeError) as exc:
        if sent_body:
            return emit({"outcome": "uncertain", "reason": str(exc)}, args.json)
        raise
    finally:
        nntp_quit(sock, reader)


def cmd_article(args: argparse.Namespace) -> int:
    host, port = nntp_endpoint(args)
    if len(args.selector) == 1:
        group, target = None, args.selector[0]
    elif len(args.selector) == 2:
        group, target = args.selector[0], args.selector[1]
    else:
        raise ValueError("usage: fn article [group] <num|msgid>")

    if group is None and not target.startswith("<"):
        raise ValueError("specify <group> when selecting an article by number")

    verb = "HEAD" if args.head else "ARTICLE"
    sock, reader, _ = nntp_connect(host, port)
    try:
        if group is not None:
            sock.sendall(f"GROUP {group}\r\n".encode("utf-8"))
            g_status = reader.readline().decode("latin-1").rstrip("\r\n")
            if not g_status.startswith("211 "):
                return emit({"outcome": "refused", "status": g_status}, args.json)
        sock.sendall(f"{verb} {target}\r\n".encode("utf-8"))
        status = reader.readline().decode("latin-1").rstrip("\r\n")
        if not status.startswith(("220 ", "221 ")):
            return emit({"outcome": "refused", "status": status}, args.json)
        lines = nntp_read_multiline(reader)
        text = "\n".join(ln.decode("utf-8", errors="replace") for ln in lines)
        parts = status.split(" ", 3)
        mid = parts[2] if len(parts) >= 3 else ""
        num = int(parts[1]) if len(parts) >= 2 and parts[1].isdigit() else 0
        if args.json:
            return emit(
                {
                    "outcome": "accepted",
                    "status": status,
                    "number": num,
                    "message_id": mid,
                    "text": text,
                },
                True,
            )
        sys.stdout.write(text + ("\n" if text else ""))
        return EXIT_ACCEPTED
    finally:
        nntp_quit(sock, reader)


# --- CLI Parser ---
def _add_control_args(p: argparse.ArgumentParser, allow_as: bool = True) -> None:
    p.add_argument("--control-sock", help="path to FNCT Unix control socket (default: $FN_CONTROL_SOCK)")
    if allow_as:
        p.add_argument("--as", dest="as_principal", help="bind connection to principal name before request")
    p.add_argument("--json", action="store_true", help="emit machine-readable JSON")


def _add_nntp_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--port", type=int, help="NNTP TCP port (default: $FN_PORT)")
    p.add_argument("--host", help="NNTP host address (default: $FN_HOST or 127.0.0.1)")
    p.add_argument("--json", action="store_true", help="emit machine-readable JSON")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="fn",
        description="Certified fn2 node & client CLI (ACL2-decided store, authority, consumer streams, and NNTP).",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_init = sub.add_parser("init", help="exclusively initialize a fresh preallocated store image")
    p_init.add_argument("image", type=Path)
    sz = p_init.add_mutually_exclusive_group()
    sz.add_argument("--size-mb", type=int, help="image size in MiB (default: 32)")
    sz.add_argument("--size", type=int, default=33554432, help="exact image size in bytes (multiple of 4096)")
    p_init.add_argument("--group", action="append", help="genesis newsgroup/stream name (repeatable; default: local.test)")

    p_serve = sub.add_parser("serve", help="recover image, fence epoch, and serve TCP NNTP + local FNCT socket")
    p_serve.add_argument("image", type=Path)
    p_serve.add_argument("--port", default="0", help="TCP NNTP listener port (0 for ephemeral)")
    p_serve.add_argument("--host", help="TCP listener IPv4 address (default: 127.0.0.1)")
    p_serve.add_argument("--control-sock", help="owner-only (0600) FNCT Unix control/consumer/authority socket")
    p_serve.add_argument("--peering", action="store_true", help="enable interim NNTP transit peering verbs")
    p_serve.add_argument("--tls-certificate", type=lambda p: Path(p).resolve(), help="PEM certificate chain for STARTTLS")
    p_serve.add_argument("--tls-key", type=lambda p: Path(p).resolve(), help="PEM private key for STARTTLS")
    p_serve.add_argument("--tls-handshakes", help="maximum concurrent STARTTLS handshakes (default: 16)")
    p_serve.add_argument("--tls-handshake-ms", help="STARTTLS admission/handshake deadline in milliseconds (default: 10000)")
    p_serve.add_argument("--group", action="append", help="expected genesis group list (default: loaded from <image>.groups)")

    p_princ = sub.add_parser("principal", help="manage durable principals over --control-sock")
    princ_sub = p_princ.add_subparsers(dest="principal_cmd", required=True)
    p_pcreate = princ_sub.add_parser("create", help="create a durable principal")
    p_pcreate.add_argument("name", help="principal name (1..64 UTF-8 octets)")
    _add_control_args(p_pcreate)

    p_grant = sub.add_parser("grant", help="manage durable authority grants over --control-sock")
    grant_sub = p_grant.add_subparsers(dest="grant_cmd", required=True)

    p_gset = grant_sub.add_parser("set", help="grant or revoke consume/read/append authority")
    p_gset.add_argument("principal", help="grantee principal name or numeric principal id")
    p_gset.add_argument("right", choices=("consume", "read", "append"))
    p_gset.add_argument("stream", nargs="?", help="stream/group name or numeric stream id (omit for consume)")
    p_gset.add_argument("--revoke", action="store_true", help="disable (revoke) the grant")
    p_gset.add_argument("--expected-head", type=int, help="explicit expected authority head for CAS")
    p_gset.add_argument("--op", help="idempotent operation id (1..2^60-1; auto-generated if omitted)")
    _add_control_args(p_gset)

    p_gget = grant_sub.add_parser("get", help="inspect current grant state for a principal")
    p_gget.add_argument("principal", help="grantee principal name or numeric principal id")
    p_gget.add_argument("right", choices=("consume", "read", "append"))
    p_gget.add_argument("stream", nargs="?", help="stream/group name or numeric stream id (omit for consume)")
    _add_control_args(p_gget)

    p_stream = sub.add_parser("stream", help="consumer & stream operations over --control-sock")
    stream_sub = p_stream.add_subparsers(dest="stream_cmd", required=True)

    p_sreg = stream_sub.add_parser("register", help="register durable inbox cursor")
    p_sreg.add_argument("--consumer", default="1", help="consumer id (positive int or 1..7 byte name; default: 1)")
    p_sreg.add_argument("--start", choices=("history", "now"), default="history")
    p_sreg.add_argument("--cursor-file", type=Path, help="save issued cursor hex to file")
    _add_control_args(p_sreg)

    p_sapp = stream_sub.add_parser("append", help="append an article over the local FNCT carrier")
    p_sapp.add_argument("--group", help="target newsgroup(s) for Newsgroups header")
    p_sapp.add_argument("--subject", help="Subject header")
    p_sapp.add_argument("--from", dest="sender", help="From header")
    p_sapp.add_argument("--msgid", help="Message-ID header (optional; node generates one if omitted)")
    p_sapp.add_argument("--body", help="article body text")
    p_sapp.add_argument("--file", type=Path, help="read article body or full RFC 5536 article from file")
    p_sapp.add_argument("--op", help="idempotent operation id (1..2^60-1)")
    _add_control_args(p_sapp)

    p_sread = stream_sub.add_parser("read", help="read a bounded page from a consumer cursor")
    p_sread.add_argument("--cursor", help="issued fncu cursor hex")
    p_sread.add_argument("--cursor-file", type=Path, help="file containing fncu cursor hex")
    p_sread.add_argument("--consumer", default="1", help="consumer id when querying committed position")
    p_sread.add_argument("--max-items", type=int, default=16)
    p_sread.add_argument("--max-octets", type=int, default=65536)
    _add_control_args(p_sread)

    p_swait = stream_sub.add_parser("wait", help="park until items arrive past cursor or timeout elapses")
    p_swait.add_argument("--cursor", help="issued fncu cursor hex")
    p_swait.add_argument("--cursor-file", type=Path, help="file containing fncu cursor hex")
    p_swait.add_argument("--consumer", default="1", help="consumer id when querying committed position")
    p_swait.add_argument("--max-items", type=int, default=16)
    p_swait.add_argument("--max-octets", type=int, default=65536)
    p_swait.add_argument("--seconds", type=int, default=30, help="maximum wait seconds (0..3600)")
    _add_control_args(p_swait)

    p_sack = stream_sub.add_parser("ack", help="durably advance committed consumer cursor")
    p_sack.add_argument("position", type=int, help="commit position reported by read/wait")
    p_sack.add_argument("--cursor", help="issued fncu cursor hex")
    p_sack.add_argument("--cursor-file", type=Path, help="file containing fncu cursor hex (updated on acceptance)")
    p_sack.add_argument("--consumer", default="1", help="consumer id when querying committed position")
    _add_control_args(p_sack)

    p_sstat = stream_sub.add_parser("status", help="inspect consumer committed position, frontier, and gap")
    p_sstat.add_argument("--consumer", default="1", help="consumer id (default: 1)")
    _add_control_args(p_sstat)

    p_groups = sub.add_parser("groups", help="list active newsgroups over NNTP")
    _add_nntp_args(p_groups)

    p_post = sub.add_parser("post", help="post an article over NNTP")
    p_post.add_argument("group", nargs="?", help="target newsgroup (optional if --file/stdin is full RFC 5536 article)")
    p_post.add_argument("--subject", help="Subject header")
    p_post.add_argument("--from", dest="sender", help="From header")
    p_post.add_argument("--msgid", help="Message-ID header")
    p_post.add_argument("--body", help="article body text")
    p_post.add_argument("--file", type=Path, help="read article body or full RFC 5536 article from file")
    _add_nntp_args(p_post)

    p_art = sub.add_parser("article", help="fetch an article by group+number or Message-ID over NNTP")
    p_art.add_argument("selector", nargs="+", help="[group] <num|msgid>")
    p_art.add_argument("--head", action="store_true", help="fetch headers only (HEAD)")
    _add_nntp_args(p_art)

    return parser


def main(argv: list[str] | None = None, root: Path | None = None) -> int:
    repo_root = root or Path(__file__).resolve().parents[1]
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.command == "init":
            return cmd_init(args, repo_root)
        if args.command == "serve":
            return cmd_serve(args, repo_root)
        if args.command == "principal" and args.principal_cmd == "create":
            return cmd_principal_create(args)
        if args.command == "grant" and args.grant_cmd == "set":
            return cmd_grant_set(args)
        if args.command == "grant" and args.grant_cmd == "get":
            return cmd_grant_get(args)
        if args.command == "stream":
            dispatch = {
                "register": cmd_stream_register,
                "append": cmd_stream_append,
                "read": cmd_stream_read,
                "wait": cmd_stream_wait,
                "ack": cmd_stream_ack,
                "status": cmd_stream_status,
            }
            return dispatch[args.stream_cmd](args)
        if args.command == "groups":
            return cmd_groups(args)
        if args.command == "post":
            return cmd_post(args)
        if args.command == "article":
            return cmd_article(args)
        parser.error(f"unknown command {args.command}")
        return EXIT_ERROR
    except UncertainOutcome as exc:
        data = dict(exc.detail)
        data.update(outcome="uncertain", reason=str(exc))
        return emit(data, getattr(args, "json", False))
    except (ValueError, WireError, OSError) as exc:
        if getattr(args, "json", False):
            print(json.dumps({"outcome": "error", "error": str(exc)}, sort_keys=True))
        else:
            sys.stderr.write(f"fn: {exc}\n")
        return EXIT_ERROR


if __name__ == "__main__":
    sys.exit(main())
