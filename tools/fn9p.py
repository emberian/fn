#!/usr/bin/env python3
"""Experimental read-only 9P2000 view of one committed fn store snapshot.

The server is glue.  It replays the committed store into ACL2 exactly as
tools/run_reader.py does -- shared store lock, Acl2Store bridge,
Store.recover, then host/reader-host.lisp's archive selection -- and every
byte it ever serves is read out of that ACL2 session through
host/ninep-host.lisp, which calls the books/nntp.lisp projection functions.
No news semantics are decided here: this file addresses, frames and copies.

The whole projection is materialized while the shared lock is held, and the
lock, the bridge and the ACL2 process are released once every served byte is
in hand.  A mount therefore shows one fixed generation for its whole life: a
later commit is invisible to it, and a fresh mount is how a reader sees a
newer generation.  specs/views-9p.md states the contract.
"""
import os
import signal
import socket
import struct
import sys
import threading

from run_store import (Acl2Store, EXIT_FAULT, EXIT_OK, Store, StoreError,
                       UsageParser, acl2_boolean, acl2_octets)
from run_reader import Acl2Reader

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Materialization is bounded before it starts: a snapshot larger than this is
# refused rather than served from a host that has already committed to holding
# it.  The bound covers the octets of every file in the view.
DEFAULT_MAX_SNAPSHOT_BYTES = 64 * 1024 * 1024

# 9P2000 (Plan 9 manual section 5).  Only the read-only subset is implemented.
TVERSION, RVERSION = 100, 101
TAUTH, RAUTH = 102, 103
TATTACH, RATTACH = 104, 105
RERROR = 107
TFLUSH, RFLUSH = 108, 109
TWALK, RWALK = 110, 111
TOPEN, ROPEN = 112, 113
TCREATE = 114
TREAD, RREAD = 116, 117
TWRITE = 118
TCLUNK, RCLUNK = 120, 121
TREMOVE = 122
TSTAT, RSTAT = 124, 125
TWSTAT = 126

VERSION = b"9P2000"
NOFID = 0xFFFFFFFF
NOTAG = 0xFFFF
QTDIR = 0x80
QTFILE = 0x00
DMDIR = 0x80000000
OREAD, OWRITE, ORDWR, OEXEC = 0, 1, 2, 3
OTRUNC, ORCLOSE = 0x10, 0x40
MAX_MSIZE = 128 * 1024
MIN_MSIZE = 1024
MAX_WELEM = 16
IOHDRSZ = 24


class ProtocolError(Exception):
    """A malformed or unsupported client message; the connection ends."""


class NineError(Exception):
    """A request refused with Rerror; the connection continues.

    Base 9P2000 carries a reason string, and the Linux client maps it through
    its own table: a string that is not in the table becomes ESERVERFAULT, so
    an ordinary miss reads as "Unknown error 526" at the shell.  Conditions a
    file system already has a name for use that name; the projection's own
    refusals keep the reason NNTP would give.
    """


class Node:
    """One file or directory of the frozen snapshot."""

    def __init__(self, name, path, is_dir, data=None, refusal=None):
        self.name = name
        self.path = path
        self.is_dir = is_dir
        self.data = data
        # A committed article whose stored bytes the projection refuses to
        # frame degrades only itself, exactly as ARTICLE's 503 does.
        self.refusal = refusal
        self.children = []
        self.parent = self
        self.directory_bytes = b""
        self.offsets = {0}

    def add(self, child):
        child.parent = self
        self.children.append(child)

    def freeze(self):
        """Precompute directory contents and their legal read offsets."""
        if self.is_dir:
            blob = b""
            for child in self.children:
                child.freeze()
                blob += stat_bytes(child)
                self.offsets.add(len(blob))
            self.directory_bytes = blob

    @property
    def qtype(self):
        return QTDIR if self.is_dir else QTFILE

    @property
    def length(self):
        if self.is_dir:
            return len(self.directory_bytes)
        return len(self.data or b"")

    def lookup(self, name):
        if name == b"..":
            return self.parent
        if name == b".":
            return self
        for child in self.children:
            if child.name == name:
                return child
        return None


def encode_string(value):
    if len(value) > 0xFFFF:
        raise ProtocolError("string too long")
    return struct.pack("<H", len(value)) + value


def qid_bytes(node):
    return struct.pack("<BIQ", node.qtype, 0, node.path)


def stat_bytes(node):
    mode = (DMDIR | 0o555) if node.is_dir else 0o444
    body = struct.pack("<HI", 0, 0) + qid_bytes(node)
    body += struct.pack("<IIIQ", mode, 0, 0, node.length)
    body += encode_string(node.name)
    for owner in (b"fn", b"fn", b"fn"):
        body += encode_string(owner)
    return struct.pack("<H", len(body)) + body


class Message:
    """A bounds-checked reader over one received 9P message body."""

    def __init__(self, body):
        self.body = body
        self.at = 0

    def take(self, count):
        if self.at + count > len(self.body):
            raise ProtocolError("truncated 9P message")
        chunk = self.body[self.at:self.at + count]
        self.at += count
        return chunk

    def u1(self):
        return self.take(1)[0]

    def u2(self):
        return struct.unpack("<H", self.take(2))[0]

    def u4(self):
        return struct.unpack("<I", self.take(4))[0]

    def u8(self):
        return struct.unpack("<Q", self.take(8))[0]

    def string(self):
        return self.take(self.u2())


def lines(blob):
    """Split one LF-joined listing ACL2 built.  Empty means no entries."""
    if not blob:
        return []
    return blob.split(b"\n")[:-1] if blob.endswith(b"\n") else blob.split(b"\n")


class Projection:
    """Reads the committed snapshot out of the ACL2 session, once."""

    def __init__(self, reader, budget):
        self.reader = reader
        self.budget = budget
        self.reader.call(
            '(ld "host/ninep-host.lisp" :ld-error-action :return :ld-error-triples t)')

    def call(self, form):
        found = acl2_boolean(self.reader.call(form))
        octets = acl2_octets(self.reader.call("(@ fn9p-output)"))
        self.budget -= len(octets)
        if self.budget < 0:
            raise StoreError("committed snapshot exceeds the 9P view bound")
        return found, octets


def build_snapshot(projection):
    """Materialize the whole view.  Every byte here came from ACL2."""
    counter = iter(range(1, 1 << 62))
    def node(name, is_dir, data=None, refusal=None):
        return Node(name, next(counter), is_dir, data, refusal)

    root = node(b"/", True)
    _, status = projection.call("(fn9p-status state)")
    root.add(node(b"status", False, status))

    groups = node(b"groups", True)
    root.add(groups)
    _, listing = projection.call("(fn9p-groups state)")
    for group_index, name in enumerate(lines(listing)):
        group = node(name, True)
        groups.add(group)
        _, numbers = projection.call("(fn9p-numbers {} state)".format(group_index))
        for number_index, number in enumerate(lines(numbers)):
            found, payload = projection.call(
                "(fn9p-article {} {} state)".format(group_index, number_index))
            group.add(node(number, False, payload if found else None,
                           None if found else "stored article framing unavailable"))

    by_id = node(b"by-id", True)
    root.add(by_id)
    _, identifiers = projection.call("(fn9p-ids state)")
    for index, name in enumerate(lines(identifiers)):
        found, payload = projection.call("(fn9p-id-article {} state)".format(index))
        by_id.add(node(name, False, payload if found else None,
                       None if found else "stored article framing unavailable"))

    root.freeze()
    return root


class Connection:
    """One client session over the frozen snapshot."""

    def __init__(self, sock, root):
        self.sock = sock
        self.root = root
        self.msize = MAX_MSIZE
        self.fids = {}
        self.open_fids = set()

    def receive(self):
        header = self.recv_exact(4)
        if header is None:
            return None
        size = struct.unpack("<I", header)[0]
        if size < 7 or size > self.msize:
            raise ProtocolError("message size outside the negotiated bound")
        rest = self.recv_exact(size - 4)
        if rest is None:
            raise ProtocolError("truncated 9P message")
        return rest[0], struct.unpack("<H", rest[1:3])[0], Message(rest[3:])

    def recv_exact(self, count):
        data = b""
        while len(data) < count:
            chunk = self.sock.recv(count - len(data))
            if not chunk:
                return None
            data += chunk
        return data

    def reply(self, kind, tag, body):
        message = struct.pack("<IBH", 7 + len(body), kind, tag) + body
        self.sock.sendall(message)

    def error(self, tag, text):
        self.reply(RERROR, tag, encode_string(text.encode("utf-8", "replace")))

    def fid(self, number):
        if number not in self.fids:
            raise NineError("unknown fid")
        return self.fids[number]

    def serve(self):
        while True:
            request = self.receive()
            if request is None:
                return
            kind, tag, message = request
            try:
                self.dispatch(kind, tag, message)
            except NineError as refusal:
                self.error(tag, str(refusal))

    def dispatch(self, kind, tag, message):
        if kind == TVERSION:
            requested = message.u4()
            version = message.string()
            self.msize = max(MIN_MSIZE, min(MAX_MSIZE, requested))
            # An unknown dialect is answered with the base protocol; 9P2000.u
            # and 9P2000.L clients then fall back to it.
            self.reply(RVERSION, tag,
                       struct.pack("<I", self.msize) + encode_string(
                           VERSION if version.startswith(VERSION) else b"unknown"))
            self.fids.clear()
            self.open_fids.clear()
        elif kind == TAUTH:
            raise NineError("9P authentication is not required")
        elif kind == TATTACH:
            fid = message.u4()
            message.u4()
            message.string()
            message.string()
            if fid == NOFID or fid in self.fids:
                raise NineError("fid in use")
            self.fids[fid] = self.root
            self.reply(RATTACH, tag, qid_bytes(self.root))
        elif kind == TFLUSH:
            message.u2()
            self.reply(RFLUSH, tag, b"")
        elif kind == TWALK:
            self.walk(tag, message)
        elif kind == TOPEN:
            fid = message.u4()
            mode = message.u1()
            node = self.fid(fid)
            if mode & 3 not in (OREAD, OEXEC) or mode & (OTRUNC | ORCLOSE):
                raise NineError("Read-only file system")
            if node.refusal is not None:
                raise NineError(node.refusal)
            self.open_fids.add(fid)
            self.reply(ROPEN, tag, qid_bytes(node) + struct.pack("<I", 0))
        elif kind == TREAD:
            self.read(tag, message)
        elif kind == TCLUNK:
            fid = message.u4()
            self.fid(fid)
            del self.fids[fid]
            self.open_fids.discard(fid)
            self.reply(RCLUNK, tag, b"")
        elif kind == TSTAT:
            node = self.fid(message.u4())
            entry = stat_bytes(node)
            self.reply(RSTAT, tag, struct.pack("<H", len(entry)) + entry)
        elif kind in (TCREATE, TWRITE, TREMOVE, TWSTAT):
            raise NineError("Read-only file system")
        else:
            raise ProtocolError("unsupported 9P message type")

    def walk(self, tag, message):
        fid = message.u4()
        newfid = message.u4()
        count = message.u2()
        if count > MAX_WELEM:
            raise NineError("walk is longer than the protocol allows")
        names = [message.string() for _ in range(count)]
        node = self.fid(fid)
        if fid in self.open_fids:
            raise NineError("cannot walk an open fid")
        if newfid != fid and newfid in self.fids:
            raise NineError("fid in use")
        qids = b""
        walked = 0
        for name in names:
            child = node.lookup(name)
            if child is None:
                break
            node = child
            qids += qid_bytes(child)
            walked += 1
        if walked < count:
            if walked == 0:
                raise NineError("No such file or directory")
            # A partial walk leaves newfid unaffected, per section 5 of the
            # protocol; only a complete walk binds it.
            self.reply(RWALK, tag, struct.pack("<H", walked) + qids)
            return
        self.fids[newfid] = node
        self.reply(RWALK, tag, struct.pack("<H", walked) + qids)

    def read(self, tag, message):
        fid = message.u4()
        offset = message.u8()
        count = message.u4()
        node = self.fid(fid)
        if fid not in self.open_fids:
            raise NineError("fid is not open")
        count = min(count, self.msize - IOHDRSZ)
        if node.is_dir:
            if offset not in node.offsets:
                raise NineError("directory read is not at an entry boundary")
            data = b""
            for entry in (stat_bytes(child) for child in node.children):
                if offset > 0:
                    offset -= len(entry)
                    continue
                if len(data) + len(entry) > count:
                    break
                data += entry
        else:
            if node.refusal is not None:
                raise NineError(node.refusal)
            data = node.data[offset:offset + count] if offset < len(node.data) else b""
        self.reply(RREAD, tag, struct.pack("<I", len(data)) + data)


def serve_connection(sock, root):
    with sock:
        try:
            connection = Connection(sock, root)
            connection.serve()
        except (ProtocolError, ConnectionError, OSError):
            return


def snapshot_from_store(path, budget):
    """Replay one committed store under the shared lock and read it all out.

    The lock, the bridge and the ACL2 process are held for this function and
    no longer: the returned tree is the whole of what any mount will show.
    """
    store = Store(path, writable=False)
    bridge = None
    reader = None
    store.acquire()
    try:
        bridge = Acl2Store()
        store.recover(bridge)
        reader = Acl2Reader(bridge)
        return build_snapshot(Projection(reader, budget))
    finally:
        if reader is not None:
            reader.close()
        if bridge is not None:
            bridge.close()
        store.close()


def terminate_on_signal(signum, unused_frame):
    raise SystemExit(128 + signum)


def main():
    signal.signal(signal.SIGTERM, terminate_on_signal)
    parser = UsageParser()
    parser.add_argument("--store", required=True, help="durable store snapshot to serve")
    parser.add_argument("--port", type=int, default=5640)
    parser.add_argument("--host", default="127.0.0.1",
                        help="loopback by default; the view has no authentication")
    parser.add_argument("--max-bytes", type=int, default=DEFAULT_MAX_SNAPSHOT_BYTES)
    args = parser.parse_args()
    if not 0 <= args.port <= 65535:
        parser.error("--port must be from 0 through 65535")
    if args.max_bytes <= 0:
        parser.error("--max-bytes must be positive")

    try:
        root = snapshot_from_store(args.store, args.max_bytes)
    except StoreError as fault:
        print("fn9p: {}".format(fault), file=sys.stderr)
        return EXIT_FAULT
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as listener:
        listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        listener.bind((args.host, args.port))
        listener.listen(8)
        print("LISTENING {}".format(listener.getsockname()[1]), flush=True)
        while True:
            client, _ = listener.accept()
            client.settimeout(None)
            # The snapshot is immutable and no bridge remains, so connections
            # share it without any lock.
            threading.Thread(target=serve_connection, args=(client, root),
                             daemon=True).start()
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
