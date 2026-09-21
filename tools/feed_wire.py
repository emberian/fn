#!/usr/bin/env python3
"""The FNFD journal file layout and the raw NNTP client half, for the owner.

These two objects were the durable-and-transport half of `tools/run_feed.py`,
the standalone feed driver retired on 2026-09-21 (`w11/harness-health`).  The
feed itself is the owner's: `tools/run_owner.py`'s `Feed`, stepping
`books/owner-feed.lisp` in the one process that holds the store lock.  What
is left here is what a host must do and a book cannot, and nothing else:

  * `Journal` -- an append-only file of length-prefixed FNFD frames, one per
    peer, at `<store>/feed/<peer>.fnfd`, fsynced before the effect it
    authorizes.  The 4-octet big-endian length is FILE LAYOUT and not a
    frame field: it is what lets the reader hand ACL2 one whole record at a
    time.  A torn tail ends the record stream, because a torn tail is the
    crash image and everything before it stands.
  * `Session` -- a TCP connection, a CRLF line reader and RFC 3977 section
    3.1.1 dot stuffing of an outgoing article block.  `books/wire.lisp` has
    a stuffer; wiring the owner's outbound block through it is one packet
    and is recorded as open in specs/peering.md.

No decision of the feed machine is here.  Which article is selected, what
command line goes out, what a response code means, when to back off and for
how long, and what an FNFD record contains are all
`books/peer-feed.lisp`/`books/owner-feed.lisp` through the owner's bridge.
`MAX_RECORD` and `MAX_LINE` are host refusal bounds on untrusted input,
deliberately above the book's own `*fn-feed-max-payload*` (1024) so that a
frame the book would refuse is refused BY THE BOOK and not silently by a
Python slice.
"""
from __future__ import annotations

import os
import socket
import struct

TRAILER_BYTES = 32
LENGTH_BYTES = 4
MAX_RECORD = 4096
MAX_LINE = 4096


class FeedError(RuntimeError):
    pass


class Journal:
    """Append-only FNFD file for one peer.  Durable before the effect."""

    def __init__(self, root: str, peer: bytes):
        self.dir = os.path.join(root, "feed")
        os.makedirs(self.dir, exist_ok=True)
        self.path = os.path.join(self.dir, peer.decode("ascii") + ".fnfd")
        self.handle = open(self.path, "ab")

    def append(self, frame: bytes):
        if len(frame) > MAX_RECORD:
            raise FeedError("FNFD record over the bound")
        self.handle.write(struct.pack(">I", len(frame)) + frame)
        self.handle.flush()
        os.fsync(self.handle.fileno())

    def records(self):
        if not os.path.exists(self.path):
            return
        with open(self.path, "rb") as handle:
            blob = handle.read()
        offset = 0
        while offset + LENGTH_BYTES <= len(blob):
            (length,) = struct.unpack(">I", blob[offset:offset + LENGTH_BYTES])
            offset += LENGTH_BYTES
            if length > MAX_RECORD or offset + length > len(blob):
                # A torn tail is the crash image: everything before it stands.
                return
            yield blob[offset:offset + length]
            offset += length

    def close(self):
        self.handle.close()


class Session:
    """The raw NNTP client half: a line reader and a dot-block writer."""

    def __init__(self, host: str, port: int, timeout: float):
        self.sock = socket.create_connection((host, port), timeout)
        self.buffer = b""
        try:
            self.greeting = self.line()
        except BaseException:
            # A peer whose greeting is over MAX_LINE used to leak this
            # socket: `line` raised out of the constructor, so no caller
            # ever held the object it would have closed.
            self.close()
            raise

    def line(self) -> bytes:
        while b"\r\n" not in self.buffer:
            if len(self.buffer) > MAX_LINE:
                raise FeedError("response line over the bound")
            chunk = self.sock.recv(4096)
            if not chunk:
                return b""
            self.buffer += chunk
        one, self.buffer = self.buffer.split(b"\r\n", 1)
        return one

    def send(self, octets: bytes):
        self.sock.sendall(octets)

    def send_block(self, article: bytes):
        """RFC 3977 section 3.1.1: dot-stuffed, terminated by a lone dot."""
        body = article.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
        lines = body.split(b"\r\n")
        stuffed = b"\r\n".join(b"." + one if one.startswith(b".") else one
                               for one in lines)
        self.sock.sendall(stuffed.rstrip(b"\r\n") + b"\r\n.\r\n")

    def close(self):
        try:
            self.sock.close()
        except OSError:
            pass
