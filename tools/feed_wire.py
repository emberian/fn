#!/usr/bin/env python3
"""FNFD journal I/O and the raw NNTP client half, for the owner.

These two objects were the durable-and-transport half of `tools/run_feed.py`,
the standalone feed driver retired on 2026-09-21 (`w11/harness-health`).  The
feed itself is the owner's: `tools/run_owner.py`'s `Feed`, stepping
`books/owner-feed.lisp` in the one process that holds the store lock.  What
is left here is what a host must do and a book cannot, and nothing else:

  * `Journal` -- ACL2 owns the length envelope, frame checks, safe repair
    offset and barrier phase machine in books/feed-journal.lisp. The host
    performs bounded reads, truncate, write and platform durability barriers.
  * `Session` -- a TCP connection, a CRLF line reader and RFC 3977 section
    3.1.1 dot stuffing of an outgoing article block.  `books/wire.lisp` has
    a stuffer; wiring the owner's outbound block through it is one packet
    and is recorded as open in specs/peering.md.

No decision of the feed machine is here.  Which article is selected, what
command line goes out, what a response code means, when to back off and for
how long, and what an FNFD record contains are all
`books/peer-feed.lisp`/`books/owner-feed.lisp` through the owner's bridge.
`MAX_LINE` remains the Session host refusal bound; journal read bounds
come directly from ACL2.
"""
from __future__ import annotations

import os
import socket

from run_store import (StoreFault, StoreIndeterminate, fsync_dir, fsync_file,
                       write_all, NO_FAULTS)

MAX_LINE = 4096


class FeedError(RuntimeError):
    pass


class Journal:
    """I/O for ACL2's FNFD envelope and durable recovery state machine.

    Construction replays and repairs before permitting append. The caller
    holds the store writer lock. Invalid complete evidence is left untouched.
    Every I/O failure requires recovery in a new owner process.
    """

    def __init__(self, root: str, peer: bytes, bridge, faults=NO_FAULTS):
        self.root = root
        self.peer = peer.decode("utf-8")
        self.bridge = bridge
        self.faults = faults
        self.phase = "closed"
        self.handle = None
        self.replayed = 0
        self.dir = os.path.join(root, "feed")
        self.path = os.path.join(self.dir, self.peer + ".fnfd")
        try:
            os.makedirs(self.dir, exist_ok=True)
            self.handle = os.open(self.path, os.O_RDWR | os.O_CREAT, 0o600)
            self._step("opened")
            bridge.feed_journal_begin()
            while True:
                prefix = os.read(self.handle, bridge.feed_journal_prefix_size())
                plan = bridge.feed_journal_prefix(prefix)
                frame = os.read(self.handle, plan) if isinstance(plan, int) else b""
                status = bridge.feed_journal_scan(self.peer, prefix, frame)
                if status == "next":
                    self.replayed += 1
                    continue
                if status == "invalid":
                    raise StoreFault("invalid complete FNFD evidence: " + self.path)
                self._step(status)
                if status == "repair":
                    os.ftruncate(self.handle, bridge.feed_journal_offset())
                    self._step("truncated")
                break
            fsync_file(self.handle)
            self._step("content-durable")
            fsync_dir(self.dir)
            self._step("directory-durable")
            fsync_dir(self.root)
            self._step("parent-durable")
            os.lseek(self.handle, 0, os.SEEK_END)
        except StoreFault:
            self.close()
            raise
        except Exception as error:
            self.close()
            raise StoreIndeterminate("FNFD recovery uncertain: " + self.path) from error

    def _step(self, event):
        self.phase = self.bridge.feed_journal_step(self.phase, event)
        if self.phase == "uncertain":
            raise StoreIndeterminate("FNFD journal requires recovery")
        self.faults.at("feed-journal:" + event)

    def append(self, frame: bytes):
        try:
            envelope = self.bridge.feed_journal_wrap(frame)
            self._step("append")
            write_all(self.handle, envelope)
            self._step("written")
            fsync_file(self.handle)
            self._step("append-durable")
        except Exception as error:
            try:
                self.phase = self.bridge.feed_journal_step(self.phase, "failed")
            finally:
                # A lost bridge cannot issue a phase result; closing the I/O
                # capability still prevents any further write from this object.
                self.close()
            raise StoreIndeterminate("FNFD append uncertain: " + self.path) from error

    def close(self):
        if self.handle is not None:
            descriptor, self.handle = self.handle, None
            os.close(descriptor)


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
        """RFC 3977 section 3.1.1: dot-stuffed, terminated by a lone dot.

        Exactly ONE CRLF comes off the end: it is the terminator of the
        article's last line, and the block supplies its own.  `rstrip` here
        removes EVERY trailing CRLF, so an article whose last line is blank
        --- which is what an article POSTed through the server stores, since
        the dot block it arrived in carried that line --- reaches the peer
        one line shorter, and an article with two blank lines at the end
        reaches it two lines shorter.  RFC 5537 3.6 lets a relaying agent
        alter Path and Xref and nothing else.

        This is the SECOND time this line has shipped: w11/twonode-feed
        removed the same `rstrip` from `tools/run_feed.py` on 2026-09-21
        (measured then as `source_lines: 11, target_lines: 10,
        only_on_target: [], only_on_source: []` --- one line fewer and not
        one line different in content), and `c3aacd2` moved the method here
        when that driver was retired, from the copy that still had it.  The
        corrected two-node gate at `f49a844` measured the same three
        numbers again, on `<fed-ab@example.invalid>`, `<fed-ba@...>` and
        `<fed-streaming@...>` --- the three articles the OWNER feed carries.
        The hand-driven relay was unaffected because it frames with
        `tools/twonode_gate.py`'s own `send_block`, which never had the bug.

        The durable fix is not here: the block rendering is framing and
        AGENTS.md gives framing to ACL2 (`fn-wire-stuff-line` exists;
        the whole-block renderer and its round trip against `fn-wire-drive`
        do not).  That is a packet, on the board.
        """
        body = article.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
        if body.endswith(b"\r\n"):
            body = body[:-2]
        lines = body.split(b"\r\n")
        stuffed = b"\r\n".join(b"." + one if one.startswith(b".") else one
                               for one in lines)
        self.sock.sendall(stuffed + b"\r\n.\r\n")

    def close(self):
        try:
            self.sock.close()
        except OSError:
            pass
