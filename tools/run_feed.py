#!/usr/bin/env python3
"""Drive one peer's outbound feed over a raw TCP NNTP session (packet K2).

One process, one peer, one connection.  Every state decision is one call into
`books/peer-feed.lisp` through a live ACL2 session: which article is selected
under the contact window, what command line to send, what a response code
means, when to back off and for how long, when an entry is dropped and with
what reason, and what the FNFD journal records are.  This file moves bytes,
reads the clock, appends to the journal file and computes SHA-256 over octet
strings it does not interpret (A-CRYPTO).

Two things Python does that are worth naming, because the "one owner per
decision" rule (AGENTS.md) is what keeps this file honest:

  * The record trailer.  `fn-feed-encode` takes the digest as an argument, so
    the host asks ACL2 for the frame with a zero trailer, hashes the protected
    prefix and appends the real one.  The header, the field encoding and every
    bound are still ACL2's; Python slices at a constant it did not choose.
  * The status line is NO LONGER read here.  RFC 3977 section 3.2 framing --
    the three-digit code -- moved into ACL2 as `fn-own-feed-response-code`
    (books/owner-feed.lisp) in w10/owner-feed, which is why this file now
    includes books/owner-feed rather than books/peer-feed.  The Message-ID a
    CHECK or TAKETHIS reply echoes is not read back at all: at most one entry
    is in flight per peer (`fn-feedp`), so the in-flight Message-ID is the
    unambiguous subject.

This file is now a THIN DRIVER kept for `tests/test_feed.py` and for feeding
one peer without an owner process.  The live feed is driven by the owner
(tools/run_owner.py, the `Feed` class), which is the one process that holds
the store lock.

The journal is `<journal>/feed/<peer>.fnfd`: a length-prefixed sequence of
FNFD frames.  The 4-octet big-endian length is file layout, not a frame field;
it is what lets the reader hand ACL2 one whole record at a time.
"""
from __future__ import annotations

import argparse
import hashlib
import os
import socket
import struct
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))

from run_store import Acl2Store, StoreError  # noqa: E402  the ACL2 bridge

TRAILER_BYTES = 32
LENGTH_BYTES = 4
MAX_RECORD = 4096
MAX_LINE = 4096
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_FAULT = 0, 1, 3, 4


class FeedError(RuntimeError):
    pass


def literal_octets(data: bytes) -> str:
    return "'(" + " ".join(str(b) for b in data) + ")"


def parse_octets(body: bytes) -> bytes:
    """An ACL2 proper list of decimal naturals, or NIL."""
    text = body.strip()
    if text == b"NIL":
        return b""
    if not (text.startswith(b"(") and text.endswith(b")")):
        raise FeedError("unexpected ACL2 octet list: %r" % text[:80])
    return bytes(int(token) for token in text[1:-1].split())


class Acl2Feed:
    """The feed machine of books/peer-feed.lisp, one live ACL2 session.

    The state lives in an ACL2 state global (`(@ ff)`), so no feed value is
    ever re-parsed or rebuilt on the Python side.
    """

    def __init__(self, peer: bytes, max_queue: int, backoff_ms: int,
                 retry_bound: int, streaming: bool, horizon: int):
        self.bridge = Acl2Store()
        self.peer = peer
        self.bridge.call('(include-book "books/owner-feed")')
        self.limits = "(fn-feed-limits {} {} {} {})".format(
            max_queue, backoff_ms, retry_bound, "t" if streaming else "nil")
        self.contact = '(fn-sched-contact "{}" 0 {})'.format(
            peer.decode("ascii"), horizon)
        self.open(None)

    def _value(self, form: str) -> bytes:
        output = self.bridge.call(form).strip()
        if not output.endswith(b"ACL2 !>"):
            raise FeedError("unexpected ACL2 reply")
        return output[:-len(b"ACL2 !>")].strip()

    def open(self, conn):
        self.bridge.call("(assign ff (fn-feed-open {} {} {} {}))".format(
            literal_octets(self.peer), self.limits, self.contact,
            "nil" if conn is None else str(conn)))

    def set_conn(self, conn):
        self.bridge.call("(assign ff (fn-feed-with-conn (@ ff) {}))".format(
            "nil" if conn is None else str(conn)))

    def restart(self):
        self.bridge.call("(assign ff (fn-feed-restart (@ ff)))")

    def feedp(self) -> bool:
        return self._value("(fn-feedp (@ ff))") == b"T"

    def enqueue(self, msgid: bytes, tick: int):
        self.bridge.call("(assign ff (fn-feed-enqueue (@ ff) {} {}))".format(
            literal_octets(msgid), tick))

    @staticmethod
    def _obs(monotonic: int) -> str:
        return "(fn-clock-observation {} 0 0 nil)".format(monotonic)

    def selection(self, monotonic: int):
        value = parse_octets(self._value(
            "(fn-feed-selection (@ ff) {})".format(self._obs(monotonic))))
        return value or None

    def tick(self, monotonic: int):
        """Select and drive.  Returns the command octets, or None."""
        form = "(fn-feed-tick-step (@ ff) {})".format(self._obs(monotonic))
        effects = self._value("(mv-nth 1 {})".format(form))
        self.bridge.call("(assign ff (mv-nth 0 {}))".format(form))
        if effects == b"NIL":
            return None
        # `((:COMMAND <conn> (<octets>)))`: the octets are the third item, and
        # ACL2 printed them, so they are read back by the same reader.
        return parse_octets(self._value(
            "(fn-frame-item 2 (car (mv-nth 1 {})))".format(form)))

    def observe(self, code: int, msgid: bytes, article: bytes,
                monotonic: int):
        form = "(fn-feed-observe (@ ff) (fn-feed-response {} {}) {} {})".format(
            code, literal_octets(msgid), literal_octets(article),
            self._obs(monotonic))
        effects = self._value("(mv-nth 1 {})".format(form))
        self.bridge.call("(assign ff (mv-nth 0 {}))".format(form))
        if effects == b"NIL":
            return None
        return parse_octets(self._value(
            "(fn-frame-item 2 (car {}))".format(
                "(mv-nth 1 {})".format(form))))

    def state_of(self, msgid: bytes) -> str:
        return self._value(
            "(fn-feed-state-of {} (fn-feed-queue (@ ff)))".format(
                literal_octets(msgid))).decode("ascii", "replace")

    def attempt_of(self, msgid: bytes) -> int:
        return int(self._value(
            "(fn-feed-state-attempt (fn-feed-state-of {} (fn-feed-queue (@ ff))))"
            .format(literal_octets(msgid))))

    def record(self, kind: str, values: str) -> bytes:
        """One FNFD frame: ACL2 builds it, the host seals it (A-CRYPTO)."""
        zero = literal_octets(bytes(TRAILER_BYTES))
        framed = parse_octets(self._value(
            "(fn-feed-encode {} {} {})".format(kind, values, zero)))
        if not framed:
            raise FeedError("ACL2 refused the record " + kind)
        protected = framed[:-TRAILER_BYTES]
        return protected + hashlib.sha256(protected).digest()

    def decode(self, frame: bytes) -> str:
        if len(frame) <= TRAILER_BYTES:
            raise FeedError("short FNFD record")
        digest = hashlib.sha256(frame[:-TRAILER_BYTES]).digest()
        return self._value("(fn-feed-decode {} {})".format(
            literal_octets(frame), literal_octets(digest))
        ).decode("ascii", "replace")

    def apply_frame(self, frame: bytes):
        digest = hashlib.sha256(frame[:-TRAILER_BYTES]).digest()
        decoded = "(fn-feed-decode {} {})".format(literal_octets(frame),
                                                  literal_octets(digest))
        self.bridge.call(
            "(assign ff (fn-feed-apply-record (@ ff)"
            " (fn-frame-result-kind {0}) (fn-frame-result-payload {0})))"
            .format(decoded))

    def response_code(self, line: bytes):
        """The reply code, read by ACL2 (fn-own-feed-response-code).

        RFC 3977 section 3.2 says a reply begins with three digits whose
        first is 1 to 5; that test, and the refusal of anything else, is the
        book's.  This method marshals one line and reads back one number.
        """
        value = self._value("(fn-own-feed-response-code {})".format(
            literal_octets(line)))
        return None if value == b"NIL" else int(value)

    def close(self):
        self.bridge.close()


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
        self.greeting = self.line()

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




def run(args) -> int:
    peer = args.peer.encode("ascii")
    articles = {}
    for pair in args.article:
        msgid, _, path = pair.partition("=")
        with open(path, "rb") as handle:
            articles[msgid.encode("ascii")] = handle.read()

    feed = Acl2Feed(peer, args.max_queue, args.backoff_ms, args.retry_bound,
                    not args.no_streaming, args.horizon)
    journal = Journal(args.journal, peer)
    started = time.monotonic()

    def now() -> int:
        return int((time.monotonic() - started) * 1000)

    try:
        # Replay first: the journal is the truth about what was offered.
        replayed = 0
        for frame in journal.records():
            feed.apply_frame(frame)
            replayed += 1
        if replayed:
            journal.append(feed.record(":feed-restart",
                                       "(list {})".format(literal_octets(peer))))
            feed.restart()
        print("REPLAYED {}".format(replayed), flush=True)

        session = Session(args.host, args.port, args.timeout)
        print("GREETING {}".format(
            session.greeting.decode("ascii", "replace")), flush=True)
        if not args.no_streaming:
            session.send(b"MODE STREAM\r\n")
            print("MODE {}".format(session.line().decode("ascii", "replace")),
                  flush=True)
        feed.set_conn(1)

        for msgid in articles:
            if feed.state_of(msgid) == "NIL":
                journal.append(feed.record(
                    ":feed-enqueue",
                    "(list {} {} {})".format(literal_octets(peer),
                                             literal_octets(msgid), now())))
                feed.enqueue(msgid, now())

        deadline = time.monotonic() + args.deadline
        while time.monotonic() < deadline:
            selected = feed.selection(now())
            if selected is None:
                if all(feed.state_of(m) in (":DONE",) or
                       feed.state_of(m).startswith("(:DROPPED")
                       for m in articles):
                    break
                time.sleep(0.05)
                continue
            attempt = int(feed._value("(fn-feed-next-attempt (@ ff))"))
            journal.append(feed.record(
                ":feed-offer",
                "(list {} {} {} {})".format(literal_octets(peer),
                                            literal_octets(selected),
                                            attempt, now())))
            command = feed.tick(now())
            if command is None:
                continue
            if args.fault == "after-offer":
                raise SystemExit(EXIT_FAULT)
            session.send(command)
            code = feed.response_code(session.line())
            if code is None:
                break
            # One entry in flight per peer, so the selected Message-ID IS the
            # subject of this reply; nothing is read back from the echo.
            target = selected
            body = articles.get(target, b"")
            if code in (335, 238):
                journal.append(feed.record(
                    ":feed-sent",
                    "(list {} {} {})".format(literal_octets(peer),
                                             literal_octets(target),
                                             feed.attempt_of(target))))
                if args.fault == "after-sent":
                    raise SystemExit(EXIT_FAULT)
                transfer = feed.observe(code, target, body, now())
                if transfer is None:
                    continue
                # CHECK/TAKETHIS: the command line and the block are one write.
                if transfer.startswith(b"TAKETHIS"):
                    head = transfer.split(b"\r\n", 1)[0] + b"\r\n"
                    session.send(head)
                session.send_block(body)
                code = feed.response_code(session.line())
                if code is None:
                    break
            journal.append(feed.record(
                ":feed-outcome",
                "(list {} {} {} {})".format(literal_octets(peer),
                                            literal_octets(target),
                                            feed.attempt_of(target), code)))
            feed.observe(code, target, b"", now())
            print("OUTCOME {} {} {}".format(
                target.decode("ascii", "replace"), code,
                feed.state_of(target)), flush=True)

        for msgid in articles:
            print("FINAL {} {}".format(msgid.decode("ascii", "replace"),
                                       feed.state_of(msgid)), flush=True)
        session.close()
        return EXIT_OK
    except (StoreError, FeedError, OSError) as error:
        print("FAULT {}".format(error), file=sys.stderr, flush=True)
        return EXIT_FAULT
    finally:
        journal.close()
        feed.close()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--journal", required=True)
    parser.add_argument("--peer", required=True)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, required=True)
    parser.add_argument("--article", action="append", default=[],
                        metavar="MSGID=PATH")
    parser.add_argument("--no-streaming", action="store_true",
                        help="offer with IHAVE (RFC 3977 6.3.2) not CHECK")
    parser.add_argument("--max-queue", type=int, default=64)
    parser.add_argument("--backoff-ms", type=int, default=100)
    parser.add_argument("--retry-bound", type=int, default=3)
    parser.add_argument("--horizon", type=int, default=10 ** 12)
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--deadline", type=float, default=120.0)
    parser.add_argument("--fault", choices=["after-offer", "after-sent"],
                        help="exit at an FNFD record boundary, for the tests")
    return run(parser.parse_args(argv))


if __name__ == "__main__":
    sys.exit(main())
