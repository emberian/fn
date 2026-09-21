#!/usr/bin/env python3
"""`tools/feed_wire.py`: the FNFD file layout and the outgoing article block.

This file used to drive `tools/run_feed.py`, a standalone feed client, against
`tests/twonode_gate_fake/tools/run_peer.py`.  That driver was retired on
2026-09-21 (`w11/harness-health`): the owner drives the feed, the Python
three-digit reply split it carried is `fn-own-feed-response-code`, and its
remaining copies of owner decisions drifted invisibly three times.  Its feed
cases are not lost -- they are stronger somewhere else.  A crash between
`sent` and the outcome, resolved by a CHECK and never a blind TAKETHIS, with
exactly one copy at the far end, is `tools/twonode_gate.py`'s
`scenario_feed_restart` (K5) against a real fn node and a real journal; the
offer-once-each case is `scenario_owner_feed`.

What is left here is what those gates do NOT isolate: the two host-side
mechanisms `tools/run_owner.py` imports.  Neither needs ACL2, so neither
skips, which is why they belong in a unit test at all.

  * the journal's own layout -- a length prefix, a round trip, the bound, and
    a torn tail ending the record stream rather than raising;
  * RFC 3977 section 3.1.1 dot stuffing of an outgoing article block, which
    had no test of any kind while it lived in the retired driver.
"""
from __future__ import annotations

import socket
import struct
import sys
import tempfile
import threading
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import feed_wire  # noqa: E402


class JournalTests(unittest.TestCase):
    """`<store>/feed/<peer>.fnfd`, read back by the same rules that wrote it."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-feed-journal-")
        self.addCleanup(self.temp.cleanup)
        self.root = self.temp.name

    def test_a_peer_gets_its_own_file_named_after_it(self):
        journal = feed_wire.Journal(self.root, b"inn")
        self.addCleanup(journal.close)
        self.assertEqual(Path(journal.path),
                         Path(self.root) / "feed" / "inn.fnfd")

    def test_records_read_back_in_order_with_their_lengths(self):
        journal = feed_wire.Journal(self.root, b"inn")
        self.addCleanup(journal.close)
        frames = [b"FNFD" + bytes([0, 0, 0, n]) + bytes(n) for n in (1, 7, 40)]
        for frame in frames:
            journal.append(frame)
        self.assertEqual(list(journal.records()), frames)
        blob = Path(journal.path).read_bytes()
        self.assertEqual(struct.unpack(">I", blob[:4])[0], len(frames[0]))

    def test_a_record_over_the_bound_is_refused_and_not_written(self):
        journal = feed_wire.Journal(self.root, b"inn")
        self.addCleanup(journal.close)
        journal.append(b"kept")
        with self.assertRaises(feed_wire.FeedError):
            journal.append(b"x" * (feed_wire.MAX_RECORD + 1))
        self.assertEqual(list(journal.records()), [b"kept"])

    def test_a_torn_tail_ends_the_record_stream(self):
        # The crash image: a length prefix whose record is not all there.
        # Everything written before it stands and nothing raises.
        path = Path(self.root) / "feed" / "inn.fnfd"
        path.parent.mkdir(parents=True)
        path.write_bytes(struct.pack(">I", 4) + b"abcd" +
                         struct.pack(">I", 99) + b"xy")
        journal = feed_wire.Journal(self.root, b"inn")
        self.addCleanup(journal.close)
        self.assertEqual(list(journal.records()), [b"abcd"])

    def test_a_length_that_claims_more_than_the_bound_ends_the_stream(self):
        path = Path(self.root) / "feed" / "inn.fnfd"
        path.parent.mkdir(parents=True)
        path.write_bytes(struct.pack(">I", 4) + b"abcd" +
                         struct.pack(">I", feed_wire.MAX_RECORD + 1) +
                         b"z" * (feed_wire.MAX_RECORD + 1))
        journal = feed_wire.Journal(self.root, b"inn")
        self.addCleanup(journal.close)
        self.assertEqual(list(journal.records()), [b"abcd"])

    def test_an_absent_file_yields_no_records(self):
        path = Path(self.root) / "feed"
        path.mkdir()
        journal = feed_wire.Journal.__new__(feed_wire.Journal)
        journal.path = str(path / "never-written.fnfd")
        self.assertEqual(list(journal.records()), [])


class Listener:
    """One loopback connection that greets and then records what it is sent."""

    def __init__(self, greeting=b"200 fake ready\r\n"):
        self.sock = socket.socket()
        self.sock.bind(("127.0.0.1", 0))
        self.sock.listen(1)
        self.port = self.sock.getsockname()[1]
        self.received = b""
        self.thread = threading.Thread(target=self._serve, args=(greeting,),
                                       daemon=True)
        self.thread.start()

    def _serve(self, greeting):
        conn, _ = self.sock.accept()
        conn.sendall(greeting)
        conn.settimeout(5.0)
        try:
            while True:
                chunk = conn.recv(4096)
                if not chunk:
                    break
                self.received += chunk
                if self.received.endswith(b"\r\n.\r\n"):
                    break
        except OSError:
            pass
        conn.close()

    def stop(self):
        self.thread.join(timeout=5)
        self.sock.close()


class SessionTests(unittest.TestCase):
    """The client half: the greeting, the line reader and the dot block."""

    def connected(self, greeting=b"200 fake ready\r\n"):
        listener = Listener(greeting)
        self.addCleanup(listener.stop)
        session = feed_wire.Session("127.0.0.1", listener.port, 5.0)
        self.addCleanup(session.close)
        return listener, session

    def test_the_greeting_is_read_before_anything_is_sent(self):
        _, session = self.connected()
        self.assertEqual(session.greeting, b"200 fake ready")

    def test_a_line_is_split_at_crlf_and_the_rest_is_buffered(self):
        listener, session = self.connected(b"203 one\r\n438 two\r\n")
        self.assertEqual(session.greeting, b"203 one")
        self.assertEqual(session.line(), b"438 two")
        listener.stop()

    def test_a_leading_dot_is_doubled_and_the_block_ends_with_a_lone_dot(self):
        # RFC 3977 section 3.1.1.  A body line that begins with `.` must
        # reach the peer as `..`, or the peer reads it as the terminator.
        listener, session = self.connected()
        session.send_block(b"Subject: t\r\n\r\n.signature\r\nlast\r\n")
        listener.stop()
        self.assertTrue(listener.received.endswith(b"\r\n.\r\n"),
                        listener.received)
        self.assertIn(b"\r\n..signature\r\n", listener.received)
        self.assertNotIn(b"\r\n.signature\r\n", listener.received)

    def test_a_bare_lf_article_goes_out_crlf_terminated(self):
        listener, session = self.connected()
        session.send_block(b"Subject: t\n\nbody\n")
        listener.stop()
        self.assertEqual(listener.received,
                         b"Subject: t\r\n\r\nbody\r\n.\r\n")
        # no bare LF survives: every \n on the wire is preceded by \r
        for index, byte in enumerate(listener.received):
            if byte == 0x0a:
                self.assertEqual(listener.received[index - 1], 0x0d)

    def test_a_response_line_over_the_bound_is_refused_and_leaks_nothing(self):
        listener = Listener(b"2" * (feed_wire.MAX_LINE + 10))
        self.addCleanup(listener.stop)
        with self.assertRaises(feed_wire.FeedError):
            feed_wire.Session("127.0.0.1", listener.port, 5.0)
        # and the socket it opened is closed: the constructor raised, so no
        # caller holds the object whose `close` would have been called.


if __name__ == "__main__":
    unittest.main()
