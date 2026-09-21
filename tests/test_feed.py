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
mechanisms `tools/run_owner.py` imports.  The journal unit tests script bridge answers to isolate I/O; real codec
and recovery composition are exercised by test_feed_journal_live.py.

  * the journal's ordered barriers, exact ACL2 envelope writes, authoritative
    repair offset, preservation of invalid evidence and uncertainty failures;
  * RFC 3977 section 3.1.1 dot stuffing of an outgoing article block, which
    had no test of any kind while it lived in the retired driver.
"""
from __future__ import annotations

import socket
import sys
import tempfile
import threading
import unittest
from unittest import mock
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import feed_wire  # noqa: E402


class JournalTests(unittest.TestCase):
    """Host I/O with scripted ACL2 answers; no second codec or policy."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-feed-journal-")
        self.addCleanup(self.temp.cleanup)
        self.root = self.temp.name
        self.bridge = mock.Mock()
        self.bridge.feed_journal_prefix_size.return_value = 4
        self.bridge.feed_journal_prefix.return_value = "end"
        self.bridge.feed_journal_scan.return_value = "end"
        self.bridge.feed_journal_step.return_value = "ready"
        self.bridge.feed_journal_offset.return_value = 8
        self.bridge.feed_journal_wrap.return_value = b"encoded-envelope"
        self.bridge.feed_filename_components.return_value = (b"inn.fnfd",)

    def open(self):
        journal = feed_wire.Journal(self.root, b"inn", self.bridge)
        self.addCleanup(journal.close)
        return journal

    def test_creation_barriers_precede_any_append(self):
        with mock.patch.object(feed_wire, "fsync_file") as content, \
             mock.patch.object(feed_wire, "fsync_dir") as directory:
            journal = self.open()
            content.assert_called_once_with(journal.handle)
            self.assertEqual(directory.call_args_list,
                             [mock.call(journal.dir), mock.call(self.root)])
            self.assertEqual(self.bridge.feed_journal_step.call_args_list,
                             [mock.call("closed", "opened"),
                              mock.call("ready", "end"),
                              mock.call("ready", "content-durable"),
                              mock.call("ready", "directory-durable"),
                              mock.call("ready", "parent-durable")])

    def test_non_ancestor_directory_walk_stops_at_root(self):
        # Regression for the 2026-09-21 test-loop incident: dirname('/') is
        # '/', so a stop directory outside the ancestor chain must fail before
        # attempting to re-visit root rather than loop and retain mock calls.
        with mock.patch.object(feed_wire, "fsync_dir") as directory:
            with self.assertRaisesRegex(feed_wire.StoreFault,
                                        "not an ancestor"):
                feed_wire.fsync_ancestor_directories("/unrelated/child",
                                                      "/expected/feed")
        self.assertEqual(directory.call_args_list, [mock.call("/unrelated")])

    def test_append_writes_exact_acl2_envelope(self):
        journal = self.open()
        journal.append(b"frame")
        self.bridge.feed_journal_wrap.assert_called_once_with(b"frame")
        self.assertEqual(Path(journal.path).read_bytes(), b"encoded-envelope")

    def test_repair_uses_acl2_safe_offset_and_barriers_before_append(self):
        path = Path(self.root) / "feed" / "inn.fnfd"
        path.parent.mkdir()
        path.write_bytes(b"retainedTORN")
        self.bridge.feed_journal_scan.return_value = "repair"
        journal = self.open()
        self.assertEqual(path.read_bytes(), b"retained")
        journal.append(b"frame")
        self.assertEqual(path.read_bytes(), b"retainedencoded-envelope")

    def test_complete_invalid_evidence_is_never_truncated(self):
        path = Path(self.root) / "feed" / "inn.fnfd"
        path.parent.mkdir()
        path.write_bytes(b"invalid-complete-evidence")
        self.bridge.feed_journal_scan.return_value = "invalid"
        with self.assertRaises(feed_wire.StoreFault):
            self.open()
        self.assertEqual(path.read_bytes(), b"invalid-complete-evidence")

    def test_legacy_timing_outcome_requires_migration_and_is_preserved(self):
        path = Path(self.root) / "feed" / "inn.fnfd"
        path.parent.mkdir()
        path.write_bytes(b"legacy-timing-evidence")
        self.bridge.feed_journal_scan.return_value = "migration-required"
        with self.assertRaisesRegex(feed_wire.StoreFault,
                                   "FNFD migration required"):
            self.open()
        self.assertEqual(path.read_bytes(), b"legacy-timing-evidence")

    def test_content_and_both_namespace_barrier_failures_are_uncertain(self):
        for barrier, results in (("fsync_file", [OSError("content")]),
                                 ("fsync_dir", [OSError("feed directory")]),
                                 ("fsync_dir", [None, OSError("store directory")])):
            with self.subTest(barrier=barrier, results=results):
                with mock.patch.object(feed_wire, barrier, side_effect=results):
                    with self.assertRaises(feed_wire.StoreIndeterminate):
                        self.open()

    def test_v1_components_are_used_as_acl2_returned(self):
        self.bridge.feed_filename_components.return_value = (
            b"v1", b"2e2e2f657363617065", b"journal.fnfd")
        with mock.patch.object(feed_wire, "fsync_file"), \
             mock.patch.object(feed_wire, "fsync_dir"):
            journal = self.open()
        self.assertEqual(Path(journal.path).relative_to(Path(self.root) / "feed"),
                         Path("v1") / "2e2e2f657363617065" / "journal.fnfd")
        self.assertNotIn("..", Path(journal.path).parts)

    def test_malformed_acl2_component_is_not_a_path(self):
        self.bridge.feed_filename_components.return_value = (b"..", b"journal.fnfd")
        with self.assertRaises(feed_wire.StoreFault):
            self.open()

    def test_discovery_uses_acl2_decoder_for_legacy_and_v1(self):
        legacy = Path(self.root) / "feed" / "inn.fnfd"
        encoded = Path(self.root) / "feed" / "v1" / "2e2e2f657363617065" / "journal.fnfd"
        legacy.parent.mkdir()
        encoded.parent.mkdir(parents=True)
        legacy.write_bytes(b"")
        encoded.write_bytes(b"")
        self.bridge.feed_filename_max_v1_chunks.return_value = 5
        self.bridge.feed_filename_decode.side_effect = [b"inn", b"../escape"]
        self.assertEqual(feed_wire.discover_journal_peers(self.root, self.bridge),
                         ("inn", "../escape"))
        self.assertEqual(self.bridge.feed_filename_decode.call_args_list,
                         [mock.call((b"inn.fnfd",)),
                          mock.call((b"v1", b"2e2e2f657363617065", b"journal.fnfd"))])

    def test_discovery_preserves_empty_v1_namespace_as_fault(self):
        (Path(self.root) / "feed" / "v1").mkdir(parents=True)
        self.bridge.feed_filename_max_v1_chunks.return_value = 5
        with self.assertRaisesRegex(feed_wire.StoreFault, "empty FNFD v1 namespace"):
            feed_wire.discover_journal_peers(self.root, self.bridge)

    def test_failed_append_carries_uncertain_phase(self):
        journal = self.open()
        self.bridge.feed_journal_step.side_effect = ["write", "sync", "uncertain"]
        with mock.patch.object(feed_wire, "fsync_file", side_effect=OSError("sync")):
            with self.assertRaises(feed_wire.StoreIndeterminate):
                journal.append(b"frame")
        self.assertEqual(journal.phase, "uncertain")
        # It is the book that refuses the next phase, not a Python policy.
        self.bridge.feed_journal_step.side_effect = None
        self.bridge.feed_journal_step.return_value = "uncertain"
        with mock.patch.object(feed_wire, "write_all") as write:
            with self.assertRaises(feed_wire.StoreIndeterminate):
                journal.append(b"another")
            write.assert_not_called()


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
    """The client half: greeting, line reader, and exact ACL2 byte writes."""

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

    def test_acl2_rendered_block_crosses_the_socket_byte_for_byte(self):
        # The renderer's semantic witnesses live in tests/acl2/wire-tests.
        # Session has no framing branch left: it writes this vector exactly,
        # including a literal leading dot, a dot-only line, and two trailing
        # empty source lines that ACL2 rendered and terminated.
        rendered = (b"Subject: t\r\n\r\n..literal\r\n..\r\nbody\r\n"
                    b"\r\n\r\n.\r\n")
        listener, session = self.connected()
        session.send_block(rendered)
        listener.stop()
        self.assertEqual(listener.received, rendered)

    def test_a_response_line_over_the_bound_is_refused_and_leaks_nothing(self):
        listener = Listener(b"2" * (feed_wire.MAX_LINE + 10))
        self.addCleanup(listener.stop)
        with self.assertRaises(feed_wire.FeedError):
            feed_wire.Session("127.0.0.1", listener.port, 5.0)
        # and the socket it opened is closed: the constructor raised, so no
        # caller holds the object whose `close` would have been called.


if __name__ == "__main__":
    unittest.main()
