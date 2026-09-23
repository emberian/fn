"""FNFD physical recovery against the actual ACL2 scanner, one ACL2 image.

The small bridge omits the server books but executes the exact scanner and
existing feed replay fold. It inherits the production envelope/phase methods.
These tests cover file/process I/O, not the composed NNTP acceptance machine.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import run_store
from run_owner import Acl2Owner, acl2_octet_list
from feed_wire import Journal
import feed_wire


class BookBridge(Acl2Owner):
    def __init__(self, peer=b"inn"):
        self.proc = None
        self.poisoned = False
        self.peer = peer
        env = dict(os.environ, ACL2_CUSTOMIZATION="NONE", ACL2_BOOK_HASH_ALISTP="NIL")
        self.proc = subprocess.Popen([env.get("FN_ACL2", "acl2")], cwd=ROOT,
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, env=env)
        run_store.read_prompt(self.proc, run_store.ACL2_START_TIMEOUT_SECONDS)
        self.call('(include-book "books/feed-journal")')
        self.call('(ld "host/feed-filename-host.lisp" :ld-error-action :return :ld-error-triples t)')

    def feed_journal_begin(self):
        super().feed_journal_begin()
        self.call("(f-put-global 'fn-test-feed "
                  "(fn-feed-open '{} (fn-feed-limits 100 1000 3 t) "
                  "(fn-sched-contact \"inn\" 0 1000000) nil) state)".format(
                      self.literal(self.peer)))

    def feed_journal_scan(self, peer, prefix, frame):
        self.call("(f-put-global 'fn-test-scan "
                  "(fn-feed-journal-scan '{} '{} '{} "
                  "(@ fn-owner-feed-safe-offset)) state)".format(
                      self.literal(peer), self.literal(prefix), self.literal(frame)))
        status = self._symbol_any("(car (@ fn-test-scan))")
        if status == "next":
            self.call("(f-put-global 'fn-owner-feed-safe-offset "
                      "(cadr (@ fn-test-scan)) state)")
            self.call("(f-put-global 'fn-test-feed "
                      "(fn-feed-replay (@ fn-test-feed) "
                      "(list (caddr (@ fn-test-scan)))) state)")
        return status

    def frame(self, kind="feed-enqueue", values="((105 110 110) (60 97 64 102 110 62) 7)"):
        form = "(let* ((values '{})(payload (fn-frame-fields-octets " \
               "(fn-frame-spec-for :{} *fn-feed-specs*) values))) " \
               "(fn-frame-seal *fn-feed-magic* *fn-frame-version* " \
               "(fn-frame-enum-index :{} *fn-feed-kinds*) payload))"
        return bytes(acl2_octet_list(self.call(form.format(values, kind, kind))))

    def inspect_file(self, path, msgid):
        """Read an at-rest FNFD through the same ACL2 scanner/replay as recovery.

        Python only supplies bounded file reads of the prefix length ACL2
        returns.  The record kind, queue state and attempt count all come
        from the book, so this is an observation of the model's projection
        of durable bytes rather than a second FNFD parser.
        """
        self.feed_journal_begin()
        if self._symbol_any("(fn-feedp (@ fn-test-feed))") != "t":
            raise AssertionError("ACL2 inspector initial feed is invalid")
        counts = {}
        prefix_size = self._nat("*fn-feed-journal-prefix-size*")
        with Path(path).open("rb") as source:
            while True:
                prefix = source.read(prefix_size)
                if not prefix:
                    break
                plan = self.feed_journal_prefix(list(prefix))
                if not isinstance(plan, int):
                    raise AssertionError("ACL2 refused FNFD prefix: {}".format(plan))
                frame = source.read(plan)
                if len(frame) != plan:
                    raise AssertionError("short FNFD frame")
                state = self.feed_journal_scan(list(self.peer), list(prefix), list(frame))
                if state != "next":
                    raise AssertionError("ACL2 refused FNFD frame: {}".format(state))
                if self._symbol_any("(fn-feedp (@ fn-test-feed))") != "t":
                    raise AssertionError("ACL2 replay left the feed recognizer")
                kind = self._symbol_any(
                    "(fn-feed-journal-kind (caddr (@ fn-test-scan)))")
                counts[kind] = counts.get(kind, 0) + 1
        mid = self.literal(list(msgid.encode("ascii")))
        before = self._symbol_any(
            "(fn-feed-state-of '{} (fn-feed-queue (@ fn-test-feed)))".format(mid))
        self.call("(f-put-global 'fn-test-feed "
                  "(fn-feed-restart (@ fn-test-feed)) state)")
        after = self._symbol_any(
            "(fn-feed-state-of '{} (fn-feed-queue (@ fn-test-feed)))".format(mid))
        return {"records": counts, "state_before_restart": before,
                "state_after_restart": after,
                "queue_length": self._nat("(len (fn-feed-queue (@ fn-test-feed)))"),
                "attempts": self._nat(
                    "(fn-feed-entry-attempts "
                    "(fn-feed-find '{} (fn-feed-queue (@ fn-test-feed))))".format(mid)),
                "next_attempt": self._nat("(fn-feed-next-attempt (@ fn-test-feed))"),
                "inflight": self._symbol_any(
                    "(fn-feed-inflightp '{} (@ fn-test-feed))".format(mid))}


class FeedJournalLiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bridge = BookBridge()
        cls.frame = cls.bridge.frame()
        cls.envelope = cls.bridge.feed_journal_wrap(cls.frame)
        cls.restart = cls.bridge.frame("feed-restart", "((105 110 110))")
        cls.restart_envelope = cls.bridge.feed_journal_wrap(cls.restart)

    @classmethod
    def tearDownClass(cls):
        cls.bridge.close()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-feed-real-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / "feed" / "inn.fnfd"
        self.path.parent.mkdir()

    def open(self, faults=run_store.NO_FAULTS):
        journal = Journal(str(self.root), b"inn", self.bridge, faults=faults)
        self.addCleanup(journal.close)
        return journal

    def test_every_torn_prefix_and_body_repairs_then_appends_then_restarts(self):
        for cut in range(1, len(self.restart_envelope)):
            with self.subTest(cut=cut):
                self.path.write_bytes(self.envelope + self.restart_envelope[:cut])
                journal = self.open()
                self.assertEqual(journal.replayed, 1)
                self.assertEqual(self.path.read_bytes(), self.envelope)
                journal.append(self.restart)
                journal.close()
                reopened = self.open()
                self.assertEqual(reopened.replayed, 2)
                self.assertEqual(self.path.read_bytes(), self.envelope + self.restart_envelope)
                self.assertEqual(self.bridge._nat("(len (fn-feed-queue (@ fn-test-feed)))"), 1)
                reopened.close()

    def test_traversal_shaped_peer_uses_acl2_v1_components(self):
        peer = b"../escape"
        journal = Journal(str(self.root), peer, self.bridge)
        self.addCleanup(journal.close)
        self.assertEqual(Path(journal.path).relative_to(self.root / "feed"),
                         Path("v1") / "2e2e2f657363617065" / "journal.fnfd")
        self.assertNotIn("..", Path(journal.path).parts)

    def test_complete_invalid_digest_length_schema_and_peer_preserve_evidence(self):
        corrupted = bytearray(self.envelope)
        corrupted[-1] ^= 1
        wrong = self.bridge.frame("feed-restart", "((98))")
        # Well-integrity-framed but outside the FNFD kind grammar. ACL2
        # builds both layers of this deliberately invalid evidence fixture.
        bad_schema = bytes(acl2_octet_list(self.bridge.call(
            "(let ((f (fn-frame-seal *fn-feed-magic* *fn-frame-version* 255 nil))) "
            "(append (fn-cbor-u32-bytes (len f)) f))")))
        for bad in (bytes(corrupted), b"\xff\xff\xff\xff", b"\0\0\0\0",
                    self.bridge.feed_journal_wrap(wrong), bad_schema):
            with self.subTest(bad=bad.hex()):
                original = self.envelope + bad
                self.path.write_bytes(original)
                with self.assertRaises(run_store.StoreFault):
                    self.open()
                self.assertEqual(self.path.read_bytes(), original)

    def test_short_reads_are_accumulated_until_real_eof(self):
        self.path.write_bytes(self.envelope + self.restart_envelope)
        read = os.read
        with mock.patch.object(feed_wire.os, "read", side_effect=lambda fd, size: read(fd, 1)):
            journal = self.open()
        self.assertEqual(journal.replayed, 2)
        self.assertEqual(self.path.read_bytes(), self.envelope + self.restart_envelope)

    def test_read_only_inspector_reports_replayed_queue_from_real_fnfd_bytes(self):
        self.path.write_bytes(self.envelope)
        original = self.path.read_bytes()
        observed = self.bridge.inspect_file(self.path, "<a@fn>")
        self.assertEqual(observed["records"], {"feed-enqueue": 1})
        self.assertEqual(observed["state_before_restart"], "queued")
        self.assertEqual(observed["state_after_restart"], "queued")
        self.assertEqual(observed["queue_length"], 1)
        self.assertEqual(self.path.read_bytes(), original)

    def test_each_recovery_barrier_failure_requires_a_fresh_successful_recovery(self):
        for name, effects in (("fsync_file", [OSError("content")]),
                              ("fsync_dir", [OSError("directory")]),
                              ("fsync_dir", [None, OSError("parent")])):
            with self.subTest(name=name, effects=effects):
                self.path.write_bytes(self.envelope + self.restart_envelope[:7])
                with mock.patch.object(feed_wire, name, side_effect=effects):
                    with self.assertRaises(run_store.StoreIndeterminate):
                        self.open()
                recovered = self.open()
                recovered.append(self.restart)
                recovered.close()
                self.assertEqual(self.path.read_bytes(), self.envelope + self.restart_envelope)

    def test_real_model_fence_survives_a_second_append_after_sync_failure(self):
        journal = self.open()
        with mock.patch.object(feed_wire, "fsync_file", side_effect=OSError("content")):
            with self.assertRaises(run_store.StoreIndeterminate):
                journal.append(self.frame)
        original = self.path.read_bytes()
        with self.assertRaises(run_store.StoreIndeterminate):
            journal.append(self.restart)
        self.assertEqual(self.path.read_bytes(), original)
        journal.close()
        reopened = self.open()
        self.assertEqual(reopened.replayed, 1)
        reopened.append(self.restart)

    def test_process_death_at_each_named_recovery_and_append_cut(self):
        # The child is the I/O host; the parent owns the single ACL2 oracle.
        # No concurrent calls: parent waits before issuing another query.
        events = ("opened", "end", "repair", "truncated", "content-durable",
                  "directory-durable", "parent-durable", "append", "written",
                  "append-durable")
        for event in events:
            with self.subTest(event=event):
                suffix = b"" if event == "end" else self.restart_envelope[:7]
                self.path.write_bytes(self.envelope + suffix)
                pid = os.fork()
                if pid == 0:
                    fault = run_store.ScriptedFaults("feed-journal:" + event, exit_code=73)
                    try:
                        journal = Journal(str(self.root), b"inn", self.bridge, faults=fault)
                        journal.append(self.restart)
                        os._exit(74)
                    except BaseException:
                        os._exit(75)
                _, status = os.waitpid(pid, 0)
                self.assertEqual(os.waitstatus_to_exitcode(status), 73)
                recovered = self.open()
                self.assertIn(recovered.replayed, (1, 2))
                recovered.append(self.restart)
                recovered.close()
                again = self.open()
                self.assertIn(again.replayed, (2, 3))
                again.close()


if __name__ == "__main__":
    unittest.main()
