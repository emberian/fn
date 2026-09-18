"""Isolated live-host checks for the fn-sn file/node composition.

These checks drive real temporary directories and the interpreted ACL2 wrapper.
They cover the adapter ordering; POSIX durability remains an explicit host
assumption rather than a claim made by these tests.
"""
import contextlib
import errno
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


class StoreNodeHostTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-sn-host-")
        self.root = Path(self.temporary.name) / "store"
        run_store.Store(self.root, writable=True).initialize()

    def tearDown(self):
        self.temporary.cleanup()

    def post(self, msgid, payload, fault=None):
        payload_path = Path(self.temporary.name) / "payload"
        payload_path.write_bytes(payload)
        return run_store.command_post(SimpleNamespace(
            store=self.root, message_id=msgid, payload=payload_path,
            group=["fn.letters", "fn.test"], charge=None, inject_fault=fault))

    @contextlib.contextmanager
    def live(self):
        store, bridge, records = run_store.open_live_store(self.root, writable=True)
        try:
            yield store, bridge, records
        finally:
            bridge.close()
            store.close()

    def test_lifecycle_uses_allocator_io_then_finish(self):
        self.assertEqual(self.post("<first@example.invalid>", b"first"), 0)
        self.assertEqual(self.post("<first@example.invalid>", b"first"), 0)
        with self.live() as (store, bridge, records):
            self.assertEqual(len(records), 1)
            self.assertEqual(bridge.article_count(), 1)
            self.assertEqual(bridge.next_txid(), 1)
            self.assertEqual(bridge.group_next(0), 2)
            self.assertEqual(bridge.group_next(1), 2)
            self.assertEqual(bridge.lookup(b"<first@example.invalid>"), b"first")
            self.assertFalse(store.fenced)

    def test_known_abort_consumes_frontier_without_a_record(self):
        with self.assertRaises(run_store.StoreError):
            self.post("<abort@example.invalid>", b"abort", "prepublish")
        with self.live() as (_store, bridge, records):
            self.assertEqual(records, [])
            self.assertEqual(bridge.article_count(), 0)
            self.assertEqual(bridge.next_txid(), 1)
        self.assertEqual(self.post("<after@example.invalid>", b"after"), 0)
        with self.live() as (_store, bridge, records):
            self.assertEqual(len(records), 1)
            self.assertEqual(bridge.record_txid(records[0]), 1)

    def test_link_failure_fences_then_observed_recovery_reopens(self):
        self.assertEqual(self.post("<prior@example.invalid>", b"prior"), 0)
        payload_path = Path(self.temporary.name) / "eio-payload"
        payload_path.write_bytes(b"eio")
        args = SimpleNamespace(store=self.root, message_id="<eio@example.invalid>",
                               payload=payload_path, group=["fn.letters"],
                               charge=None, inject_fault=None)
        with mock.patch("run_store.os.link", side_effect=OSError(errno.EIO, "link")):
            with self.assertRaises(run_store.StoreIndeterminate):
                run_store.command_post(args)
        with self.live() as (_store, bridge, records):
            self.assertEqual(len(records), 1)
            self.assertEqual(bridge.article_count(), 1)
            self.assertEqual(bridge.next_txid(), 2)
            self.assertFalse(bridge.lookup_found(b"<eio@example.invalid>"))

    def test_recovery_barrier_error_fences_until_fresh_observed_replay(self):
        self.assertEqual(self.post("<prior@example.invalid>", b"prior"), 0)
        store = run_store.Store(self.root, writable=True)
        bridge = None
        try:
            store.acquire()
            bridge = run_store.Acl2Store()
            real = run_store.fsync_dir

            def fail_root(path):
                if Path(path) == store.root:
                    raise OSError(errno.EIO, "recovery barrier")
                return real(path)

            with mock.patch("run_store.fsync_dir", side_effect=fail_root):
                with self.assertRaises(run_store.StoreIndeterminate):
                    store.recover(bridge)
            self.assertTrue(store.fenced)
        finally:
            if bridge is not None:
                bridge.close()
            store.close()
        with self.live() as (store, bridge, records):
            self.assertFalse(store.fenced)
            self.assertEqual(len(records), 1)
            self.assertEqual(bridge.article_count(), 1)

    def test_finish_rejects_stale_ready_state(self):
        bridge = run_store.Acl2Store()
        try:
            self.assertEqual(bridge.finish(), "fault")
            self.assertEqual(bridge.article_count(), 0)
            self.assertEqual(bridge.next_txid(), 0)
        finally:
            bridge.close()

    def prepare_record(self, store, bridge, records, label):
        txid = bridge.next_txid()
        self.assertEqual(store.advance_frontier(bridge, txid), txid + 1)
        msgid = ("<{}@example.invalid>".format(label)).encode("ascii")
        obligation = ("archive:{}".format(label)).encode("ascii")
        subject = ("sha256:{}".format(label)).encode("ascii")
        self.assertEqual(bridge.prepare(
            msgid, label.encode("ascii"), [0],
            obligation, subject, b"unsigned-legacy-v0", 1), "prepared")
        return bridge.pending_record()

    def test_lost_directory_reply_cannot_retry_finish_before_recovery(self):
        with self.live() as (store, bridge, records):
            record = self.prepare_record(store, bridge, records, "lost-directory")
            original = run_store.Acl2Store.io

            def lose_directory(observed, result="ok"):
                value = original(bridge, observed, result)
                if observed == "record-directory" and result == "ok":
                    raise run_store.StoreError("injected lost directory reply")
                return value

            with mock.patch("run_store.Acl2Store.io", side_effect=lose_directory):
                with self.assertRaises(run_store.StoreIndeterminate):
                    store.publish(bridge, len(records), record)
            self.assertTrue(store.fenced)
            self.assertFalse(store.completion_pending)
            with mock.patch.object(bridge, "finish", side_effect=AssertionError("must not call core")) as finish:
                with self.assertRaises(run_store.StoreIndeterminate):
                    store.finish(bridge)
                finish.assert_not_called()
            store.recover(bridge)
            self.assertFalse(store.fenced)
            expected_frontier = store.frontier + 1
            self.assertEqual(store.advance_frontier(bridge, bridge.next_txid()), expected_frontier)

    def test_failed_or_lost_finish_cannot_retry_before_recovery(self):
        for outcome in ("rejected", "lost"):
            with self.subTest(outcome=outcome), self.live() as (store, bridge, records):
                record = self.prepare_record(store, bridge, records, "finish-" + outcome)
                self.assertEqual(store.publish(bridge, len(records), record), "durable")
                self.assertTrue(store.completion_pending)
                actual_finish = bridge.finish

                def fail_finish():
                    if outcome == "lost":
                        self.assertEqual(actual_finish(), "durable")
                        raise run_store.StoreError("injected lost finish reply")
                    return "fault"

                with mock.patch.object(bridge, "finish", side_effect=fail_finish):
                    with self.assertRaises(run_store.StoreIndeterminate):
                        store.finish(bridge)
                self.assertTrue(store.fenced)
                self.assertFalse(store.completion_pending)
                with mock.patch.object(bridge, "finish", side_effect=AssertionError("must not retry core")) as finish:
                    with self.assertRaises(run_store.StoreIndeterminate):
                        store.finish(bridge)
                    finish.assert_not_called()
                store.recover(bridge)
                self.assertFalse(store.fenced)
                expected_frontier = store.frontier + 1
                self.assertEqual(store.advance_frontier(bridge, bridge.next_txid()), expected_frontier)

    def test_lost_bridge_reply_after_namespace_observation_stays_fenced(self):
        """The host closes its gate before every post-syscall callback."""
        self.assertEqual(self.post("<prior@example.invalid>", b"prior"), 0)
        for operation in ("start-frontier", "frontier-file", "frontier-replace",
                          "frontier-directory", "record-file", "record-link",
                          "record-directory"):
            with self.subTest(operation=operation):
                with self.live() as (store, bridge, records):
                    if operation.startswith("record"):
                        txid = bridge.next_txid()
                        store.advance_frontier(bridge, txid)
                        msgid = ("<lost-{}@example.invalid>".format(operation)).encode("ascii")
                        obligation = ("archive:lost-{}".format(operation)).encode("ascii")
                        subject = ("sha256:lost-{}".format(operation)).encode("ascii")
                        self.assertEqual(bridge.prepare(
                            msgid, b"lost", [0],
                            obligation, subject, b"unsigned-legacy-v0", 1),
                            "prepared")
                        invoke = lambda: store.publish(bridge, len(records), bridge.pending_record())
                    else:
                        invoke = lambda: store.advance_frontier(bridge, bridge.next_txid())
                    original = run_store.Acl2Store.io

                    def lost_reply(observed, result="ok"):
                        value = original(bridge, observed, result)
                        if observed == operation and result == "ok":
                            raise run_store.StoreError("injected lost bridge reply")
                        return value

                    with mock.patch("run_store.Acl2Store.io", side_effect=lost_reply):
                        with self.assertRaises(run_store.StoreError):
                            invoke()
                    self.assertTrue(store.fenced)
                    self.assertFalse(store.completion_pending)


if __name__ == "__main__":
    unittest.main()
