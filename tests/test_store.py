"""Real-directory tests for the experimental ACL2-backed transaction store."""
import contextlib
import errno
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from run_store import Acl2Store, Store, StoreFault, StoreIndeterminate, unframe  # noqa: E402


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-store-test-")
        self.path = Path(self.temp.name) / "store"
        self.payload = Path(self.temp.name) / "payload"
        self.invoke("init")

    def tearDown(self):
        self.temp.cleanup()

    def invoke(self, command, *args, expected=0):
        result = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(self.path),
                                 command, *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, check=False)
        if result.returncode != expected:
            self.fail("{} returned {}\nstdout={}\nstderr={}".format(
                command, result.returncode, result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result

    def post(self, msgid, data, groups=("fn.letters",), *extra, expected=0):
        self.payload.write_bytes(data)
        arguments = ["--message-id", msgid, "--payload", self.payload]
        for group in groups:
            arguments.extend(["--group", group])
        arguments.extend(extra)
        return self.invoke("post", *arguments, expected=expected)

    @contextlib.contextmanager
    def recovered_bridge(self):
        store = Store(self.path, writable=False)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            store.recover(bridge)
            yield bridge
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def test_post_reopen_replays_and_preserves_literal_lisp_bytes(self):
        payload = b'Message-ID: <literal@example.invalid>\r\n\r\n#.(error "must not execute") \\ ()\r\n'
        self.post("<literal@example.invalid>", payload)
        status = self.invoke("status")
        self.assertIn(b"transactions=1 articles=1", status.stdout)
        inspected = self.invoke("inspect", "--message-id", "<literal@example.invalid>")
        self.assertEqual(inspected.stdout, payload)

    def test_two_group_post_replays_both_allocations_and_one_pin(self):
        self.post("<two@example.invalid>", b"two", ("fn.letters", "fn.test"))
        with self.recovered_bridge() as bridge:
            self.assertEqual(bridge.article_count(), 1)
            self.assertEqual(bridge.group_next(0), 2)
            self.assertEqual(bridge.group_next(1), 2)
            self.assertEqual(bridge.pin_count(), 1)
            self.assertEqual(bridge.reserved(), 2)

    def test_duplicate_retry_and_conflicting_id_do_not_overwrite(self):
        original = b"first"
        self.post("<same@example.invalid>", original)
        duplicate = self.post("<same@example.invalid>", original)
        self.assertEqual(duplicate.stdout.strip(), b"duplicate")
        conflict = self.post("<same@example.invalid>", b"second", expected=2)
        self.assertIn(b"conflicting immutable Message-ID", conflict.stderr)
        inspected = self.invoke("inspect", "--message-id", "<same@example.invalid>")
        self.assertEqual(inspected.stdout, original)

    def test_corruption_truncation_and_gap_fault_instead_of_prefix_recovery(self):
        self.post("<zero@example.invalid>", b"zero")
        transaction = self.path / "transactions" / "00000000000000000000.txn"
        transaction.write_bytes(transaction.read_bytes()[:-1])
        result = self.invoke("recover", expected=2)
        self.assertIn(b"truncated", result.stderr)

        # A fresh store exercises a namespace gap independently of framing.
        other = Path(self.temp.name) / "gap"
        subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "init"],
                       cwd=ROOT, check=True, stdout=subprocess.PIPE)
        source = other / "transactions" / "00000000000000000000.txn"
        source.write_bytes(b"FNST\x01\x00\x00\x00\x00" + b"x" * 32)
        os.link(source, other / "transactions" / "00000000000000000001.txn")
        source.unlink()
        gap = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "recover"],
                             cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(gap.returncode, 2)
        self.assertIn(b"sequence gap", gap.stderr)

    def test_known_abort_before_publication_and_indeterminate_after_publication(self):
        aborted = self.post("<abort@example.invalid>", b"abort", ("fn.letters",),
                            "--inject-fault", "prepublish", expected=2)
        self.assertIn(b"known abort", aborted.stderr)
        self.invoke("recover")
        self.assertEqual(list((self.path / "transactions").iterdir()), [])
        self.post("<after-abort@example.invalid>", b"after-abort")
        with self.recovered_bridge() as bridge:
            # The post after reopen uses txid 1, never the aborted txid 0.
            raw = (self.path / "transactions" / "00000000000000000000.txn").read_bytes()
            self.assertEqual(bridge.record_txid(unframe(raw, 32768)), 1)

        uncertain = self.post("<uncertain@example.invalid>", b"uncertain", ("fn.letters",),
                              "--inject-fault", "postpublish", expected=2)
        self.assertIn(b"indeterminate", uncertain.stderr)
        # A complete but unacknowledged final file may survive; reopening does
        # exact decode, replay, and directory barriers before becoming usable.
        recovered = self.invoke("recover")
        self.assertIn(b"transactions=2 articles=2", recovered.stdout)

    def test_writer_lock_refuses_concurrent_mutator(self):
        holder = Store(self.path, writable=True)
        holder.acquire()
        try:
            self.payload.write_bytes(b"locked")
            refused = self.invoke("post", "--message-id", "<lock@example.invalid>",
                               "--payload", self.payload, "--group", "fn.letters", expected=2)
            self.assertIn(b"already locked", refused.stderr)
        finally:
            holder.close()

    def test_link_eio_without_visible_final_fences_host_and_core(self):
        store = Store(self.path, writable=True)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            store.recover(bridge)
            msgid, payload = b"<eio@example.invalid>", b"eio"
            obligation = b"archive:eio"
            subject = b"sha256:eio"
            evidence = b"unsigned-legacy-v0"
            self.assertEqual(bridge.prepare(msgid, payload, [0], obligation, subject, evidence, 1),
                             "prepared")
            with mock.patch("run_store.os.link", side_effect=OSError(errno.EIO, "injected EIO")):
                with self.assertRaises(StoreIndeterminate):
                    store.publish(0, bridge.pending_record())
            self.assertTrue(store.fenced)
            self.assertEqual(bridge.complete("indeterminate"), "indeterminate")
            self.assertEqual(bridge.prepare(b"<after@example.invalid>", b"after", [0],
                                            b"archive:after", b"sha256:after", evidence, 1),
                             "refused")
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def test_rejected_completion_keeps_pending_metadata_and_allocation(self):
        bridge = Acl2Store()
        try:
            self.assertEqual(bridge.prepare(b"<pending@example.invalid>", b"pending", [0],
                                            b"archive:pending", b"sha256:pending",
                                            b"unsigned-legacy-v0", 1), "prepared")
            pending = bridge.pending_record()
            next_txid = bridge.next_txid()
            self.assertEqual(bridge.complete("unexpected"), "fault")
            self.assertEqual(bridge.pending_record(), pending)
            self.assertEqual(bridge.next_txid(), next_txid)
            self.assertEqual(bridge.complete("aborted"), "aborted")
            self.assertEqual(bridge.next_txid(), next_txid)
            # A stale completion cannot be echoed as another durable event.
            self.assertEqual(bridge.complete("durable"), "fault")
            self.assertEqual(bridge.next_txid(), next_txid)
        finally:
            bridge.close()

    def test_recovery_limits_and_barrier_failure_fence_until_success(self):
        self.post("<limit@example.invalid>", b"limit")
        store = Store(self.path, writable=True)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            store.config["max_transactions"] = 0
            with self.assertRaises(StoreFault):
                store.transaction_files()
            store.config["max_transactions"] = 128
            store.config["max_recovery_record_bytes"] = 0
            with self.assertRaises(StoreFault):
                store.durable_records(bridge)
            store.config["max_recovery_record_bytes"] = 128 * 32768
            with mock.patch("run_store.fsync_dir", side_effect=OSError(errno.EIO, "barrier")):
                with self.assertRaises(StoreIndeterminate):
                    store.recover(bridge)
            self.assertTrue(store.fenced)
            store.recover(bridge)
            self.assertFalse(store.fenced)
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def test_failed_config_file_barrier_is_reestablished_during_recovery(self):
        path = Path(self.temp.name) / "init-barrier"
        initial = Store(path, writable=True)
        with mock.patch("run_store.fsync_file", side_effect=OSError(errno.EIO, "config barrier")):
            with self.assertRaises(OSError):
                initial.initialize()
        self.assertTrue((path / "config.json").is_file())
        # Retrying initialization under its writer lock completes the missing
        # allocator file; recovery below establishes the observed config name.
        initial.initialize()

        store = Store(path, writable=True)
        bridge = None
        calls = []
        real_file_barrier, real_dir_barrier = run_store.fsync_regular, run_store.fsync_dir
        try:
            store.acquire()
            bridge = Acl2Store()
            with mock.patch("run_store.fsync_regular", side_effect=lambda target: (
                    calls.append(("file", Path(target).name)), real_file_barrier(target))[1]), \
                 mock.patch("run_store.fsync_dir", side_effect=lambda target: (
                    calls.append(("dir", Path(target).name)), real_dir_barrier(target))[1]):
                store.recover(bridge)
            self.assertEqual(calls[0], ("file", "config.json"))
            self.assertEqual(calls[-1], ("dir", path.parent.name))
            self.assertFalse(store.fenced)
        finally:
            if bridge is not None:
                bridge.close()
            store.close()


if __name__ == "__main__":
    unittest.main()
