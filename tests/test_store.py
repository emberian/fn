"""Real-directory tests for the experimental ACL2-backed transaction store."""
import contextlib
import errno
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from run_store import (Acl2Store, Store, StoreFault, StoreIndeterminate, frame,
                       unframe)  # noqa: E402


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

    def reserve_and_prepare(self, store, bridge, msgid, payload, groups,
                            obligation, subject, evidence, charge):
        """Drive the real allocator events before the composed prepare gate."""
        txid = bridge.next_txid()
        self.assertEqual(store.advance_frontier(bridge, txid), txid + 1)
        self.assertEqual(bridge.prepare(msgid, payload, groups, obligation,
                                        subject, evidence, charge), "prepared")
        return bridge.pending_record()

    def test_post_reopen_replays_and_preserves_literal_lisp_bytes(self):
        payload = b'Message-ID: <literal@example.invalid>\r\n\r\n#.(error "must not execute") \\ ()\r\n'
        self.post("<literal@example.invalid>", payload)
        status = self.invoke("status")
        self.assertIn(b"transactions=1 articles=1", status.stdout)
        inspected = self.invoke("inspect", "--message-id", "<literal@example.invalid>")
        self.assertEqual(inspected.stdout, payload)

    def test_acl2_transaction_names_continue_after_nonempty_recovery(self):
        """The second final name comes from ACL2 after replaying real history."""
        self.post("<name-zero@example.invalid>", b"zero")
        self.invoke("recover")
        self.post("<name-one@example.invalid>", b"one")
        names = sorted(path.name for path in (self.path / "transactions").iterdir())
        self.assertEqual(names, ["00000000000000000000.txn",
                                 "00000000000000000001.txn"])
        with self.recovered_bridge() as bridge:
            self.assertEqual(bridge.transaction_name(0), names[0])
            self.assertEqual(bridge.transaction_name(1), names[1])
            self.assertEqual(bridge.article_count(), 2)

    def test_empty_payload_is_present_and_orphan_staging_is_ignored(self):
        self.post("<empty@example.invalid>", b"")
        (self.path / "staging" / ".orphan").write_bytes(b"not a transaction")
        inspected = self.invoke("inspect", "--message-id", "<empty@example.invalid>")
        self.assertEqual(inspected.returncode, 0)
        self.assertEqual(inspected.stdout, b"")
        self.assertIn(b"transactions=1 articles=1", self.invoke("status").stdout)

    def test_metadata_frames_round_trip_and_reject_truncation(self):
        """P4: config and allocator are ACL2 FNSM frames, not JSON records."""
        config = (self.path / "config.json").read_bytes()
        frontier = (self.path / "allocation-frontier.json").read_bytes()
        self.assertTrue(config.startswith(b"FNSM\x01\x01"))
        self.assertTrue(frontier.startswith(b"FNSM\x01\x02"))
        self.invoke("recover")

        (self.path / "allocation-frontier.json").write_bytes(frontier[:-1])
        refused = self.invoke("recover", expected=run_store.EXIT_FAULT)
        self.assertIn(b"frontier frame", refused.stderr)

    def test_legacy_json_metadata_is_never_rewritten_on_open(self):
        """Format-5-looking metadata is retained for explicit offline migration."""
        legacy = b'{"format":"fn-store-experiment-5"}\n'
        path = self.path / "config.json"
        path.write_bytes(legacy)
        result = self.invoke("recover", expected=run_store.EXIT_FAULT)
        self.assertIn(b"explicit offline migration", result.stderr)
        self.assertEqual(path.read_bytes(), legacy)

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
        conflict = self.post("<same@example.invalid>", b"second",
                             expected=run_store.EXIT_REFUSED)
        self.assertIn(b"conflicting immutable Message-ID", conflict.stderr)
        inspected = self.invoke("inspect", "--message-id", "<same@example.invalid>")
        self.assertEqual(inspected.stdout, original)

    def test_duplicate_is_detected_before_full_transaction_limit(self):
        self.post("<bound-duplicate@example.invalid>", b"same")
        store = Store(self.path, writable=True)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            store.recover(bridge)
            store.config["max_transactions"] = 1
            self.assertEqual(bridge.existing_action(b"<bound-duplicate@example.invalid>",
                                                    b"same", [0]), "duplicate")
            self.assertEqual(len(store.transaction_files()), 1)
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def test_corruption_truncation_and_gap_fault_instead_of_prefix_recovery(self):
        self.post("<zero@example.invalid>", b"zero")
        transaction = self.path / "transactions" / "00000000000000000000.txn"
        transaction.write_bytes(transaction.read_bytes()[:-1])
        result = self.invoke("recover", expected=run_store.EXIT_FAULT)
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
        self.assertEqual(gap.returncode, run_store.EXIT_FAULT)
        self.assertIn(b"sequence gap", gap.stderr)

    def test_checksum_unknown_schema_and_final_symlink_fault(self):
        self.post("<flip@example.invalid>", b"flip")
        transaction = self.path / "transactions" / "00000000000000000000.txn"
        raw = bytearray(transaction.read_bytes())
        raw[-1] ^= 1
        transaction.write_bytes(raw)
        self.assertIn(b"integrity", self.invoke("recover", expected=run_store.EXIT_FAULT).stderr)

        other = Path(self.temp.name) / "unknown"
        subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "init"],
                       cwd=ROOT, check=True, stdout=subprocess.PIPE)
        (other / "transactions" / "00000000000000000000.txn").write_bytes(frame(b"unknown-schema"))
        unknown = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "recover"],
                                  cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(unknown.returncode, run_store.EXIT_FAULT)
        (other / "transactions" / "00000000000000000000.txn").unlink()
        os.symlink(other / "config.json", other / "transactions" / "00000000000000000000.txn")
        symlink = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "recover"],
                                  cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(symlink.returncode, run_store.EXIT_FAULT)
        self.assertIn(b"symlink", symlink.stderr)

    def test_known_abort_before_publication_and_indeterminate_after_publication(self):
        aborted = self.post("<abort@example.invalid>", b"abort", ("fn.letters",),
                            "--inject-fault", "prepublish",
                            expected=run_store.EXIT_REFUSED)
        self.assertIn(b"known abort", aborted.stderr)
        self.invoke("recover")
        self.assertEqual(list((self.path / "transactions").iterdir()), [])
        self.post("<after-abort@example.invalid>", b"after-abort")
        with self.recovered_bridge() as bridge:
            # The post after reopen uses txid 1, never the aborted txid 0.
            raw = (self.path / "transactions" / "00000000000000000000.txn").read_bytes()
            self.assertEqual(bridge.record_txid(unframe(raw)), 1)

        uncertain = self.post("<uncertain@example.invalid>", b"uncertain", ("fn.letters",),
                              "--inject-fault", "postpublish",
                              expected=run_store.EXIT_UNCERTAIN)
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
                               "--payload", self.payload, "--group", "fn.letters",
                               expected=run_store.EXIT_REFUSED)
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
            record = self.reserve_and_prepare(store, bridge, msgid, payload, [0],
                                              obligation, subject, evidence, 1)
            with mock.patch("run_store.os.link", side_effect=OSError(errno.EIO, "injected EIO")):
                with self.assertRaises(StoreIndeterminate):
                    store.publish(bridge, 0, record)
            self.assertTrue(store.fenced)
            self.assertEqual(bridge.prepare(b"<after@example.invalid>", b"after", [0],
                                            b"archive:after", b"sha256:after", evidence, 1),
                             "refused")
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

    def test_finish_rejects_stale_and_prepublication_states(self):
        store = Store(self.path, writable=True)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            store.recover(bridge)
            self.assertEqual(bridge.finish(), "fault")
            pending = self.reserve_and_prepare(
                store, bridge, b"<pending@example.invalid>", b"pending", [0],
                b"archive:pending", b"sha256:pending", b"unsigned-legacy-v0", 1)
            pending = bridge.pending_record()
            next_txid = bridge.next_txid()
            self.assertEqual(bridge.finish(), "fault")
            self.assertEqual(bridge.pending_record(), pending)
            self.assertEqual(bridge.next_txid(), next_txid)
            self.assertEqual(bridge.known_abort(), "aborted")
            self.assertEqual(bridge.next_txid(), next_txid)
            self.assertEqual(bridge.finish(), "fault")
            self.assertEqual(bridge.next_txid(), next_txid)
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

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

    def test_published_post_with_failed_core_reply_stays_fenced_and_recovers(self):
        for index, failure in enumerate(("rejected", "failed", "lost")):
            with self.subTest(failure=failure):
                message_id = "<completion-{}@example.invalid>".format(failure)
                payload = failure.encode("ascii")
                self.payload.write_bytes(payload)
                store, bridge, records = run_store.open_live_store(self.path, writable=True)
                real_finish = bridge.finish

                def finish():
                    if failure == "rejected":
                        return "fault"
                    if failure == "lost":
                        self.assertEqual(real_finish(), "durable")
                    raise run_store.StoreFault("injected core reply failure")

                args = SimpleNamespace(store=self.path, message_id=message_id, owner=None,
                                       payload=self.payload, group=["fn.letters"],
                                       charge=None, inject_fault=None)
                output = io.StringIO()
                with mock.patch("run_store.open_live_store", return_value=(store, bridge, records)), \
                     mock.patch.object(bridge, "finish", side_effect=finish), \
                     contextlib.redirect_stdout(output):
                    with self.assertRaises(StoreIndeterminate):
                        run_store.command_post(args)
                self.assertEqual(output.getvalue(), "")
                self.assertTrue(store.fenced)
                # Actual publication survives both a rejected completion and
                # a lost reply after the core completed. Recovery, not rollback,
                # reconciles the same retained article and obligation.
                with self.recovered_bridge() as recovered:
                    self.assertEqual(recovered.article_count(), index + 1)
                    self.assertEqual(recovered.pin_count(), index + 1)
                self.assertEqual(self.invoke("inspect", "--message-id", message_id).stdout,
                                 payload)

    def test_recovery_scan_io_failure_keeps_gate_closed_until_success(self):
        self.post("<scan@example.invalid>", b"retained")
        store, bridge, _ = run_store.open_live_store(self.path, writable=True)
        real_read = run_store.read_regular_bounded

        def fail_transaction_read(path, maximum):
            if Path(path).suffix == ".txn":
                raise OSError(errno.EIO, "injected transaction read failure")
            return real_read(path, maximum)

        try:
            self.assertFalse(store.fenced)
            with mock.patch("run_store.read_regular_bounded", side_effect=fail_transaction_read):
                with self.assertRaises(OSError):
                    store.recover(bridge)
            self.assertTrue(store.fenced)
            with self.assertRaises(StoreIndeterminate):
                store.advance_frontier(bridge, store.frontier)
            store.recover(bridge)
            self.assertFalse(store.fenced)
            self.assertEqual(bridge.article_count(), 1)
            self.assertEqual(bridge.pin_count(), 1)
        finally:
            bridge.close()
            store.close()

    def test_allocator_replace_error_and_frontier_replay_boundaries(self):
        store = Store(self.path, writable=True)
        bridge = None
        try:
            store.acquire()
            bridge = Acl2Store()
            store.recover(bridge)
            with mock.patch("run_store.os.replace", side_effect=OSError(errno.EIO, "replace")):
                with self.assertRaises(StoreIndeterminate):
                    store.advance_frontier(bridge, 0)
            self.assertTrue(store.fenced)
        finally:
            if bridge is not None:
                bridge.close()
            store.close()

        ahead = Store(self.path, writable=True)
        ahead.initialize()
        # Exercise the current ACL2-owned FNSM frontier grammar, not the
        # removed JSON/checksum implementation.
        from tools import frame_bridge
        contents = frame_bridge.session().metadata_frontier_frame(3)
        (self.path / "allocation-frontier.json").write_bytes(contents)
        bridge = None
        try:
            ahead.acquire()
            bridge = Acl2Store()
            ahead.recover(bridge)
            self.assertEqual(bridge.next_txid(), 3)
        finally:
            if bridge is not None:
                bridge.close()
            ahead.close()

        (self.path / "allocation-frontier.json").write_bytes(
            frame_bridge.session().metadata_frontier_frame(0))
        self.post("<frontier@example.invalid>", b"frontier")
        (self.path / "allocation-frontier.json").write_bytes(
            frame_bridge.session().metadata_frontier_frame(0))
        self.assertIn(b"rejected", self.invoke("recover", expected=run_store.EXIT_FAULT).stderr)

    def test_initialize_refuses_missing_frontier_when_history_exists(self):
        self.post("<history@example.invalid>", b"history")
        (self.path / "allocation-frontier.json").unlink()
        with self.assertRaises(StoreFault):
            Store(self.path, writable=True).initialize()

    def test_allocator_barrier_failure_recovers_observed_frontier_on_same_object(self):
        store, bridge, _ = run_store.open_live_store(self.path, writable=True)
        try:
            with mock.patch("run_store.fsync_dir", side_effect=OSError(errno.EIO, "allocator barrier")):
                with self.assertRaises(StoreIndeterminate):
                    store.advance_frontier(bridge, 0)
            self.assertTrue(store.fenced)
            self.assertEqual(store.frontier, 0)  # only the cached observation
            store.recover(bridge)
            self.assertFalse(store.fenced)
            self.assertEqual(store.frontier, 1)
            self.assertEqual(bridge.next_txid(), 1)

            record = self.reserve_and_prepare(
                store, bridge, b"<after-barrier@example.invalid>", b"kept", [0],
                b"archive:after-barrier", b"sha256:kept", b"unsigned-legacy-v0", 1)
            self.assertEqual(bridge.record_txid(record), 1)
            self.assertEqual(store.publish(bridge, 0, record), "durable")
            self.assertEqual(store.finish(bridge), "durable")
        finally:
            bridge.close()
            store.close()
        with self.recovered_bridge() as recovered:
            self.assertEqual(recovered.next_txid(), 2)
            self.assertEqual(recovered.article_count(), 1)
            self.assertEqual(recovered.pin_count(), 1)

    def test_failed_config_file_barrier_is_reestablished_during_recovery(self):
        path = Path(self.temp.name) / "init-barrier"
        initial = Store(path, writable=True)
        with mock.patch("run_store.fsync_file", side_effect=OSError(errno.EIO, "config barrier")):
            with self.assertRaises(OSError):
                initial.initialize()
        # Initialization publishes through staging, so a failed data barrier
        # leaves no final name at all: there is no torn config.json to make
        # the store permanently un-initialisable.
        self.assertFalse((path / "config.json").exists())
        self.assertTrue(list((path / "staging").iterdir()))
        # Retrying initialization under its writer lock publishes both files;
        # recovery below establishes the observed config name.
        initial.initialize()
        self.assertTrue((path / "config.json").is_file())

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
