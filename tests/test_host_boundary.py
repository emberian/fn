"""Host boundary outcomes: barriers, exit codes, ownership and orphan reporting.

None of these tests start ACL2.  They exercise the adapter's own classification
and platform-primitive choices, which are the parts a live bridge cannot show.
"""
import errno
import fcntl
import io
import os
from pathlib import Path
import contextlib
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from tools import run_bp_ingress, run_bp_receive  # noqa: E402
from tools import receipt_journal, workflow_journal  # noqa: E402


class DurabilityBarrierTests(unittest.TestCase):
    """D12: one helper, and on darwin it is F_FULLFSYNC."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-barrier-")
        self.path = Path(self.temp.name) / "file"
        self.path.write_bytes(b"bytes")
        self.fd = os.open(self.path, os.O_RDONLY)
        self.addCleanup(os.close, self.fd)
        self.addCleanup(self.temp.cleanup)

    @unittest.skipUnless(sys.platform == "darwin", "F_FULLFSYNC is a darwin control")
    def test_darwin_barrier_asks_the_device_to_flush_its_cache(self):
        self.assertEqual(run_store.FULL_FSYNC, fcntl.F_FULLFSYNC)
        with mock.patch.object(run_store.fcntl, "fcntl") as full, \
             mock.patch.object(run_store.os, "fsync") as plain:
            run_store.durable_barrier(self.fd)
        full.assert_called_once_with(self.fd, fcntl.F_FULLFSYNC)
        plain.assert_not_called()

    @unittest.skipUnless(sys.platform == "darwin", "F_FULLFSYNC is a darwin control")
    def test_a_filesystem_that_rejects_full_fsync_falls_back_to_fsync(self):
        rejected = OSError(errno.ENOTSUP, "no device flush here")
        with mock.patch.object(run_store.fcntl, "fcntl", side_effect=rejected), \
             mock.patch.object(run_store.os, "fsync") as plain:
            run_store.durable_barrier(self.fd)
        plain.assert_called_once_with(self.fd)

    def test_an_unrelated_barrier_error_is_not_swallowed(self):
        refused = OSError(errno.EIO, "device error")
        with mock.patch.object(run_store.fcntl, "fcntl", side_effect=refused), \
             mock.patch.object(run_store.os, "fsync") as plain:
            if run_store.FULL_FSYNC is None:
                self.skipTest("no F_FULLFSYNC path on this platform")
            with self.assertRaises(OSError):
                run_store.durable_barrier(self.fd)
        plain.assert_not_called()

    def test_every_journal_barrier_goes_through_the_one_helper(self):
        self.assertIs(workflow_journal.durable_barrier, run_store.durable_barrier)
        self.assertIs(receipt_journal.durable_barrier, run_store.durable_barrier)
        with mock.patch.object(run_store, "durable_barrier") as barrier:
            run_store.fsync_file(self.fd)
            run_store.fsync_dir(Path(self.temp.name))
            run_store.fsync_regular(self.path)
        self.assertEqual(barrier.call_count, 3)


class ExitCodeTests(unittest.TestCase):
    """D13: uncertain, refused, accepted and fault never share a code."""

    def test_documented_table(self):
        table = {
            run_store.StoreIndeterminate("uncertain"): run_store.EXIT_UNCERTAIN,
            run_store.StoreFault("invalid state"): run_store.EXIT_FAULT,
            run_store.StoreError("known refusal"): run_store.EXIT_REFUSED,
            OSError(errno.EIO, "io fault"): run_store.EXIT_FAULT,
            UnicodeEncodeError("ascii", "é", 0, 1, "bad argument"):
                run_store.EXIT_USAGE,
        }
        for error, expected in table.items():
            with self.subTest(error=type(error).__name__):
                self.assertEqual(run_store.exit_code_for(error), expected)
        self.assertEqual(len({run_store.EXIT_OK, run_store.EXIT_REFUSED,
                              run_store.EXIT_UNCERTAIN, run_store.EXIT_FAULT,
                              run_store.EXIT_USAGE}), 5)

    def test_store_cli_maps_each_outcome_to_its_own_code(self):
        cases = ((run_store.StoreIndeterminate("u"), run_store.EXIT_UNCERTAIN),
                 (run_store.StoreFault("f"), run_store.EXIT_FAULT),
                 (run_store.StoreError("r"), run_store.EXIT_REFUSED),
                 (OSError(errno.EIO, "io"), run_store.EXIT_FAULT))
        for error, expected in cases:
            with self.subTest(error=type(error).__name__):
                with mock.patch.object(run_store, "command_status", side_effect=error):
                    with contextlib.redirect_stderr(io.StringIO()):
                        self.assertEqual(
                            run_store.main(["--store", "/nonexistent", "status"]), expected)

    def test_store_cli_usage_error_is_its_own_code(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                run_store.main(["--store", "/nonexistent", "no-such-command"])
        self.assertEqual(raised.exception.code, run_store.EXIT_USAGE)

    def test_pending_bpa_delete_is_reported_as_acceptance_not_failure(self):
        """A durable acceptance awaiting a delete keeps the accepted code."""
        pending = run_bp_ingress.BpDeletePending(
            "durably accepted ADU awaits BPA delete", "accepted", "bid-1", Path("/staged"))
        output = io.StringIO()
        arguments = ["--store", "s", "--journal", "j", "--workflow-journal", "w",
                     "--bid", "bid-1", "--inventory", "i", "--adu", "a",
                     "--bundle", "b", "--source-eid", "dtn://sender/"]
        with mock.patch.object(run_bp_ingress, "ingest_bpa_adu", side_effect=pending), \
             contextlib.redirect_stdout(output):
            self.assertEqual(run_bp_ingress.main(arguments), run_store.EXIT_OK)
        self.assertIn("accepted bid=bid-1", output.getvalue())
        self.assertIn("bpa-delete=pending", output.getvalue())

    def test_ingress_refusal_and_fault_stay_distinct(self):
        arguments = ["--store", "s", "--journal", "j", "--workflow-journal", "w",
                     "--bid", "bid-1", "--inventory", "i", "--adu", "a",
                     "--bundle", "b", "--source-eid", "dtn://sender/"]
        cases = ((run_bp_ingress.BpIngressError("capacity"), run_store.EXIT_REFUSED),
                 (run_store.StoreIndeterminate("uncertain"), run_store.EXIT_UNCERTAIN),
                 (run_store.StoreFault("invalid"), run_store.EXIT_FAULT))
        for error, expected in cases:
            with self.subTest(error=type(error).__name__):
                with mock.patch.object(run_bp_ingress, "ingest_bpa_adu", side_effect=error), \
                     contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(run_bp_ingress.main(arguments), expected)


class OwnershipAndOrphanTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-ownership-")
        self.path = Path(self.temp.name) / "store"
        self.addCleanup(self.temp.cleanup)

    def test_absent_lock_pathname_is_a_fault_not_a_held_lock(self):
        """An uninitialised store is an invalid state, never `already locked`."""
        self.path.mkdir()
        store = run_store.Store(self.path, writable=False)
        with self.assertRaises(run_store.StoreFault) as raised:
            store._open_lock(exclusive=False, create=False)
        self.assertNotIn("already locked", str(raised.exception))
        self.assertIn("writer lock", str(raised.exception))

    def test_a_contended_lock_is_still_a_clean_refusal(self):
        run_store.Store(self.path, writable=True).initialize()
        holder = run_store.Store(self.path, writable=True)
        holder.acquire()
        self.addCleanup(holder.close)
        contender = run_store.Store(self.path, writable=True)
        with self.assertRaisesRegex(run_store.StoreError, "already locked") as raised:
            contender.acquire()
        self.assertNotIsInstance(raised.exception, run_store.StoreFault)
        self.assertEqual(run_store.exit_code_for(raised.exception), run_store.EXIT_REFUSED)

    def test_initialization_publishes_metadata_through_staging(self):
        opened = []
        real_open = os.open

        def record_open(target, flags, mode=0o777):
            opened.append(Path(target))
            return real_open(target, flags, mode)

        with mock.patch("run_store.os.open", side_effect=record_open):
            run_store.Store(self.path, writable=True).initialize()
        created = [path for path in opened if path.parent == self.path / "staging"]
        # Three initial files go through staging: the config, the allocation
        # frontier, and (since R1) the generation-1 configuration record.
        self.assertEqual(len(created), 3)
        self.assertTrue((self.path / "config.json").is_file())
        self.assertTrue((self.path / "allocation-frontier.json").is_file())
        self.assertEqual(list((self.path / "staging").iterdir()), [])

    def test_recovery_reports_staging_orphans_without_deleting_them(self):
        run_store.Store(self.path, writable=True).initialize()
        store = run_store.Store(self.path, writable=True)
        orphan = self.path / "staging" / ".stage-1-abcdef"
        orphan.write_bytes(b"interrupted")
        self.assertEqual(store.staging_orphans(), (".stage-1-abcdef",))
        store.orphans = store.staging_orphans()
        self.assertIn(".stage-1-abcdef", run_store.orphan_report(store))
        self.assertTrue(orphan.exists())
        store.orphans = ()
        self.assertEqual(run_store.orphan_report(store), "staging-orphans=0")

    def test_orphan_report_stays_bounded(self):
        run_store.Store(self.path, writable=True).initialize()
        store = run_store.Store(self.path, writable=True)
        for number in range(run_store.MAX_STAGING_REPORT + 5):
            (self.path / "staging" / ".stage-{:04d}".format(number)).write_bytes(b"x")
        names = store.staging_orphans()
        self.assertEqual(len(names), run_store.MAX_STAGING_REPORT + 1)
        self.assertIn("...", names)


class ReceiverBoundaryTests(unittest.TestCase):
    def test_non_ascii_bid_is_refused_rather_than_raising_an_encoding_error(self):
        with self.assertRaises(run_bp_receive.BpReceiveError) as raised:
            run_bp_receive.receive_bpa_request(
                store_root="/nonexistent", inbox_root="/nonexistent",
                receipt_root="/nonexistent", bid="bid-é", inventory=list,
                download=lambda bid: b"", delete=lambda bid: None,
                bundle=lambda bid: b"", source_eid="dtn://sender/")
        self.assertNotIsInstance(raised.exception, UnicodeError)
        self.assertIn("BID", str(raised.exception))

    def test_over_long_and_empty_bids_refuse_the_same_way(self):
        for bid in ("", "b" * (run_bp_receive.MAX_BID_OCTETS + 1)):
            with self.subTest(bid=len(bid)):
                with self.assertRaises(run_bp_receive.BpReceiveError):
                    run_bp_receive.receive_bpa_request(
                        store_root="/nonexistent", inbox_root="/nonexistent",
                        receipt_root="/nonexistent", bid=bid, inventory=list,
                        download=lambda found: b"", delete=lambda found: None,
                        bundle=lambda found: b"", source_eid="dtn://sender/")


if __name__ == "__main__":
    unittest.main()
