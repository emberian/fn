"""Adversarial real-directory checks for the provisional BP workflow host.

These tests exercise only adapter boundaries.  They never reconstruct BP state
in Python; the replay callback records what the host passes to the ACL2 bridge.
"""

from __future__ import annotations

import tempfile
import unittest
import multiprocessing
import os
from pathlib import Path
from unittest import mock

from tools.workflow_journal import (InboundDeletePending, JournalError,
                                    JournalFault, JournalUncertain, WorkflowJournal,
                                    decode_inbound, encode_inbound)
from tools.run_store import Acl2Store
from tools.workflow_bridge import Acl2WorkflowReplay

# Opaque to this journal; ACL2 derives it from the bundle's primary block.
IDENTITY = b"\x83\x82\x01\x65//n1/\x18\x64\x01"



CONFIG = {"local-eid": "dtn://local/", "peer-eid": "dtn://peer/",
          "policy-id": "policy:local:1", "receipt-authority": "dtn://peer/",
          "bp-lifetime": 3600, "incarnation": "incarnation:1",
          "authorization-context": "authorization:1"}


def crash_after_inbound_link(root: str) -> None:
    """Process-cut helper: terminate after link and before the directory barrier."""
    journal = WorkflowJournal(Path(root), lambda records: records)
    journal.open()
    with mock.patch("tools.workflow_journal.fsync_dir", side_effect=lambda path: os._exit(93)):
        journal.stage_inbound("bid-crash", IDENTITY, lambda: ["bid-crash"],
                              lambda bid: b"crash-payload", lambda bid: None)


class WorkflowFaultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="fn-workflow-fault-")
        self.root = Path(self.temp.name) / "workflow"

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_open_barrier_failure_fences_and_releases_exclusive_lock(self) -> None:
        """A failed recovery never leaves a live owner behind."""
        failed = WorkflowJournal(self.root, lambda records: records)
        with mock.patch("tools.workflow_journal.fsync_dir", side_effect=OSError("barrier")):
            with self.assertRaises(JournalFault):
                failed.open()
        self.assertTrue(failed.fenced)
        self.assertIsNone(failed.lock_fd)

        recovered = WorkflowJournal(self.root, lambda records: records)
        self.assertEqual(recovered.open(), ())
        recovered.close()

    def test_exact_inbound_retry_after_delete_failure_is_idempotent(self) -> None:
        """Once staging succeeds, a lost BPA-delete result must be idempotent."""
        journal = WorkflowJournal(self.root, lambda records: records)
        journal.open()
        downloads: list[str] = []
        deletes: list[str] = []

        def download(bid: str) -> bytes:
            downloads.append(bid)
            return b"opaque-bundle"

        def delete_after_effect(bid: str) -> None:
            deletes.append(bid)
            raise OSError("delete completion lost")

        with self.assertRaises(InboundDeletePending):
            journal.stage_inbound("bid-1", IDENTITY, lambda: ["bid-1"], download,
                                  delete_after_effect)

        retry = journal.retry_staged_delete("bid-1", IDENTITY, lambda: ["bid-1"],
                                            lambda bid: deletes.append(bid))
        self.assertTrue(retry.exists())
        self.assertEqual(decode_inbound(retry.read_bytes()), ("bid-1", IDENTITY, b"opaque-bundle"))
        self.assertEqual(downloads, ["bid-1"])
        self.assertEqual(deletes, ["bid-1", "bid-1"])
        journal.close()

    def test_conflicting_retry_for_a_durable_bid_fences_without_deleting(self) -> None:
        journal = WorkflowJournal(self.root, lambda records: records)
        journal.open()
        deleted = []
        with self.assertRaises(InboundDeletePending):
            journal.stage_inbound("bid-conflict", IDENTITY, lambda: ["bid-conflict"],
                                  lambda bid: b"first", 
                                  lambda bid: (_ for _ in ()).throw(OSError("lost delete")))
        with self.assertRaisesRegex(JournalFault, "conflicting"):
            journal.stage_inbound("bid-conflict", IDENTITY, lambda: ["bid-conflict"],
                                  lambda bid: b"different", deleted.append)
        self.assertTrue(journal.fenced)
        self.assertEqual(deleted, [])
        journal.close()

    def test_inbound_directory_barrier_after_link_fences_and_reopens(self) -> None:
        journal = WorkflowJournal(self.root, lambda records: records)
        journal.open()
        deleted = []
        with mock.patch("tools.workflow_journal.fsync_dir", side_effect=OSError("inbound barrier")):
            with self.assertRaises(JournalUncertain):
                journal.stage_inbound("bid-link", IDENTITY, lambda: ["bid-link"],
                                      lambda bid: b"linked", deleted.append)
        self.assertTrue(journal.fenced)
        self.assertEqual(deleted, [])
        journal.close()

        reopened = WorkflowJournal(self.root, lambda records: records)
        reopened.open()
        self.assertEqual([(bid, decode_inbound(path.read_bytes()))
                          for bid, _identity, path in reopened.inbound_items],
                         [("bid-link", ("bid-link", b"linked"))])
        reopened.close()

    def test_recovery_callback_failure_fences_and_releases_exclusive_lock(self) -> None:
        failed = WorkflowJournal(self.root,
                                 lambda records: (_ for _ in ()).throw(ValueError("bridge")))
        with self.assertRaises(JournalFault):
            failed.open()
        self.assertTrue(failed.fenced)
        self.assertIsNone(failed.lock_fd)
        recovered = WorkflowJournal(self.root, lambda records: "recovered")
        self.assertEqual(recovered.open(), "recovered")
        recovered.close()

    def test_restart_rediscovers_the_exact_durable_inbox_frame(self) -> None:
        journal = WorkflowJournal(self.root, lambda records: records)
        journal.open()
        with self.assertRaises(InboundDeletePending):
            journal.stage_inbound("bid-restart", IDENTITY, lambda: ["bid-restart"],
                                  lambda bid: b"restart-payload",
                                  lambda bid: (_ for _ in ()).throw(OSError("lost delete")))
        journal.close()

        replayed = []
        reopened = WorkflowJournal(self.root,
                                   lambda records: replayed.append(records) or "reopened")
        self.assertEqual(reopened.open(), "reopened")
        self.assertEqual(replayed, [()])
        self.assertEqual(len(reopened.inbound_items), 1)
        bid, _identity, path = reopened.inbound_items[0]
        self.assertEqual((bid, decode_inbound(path.read_bytes())),
                         ("bid-restart", ("bid-restart", b"restart-payload")))
        reopened.close()

    def test_process_restart_rediscovers_inbox_linked_before_directory_barrier(self) -> None:
        process = multiprocessing.Process(target=crash_after_inbound_link,
                                          args=(str(self.root),))
        process.start()
        process.join(10)
        self.assertFalse(process.is_alive())
        self.assertEqual(process.exitcode, 93)

        reopened = WorkflowJournal(self.root, lambda records: records)
        reopened.open()
        self.assertEqual([(bid, decode_inbound(path.read_bytes()))
                          for bid, _identity, path in reopened.inbound_items],
                         [("bid-crash", ("bid-crash", b"crash-payload"))])
        reopened.close()

    def test_inventory_count_and_aggregate_refuse_before_staging_allocation(self) -> None:
        journal = WorkflowJournal(self.root, lambda records: records)
        journal.open()

        downloaded = []
        with mock.patch("tools.workflow_journal.MAX_BPA_INVENTORY", 2):
            with self.assertRaisesRegex(JournalError, "inventory"):
                journal.stage_inbound("bid", IDENTITY, lambda: iter(("bid", "x", "y")),
                                      lambda bid: downloaded.append(bid) or b"payload",
                                      lambda bid: None)
        self.assertEqual(downloaded, [])
        self.assertEqual(list(journal.staging.iterdir()), [])
        self.assertEqual(list(journal.inbound.iterdir()), [])

        with mock.patch("tools.workflow_journal.MAX_INBOUND_COUNT", 0):
            with self.assertRaisesRegex(JournalError, "count"):
                journal.stage_inbound("bid", IDENTITY, lambda: ["bid"],
                                      lambda bid: downloaded.append(bid) or b"payload",
                                      lambda bid: None)
        self.assertEqual(downloaded, [])
        self.assertEqual(list(journal.staging.iterdir()), [])

        with mock.patch("tools.workflow_journal.MAX_INBOUND_AGGREGATE", 1):
            with self.assertRaisesRegex(JournalError, "aggregate"):
                journal.stage_inbound("bid", IDENTITY, lambda: ["bid"],
                                      lambda bid: downloaded.append(bid) or b"payload",
                                      lambda bid: None)
        self.assertEqual(downloaded, ["bid"])
        self.assertEqual(list(journal.staging.iterdir()), [])
        self.assertEqual(list(journal.inbound.iterdir()), [])
        journal.close()

    def test_open_rejects_excess_inbox_before_replay(self) -> None:
        root = self.root
        (root / "inbound").mkdir(parents=True)
        (root / "inbound" / "x.bp").write_bytes(encode_inbound("bid", IDENTITY, b"payload"))
        replayed = []
        with mock.patch("tools.workflow_journal.MAX_INBOUND_COUNT", 0):
            opened = WorkflowJournal(root, lambda records: replayed.append(records))
            with self.assertRaisesRegex(JournalFault, "count"):
                opened.open()
        self.assertTrue(opened.fenced)
        self.assertIsNone(opened.lock_fd)
        self.assertEqual(replayed, [])

    def test_actual_acl2_bridge_initializes_then_replays_config(self) -> None:
        """The only workflow state transition is the executable ACL2 replay."""
        store = Acl2Store()
        journal = reopened = None
        try:
            bridge = Acl2WorkflowReplay(store)
            journal = WorkflowJournal(self.root, bridge)
            self.assertIs(journal.open(), bridge)
            self.assertFalse(bridge.initialized)
            published = journal.initialize(CONFIG)
            self.assertEqual(published.sequence, 0)
            self.assertTrue(bridge.initialized)
            journal.close()

            reopened = WorkflowJournal(self.root, bridge)
            self.assertIs(reopened.open(), bridge)
            self.assertTrue(bridge.initialized)
            self.assertFalse(reopened.fenced)
        finally:
            if journal is not None:
                journal.close()
            if reopened is not None:
                reopened.close()
            store.close()


if __name__ == "__main__":
    unittest.main()
