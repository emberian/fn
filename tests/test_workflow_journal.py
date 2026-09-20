import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from tools.run_store import ScriptedFaults
from tools.workflow_journal import (InboundDeletePending, JournalError, JournalFault,
                                    JournalUncertain, WorkflowJournal, decode_record,
                                    decode_inbound, encode_inbound, encode_record)

# The journal never derives, parses or compares these octets against anything
# but each other: ACL2 derives them from a bundle's primary block and the inbox
# is keyed by their digest.  Two distinct values stand for two distinct bundles.
IDENTITY = b"\x83\x82\x01\x65//n1/\x18\x64\x01"
OTHER_IDENTITY = b"\x83\x82\x01\x65//n2/\x18\x64\x01"



ATTEMPT = {"txid": 7, "tx-generation": 3, "work-id": "work:a",
           "attempt-id": "attempt:a:1", "attempt-generation": 1,
           "local-eid": "dtn://local/", "peer-eid": "dtn://peer/",
           "policy-id": "policy:local:1", "bp-lifetime": 3600}
ENQUEUE = {"txid": 7, "tx-generation": 3, "work-id": "work:a",
           "msgid": "<a@example>", "immutable-subject": "sha256:abc",
           "archive-obligation-id": "archive:a",
           "forward-obligation-id": "forward:a", "peer-eid": "dtn://peer/",
           "policy-id": "policy:local:1", "terms-id": "terms:1"}
EXPECTED_ATTEMPT_HEX = (
    "464e5746010300000060000000000000000700000000000000030006776f726b3a61"
    "000b617474656d70743a613a310000000000000001000c64746e3a2f2f6c6f63616c"
    "2f000b64746e3a2f2f706565722f000e706f6c6963793a6c6f63616c3a3100000000"
    "00000e100bb6baf5f022bd48d08c32b3e8375e47cdba50a410b357643767b0ab0a19cb5a")


class WorkflowJournalTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-workflow-")
        self.root = Path(self.temp.name) / "workflow"
        self.replays = []
        def replay(records):
            self.replays.append(records)
            return {"acl2-image": len(records)}
        self.journal = WorkflowJournal(self.root, replay)
        self.assertEqual(self.journal.open(), {"acl2-image": 0})

    def tearDown(self): self.journal.close(); self.temp.cleanup()

    def faulted(self, point="directory-fsync", error=None):
        """Attach the test-only injector; the journal itself holds no branch."""
        self.journal.faults = ScriptedFaults(
            point, OSError("injected directory uncertainty") if error is None else error)
        return self.journal

    def test_codec_exact_round_trip_and_damage(self):
        encoded = encode_record("attempt", ATTEMPT)
        # This literal pins the local schema byte, field order, widths and digest.
        self.assertEqual(encoded.hex(), EXPECTED_ATTEMPT_HEX)
        self.assertEqual(decode_record(encoded), ("attempt", ATTEMPT))
        damaged = bytearray(encoded); damaged[12] ^= 1
        with self.assertRaises(JournalFault): decode_record(bytes(damaged))

    def test_attempt_is_durable_before_bpa_call(self):
        observations=[]
        def bpa():
            path=self.journal.records / "0000000000000000.wf"
            observations.append(decode_record(path.read_bytes()))
            return "submitted"
        self.assertEqual(self.journal.persist_attempt_then_call(ATTEMPT, bpa), "submitted")
        self.assertEqual(observations, [("attempt", ATTEMPT)])

    def test_enqueue_requires_node_binding_and_ack_means_published(self):
        with self.assertRaisesRegex(Exception, "durable node"):
            self.journal.persist_enqueue(ENQUEUE, lambda values: False)
        self.assertEqual(list(self.journal.records.iterdir()), [])
        published=self.journal.persist_enqueue(ENQUEUE, lambda values: True)
        self.assertTrue(published.path.exists())
        self.assertEqual(decode_record(published.path.read_bytes()),
                         ("outcome", {"txid":7, "tx-generation":3,
                                      "phase":"ordinary", "result":"durable"}))

    def test_uncertain_publication_fences_and_does_not_call_bpa(self):
        called=[]
        with mock.patch("tools.workflow_journal.fsync_dir",
                        side_effect=OSError("directory barrier")):
            with self.assertRaises(JournalUncertain):
                self.journal.persist_attempt_then_call(ATTEMPT,
                                                        lambda: called.append(True))
        self.assertEqual(called, [])
        self.assertTrue(self.journal.fenced)
        with self.assertRaises(JournalFault): self.journal.publish("attempt", ATTEMPT)

    def test_reopen_replays_visible_uncertain_attempt(self):
        with self.assertRaises(JournalUncertain):
            self.faulted().publish("attempt", ATTEMPT)
        self.journal.close()
        reopened_records=[]
        reopened=WorkflowJournal(self.root,
            lambda records: reopened_records.extend(records) or "acl2-recovered")
        self.assertEqual(reopened.open(), "acl2-recovered")
        self.assertEqual(reopened_records, [("attempt", ATTEMPT)])
        reopened.close()

    def test_transport_expiry_is_only_replayed_input(self):
        transport={"work-id":"work:a", "attempt-id":"attempt:a:1",
                   "attempt-generation":1, "status":"expired"}
        self.journal.publish("transport", transport)
        observed=[]
        self.journal.close()
        reopened=WorkflowJournal(self.root, lambda records: observed.extend(records) or object())
        reopened.open()
        self.assertEqual(observed, [("transport", transport)])
        reopened.close()

    def test_malformed_namespace_refuses_image(self):
        (self.journal.records / "junk").write_bytes(b"x")
        self.journal.close()
        reopened=WorkflowJournal(self.root, lambda records: self.fail("must not replay"))
        with self.assertRaises(JournalFault): reopened.open()
        reopened.close()

    def test_a_symlinked_or_irregular_lock_pathname_is_refused(self):
        """The lock pathname cannot be replaced to evade an existing lock."""
        self.journal.close()
        lock=self.root/"workflow.lock"
        elsewhere=self.root/"elsewhere.lock"; elsewhere.write_bytes(b"")
        lock.unlink(); lock.symlink_to(elsewhere)
        replaced=WorkflowJournal(self.root, lambda records: records)
        with self.assertRaisesRegex(JournalFault, "symlink"):
            replaced.open()
        lock.unlink(); os.mkfifo(lock, 0o600)
        with self.assertRaisesRegex(JournalFault, "non-regular"):
            WorkflowJournal(self.root, lambda records: records).open()
        lock.unlink()
        self.journal=WorkflowJournal(self.root, lambda records: records)
        self.journal.open()

    def test_lock_contention_refuses_second_owner(self):
        contender=WorkflowJournal(self.root, lambda records: records)
        with self.assertRaisesRegex(JournalFault, "already owned"):
            contender.open()

    def test_headroom_refusal_preserves_existing_attempt(self):
        published=self.journal.publish("attempt", ATTEMPT)
        before=published.path.read_bytes()
        with mock.patch("tools.workflow_journal.MAX_AGGREGATE", len(before)):
            with self.assertRaisesRegex(JournalFault, "aggregate"):
                self.journal.publish("attempt", {**ATTEMPT, "attempt-id":"attempt:a:2"})
        self.assertEqual(published.path.read_bytes(), before)
        self.assertEqual(len(list(self.journal.records.iterdir())), 1)

    def test_intent_refused_before_publication_without_outcome_headroom(self):
        with mock.patch("tools.workflow_journal.MAX_RECORDS", 1):
            with self.assertRaisesRegex(JournalFault, "resolution headroom"):
                self.journal.persist_attempt_then_call(ATTEMPT, self.fail)
        self.assertEqual(list(self.journal.records.iterdir()), [])

    def test_inbound_inventory_download_fsync_then_explicit_delete(self):
        order=[]
        path=self.journal.stage_inbound(
            "local-bid-7", IDENTITY, lambda: order.append("inventory") or ["local-bid-7"],
            lambda bid: order.append(("download",bid)) or b"bundle",
            lambda bid: order.append(("delete",bid)))
        self.assertEqual(decode_inbound(path.read_bytes()), ("local-bid-7", IDENTITY, b"bundle"))
        self.assertEqual(order, ["inventory", ("download","local-bid-7"),
                                 ("delete","local-bid-7")])

    def test_inbound_barrier_failure_never_deletes_from_bpa(self):
        deleted=[]
        with mock.patch("tools.workflow_journal.fsync_dir",
                        side_effect=OSError("inbound barrier")):
            with self.assertRaises(JournalUncertain):
                self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"], lambda bid:b"bundle",
                                           lambda bid:deleted.append(bid))
        self.assertEqual(deleted, [])

    def test_inbound_lost_delete_retry_matches_and_deletes(self):
        with self.assertRaises(InboundDeletePending):
            self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"], lambda bid:b"bundle",
                                       lambda bid:(_ for _ in ()).throw(RuntimeError("lost")))
        deleted=[]
        path=self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"], lambda bid:b"bundle",
                                        lambda bid:deleted.append(bid))
        self.assertEqual(decode_inbound(path.read_bytes()), ("bid", IDENTITY, b"bundle"))
        self.assertEqual(deleted,["bid"])

    def test_pending_delete_with_the_bid_gone_reconciles_as_completed(self):
        """D14: a lost delete reply is resolved by the bundle's absence."""
        with self.assertRaises(InboundDeletePending):
            self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"], lambda bid:b"bundle",
                                       lambda bid:(_ for _ in ()).throw(RuntimeError("lost")))
        deleted=[]
        # The BPA no longer lists the BID: the earlier request took effect.
        path=self.journal.retry_staged_delete("bid", IDENTITY, lambda:[], deleted.append)
        self.assertEqual(decode_inbound(path.read_bytes()), ("bid", IDENTITY, b"bundle"))
        self.assertEqual(deleted, [])
        # Staging the same BID again is the same reconciliation, not a refusal
        # and not a second download.
        downloads=[]
        again=self.journal.stage_inbound(
            "bid", IDENTITY, lambda:[], lambda bid:downloads.append(bid) or b"bundle",
            lambda bid:deleted.append(bid))
        self.assertEqual(again, path)
        self.assertEqual((downloads, deleted), ([], []))

    def test_pending_delete_with_the_bid_present_is_retried(self):
        with self.assertRaises(InboundDeletePending):
            self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"], lambda bid:b"bundle",
                                       lambda bid:(_ for _ in ()).throw(RuntimeError("lost")))
        deleted=[]
        path=self.journal.retry_staged_delete("bid", IDENTITY, lambda:["bid"], deleted.append)
        self.assertEqual(deleted, ["bid"])
        self.assertEqual(decode_inbound(path.read_bytes()), ("bid", IDENTITY, b"bundle"))

    def test_absent_bid_without_a_durable_frame_is_still_refused(self):
        with self.assertRaisesRegex(JournalError, "not present in inventory"):
            self.journal.stage_inbound("missing", IDENTITY, lambda:[], lambda bid:b"bundle",
                                       lambda bid:None)
        with self.assertRaisesRegex(JournalFault, "absent"):
            self.journal.retry_staged_delete("missing", IDENTITY, lambda:[], lambda bid:None)

    def test_a_record_replaced_by_a_symlink_is_refused_on_reopen(self):
        published=self.journal.publish("attempt", ATTEMPT)
        self.journal.close()
        elsewhere=self.root/"elsewhere"
        elsewhere.write_bytes(published.path.read_bytes())
        published.path.unlink()
        published.path.symlink_to(elsewhere)
        reopened=WorkflowJournal(self.root, lambda records: self.fail("must not replay"))
        with self.assertRaises(JournalFault): reopened.open()
        reopened.close()

    def test_a_failing_close_cannot_close_a_reused_descriptor(self):
        """The staging descriptor number is retired before it is closed."""
        real_close=os.close
        replacement=None
        staged=[]

        def close_then_fail(fd):
            nonlocal replacement
            real_close(fd)
            if staged and fd == staged[0] and replacement is None:
                # POSIX hands out the lowest unused number, so reusing the
                # just-closed one makes an accidental second close observable.
                replacement=os.open(self.root/"unrelated", os.O_CREAT|os.O_RDWR, 0o600)
                raise OSError("injected staging close failure")

        real_open=os.open

        def record_open(path, flags, mode=0o777):
            fd=real_open(path, flags, mode)
            if Path(path).parent == self.journal.staging: staged.append(fd)
            return fd

        try:
            with mock.patch("tools.workflow_journal.os.open", side_effect=record_open), \
                 mock.patch("tools.workflow_journal.os.close", side_effect=close_then_fail):
                with self.assertRaises(OSError):
                    self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"],
                                               lambda bid:b"bundle", lambda bid:None)
            self.assertIsNotNone(replacement)
            os.fstat(replacement)
        finally:
            if replacement is not None: real_close(replacement)

    def test_open_rediscovers_durable_inbound_metadata(self):
        self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"], lambda bid:b"bundle", lambda bid:None)
        self.journal.close()
        reopened=WorkflowJournal(self.root, lambda records: records)
        reopened.open()
        self.assertEqual([(bid,identity,path.name)
                          for bid,identity,path in reopened.inbound_items],
                         [("bid", IDENTITY,
                           __import__("hashlib").sha256(IDENTITY).hexdigest()+".bp")])
        reopened.close()

    def test_inbox_is_keyed_by_identity_and_not_by_the_agents_bid(self):
        """A redelivery under a fresh BID is the same bundle; two identities are not."""
        first=self.journal.stage_inbound("bid-a", IDENTITY, lambda:["bid-a"],
                                         lambda bid:b"bundle", lambda bid:None)
        again=self.journal.stage_inbound("bid-b", IDENTITY, lambda:["bid-b"],
                                         lambda bid:b"bundle", lambda bid:None)
        self.assertEqual(again, first)
        # Same payload, different identity: two bundles, two staged frames.
        other=self.journal.stage_inbound("bid-c", OTHER_IDENTITY, lambda:["bid-c"],
                                         lambda bid:b"bundle", lambda bid:None)
        self.assertNotEqual(other, first)
        self.assertEqual(len(list(self.journal.inbound.iterdir())), 2)

    def test_a_frame_staged_under_a_different_identity_fences(self):
        self.journal.stage_inbound("bid", IDENTITY, lambda:["bid"],
                                   lambda bid:b"bundle", lambda bid:None)
        digest=__import__("hashlib").sha256(IDENTITY).hexdigest()+".bp"
        (self.journal.inbound/digest).write_bytes(
            encode_inbound("bid", OTHER_IDENTITY, b"bundle"))
        with self.assertRaisesRegex(JournalFault, "inbound name"):
            reopened=WorkflowJournal(self.root, lambda records: records); reopened.open()


if __name__ == "__main__": unittest.main()
