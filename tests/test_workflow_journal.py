import tempfile
import unittest
from pathlib import Path
from unittest import mock

from tools.workflow_journal import (InboundDeletePending, JournalFault, JournalUncertain,
                                    WorkflowJournal, decode_record,
                                    decode_inbound, encode_record)


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
        self.assertEqual(decode_record(published.path.read_bytes()), ("enqueue", ENQUEUE))

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
            self.journal.publish("attempt", ATTEMPT, "directory-fsync")
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

    def test_inbound_inventory_download_fsync_then_explicit_delete(self):
        order=[]
        path=self.journal.stage_inbound(
            "local-bid-7", lambda: order.append("inventory") or ["local-bid-7"],
            lambda bid: order.append(("download",bid)) or b"bundle",
            lambda bid: order.append(("delete",bid)))
        self.assertEqual(decode_inbound(path.read_bytes()), ("local-bid-7", b"bundle"))
        self.assertEqual(order, ["inventory", ("download","local-bid-7"),
                                 ("delete","local-bid-7")])

    def test_inbound_barrier_failure_never_deletes_from_bpa(self):
        deleted=[]
        with mock.patch("tools.workflow_journal.fsync_dir",
                        side_effect=OSError("inbound barrier")):
            with self.assertRaises(JournalUncertain):
                self.journal.stage_inbound("bid", lambda:["bid"], lambda bid:b"bundle",
                                           lambda bid:deleted.append(bid))
        self.assertEqual(deleted, [])

    def test_inbound_lost_delete_retry_matches_and_deletes(self):
        with self.assertRaises(InboundDeletePending):
            self.journal.stage_inbound("bid", lambda:["bid"], lambda bid:b"bundle",
                                       lambda bid:(_ for _ in ()).throw(RuntimeError("lost")))
        deleted=[]
        path=self.journal.stage_inbound("bid", lambda:["bid"], lambda bid:b"bundle",
                                        lambda bid:deleted.append(bid))
        self.assertEqual(decode_inbound(path.read_bytes()), ("bid",b"bundle"))
        self.assertEqual(deleted,["bid"])

    def test_open_rediscovers_durable_inbound_metadata(self):
        self.journal.stage_inbound("bid", lambda:["bid"], lambda bid:b"bundle", lambda bid:None)
        self.journal.close()
        reopened=WorkflowJournal(self.root, lambda records: records)
        reopened.open()
        self.assertEqual([(bid,path.name) for bid,path in reopened.inbound_items],
                         [("bid", __import__("hashlib").sha256(b"bid").hexdigest()+".bp")])
        reopened.close()


if __name__ == "__main__": unittest.main()
