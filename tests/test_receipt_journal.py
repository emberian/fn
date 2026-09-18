import tempfile,unittest
from pathlib import Path
from unittest import mock
from tools.receipt_journal import (ReceiptJournal,decode_receiver_record,encode_receiver_record,
                                   MAX_RECORD)
from tools.receipt_bridge import Acl2ReceiptBridge
from tools.workflow_journal import JournalError,JournalFault,JournalUncertain
CONFIG={"destination-eid":"dtn://receiver/","policy-id":"policy:1","issuer-eid":"dtn://issuer/"}
REQ={"inbound-bid":"bid:1","request-adu":b"request","store-record":b"record","policy-authorized":True}
class Bridge:
 def __init__(self):self.records=[];self.reject=False
 def replay(self,records):self.records=list(records);return self
 def valid_config(self,record):return not self.reject and all(len(v)<=256 for v in record[1].values())
 def preflight(self,record):return not self.reject
 def apply(self,record):self.records.append(record)
 def preview_receipt(self,w,r):return b"receipt"
 def receipt_adu(self,r):return b"receipt" if len(self.records)>2 else b""
class ReceiptJournalTests(unittest.TestCase):
 def setUp(self):
  self.t=tempfile.TemporaryDirectory();self.b=Bridge();self.j=ReceiptJournal(Path(self.t.name)/"r",self.b);self.j.open();self.j.initialize(CONFIG)
 def tearDown(self):self.j.close();self.t.cleanup()
 def test_exact_codec_and_damage(self):
  raw=encode_receiver_record("request-context",REQ);self.assertEqual(decode_receiver_record(raw),("request-context",REQ))
  bad=bytearray(raw);bad[-1]^=1
  with self.assertRaises(JournalFault):decode_receiver_record(bytes(bad))
 def test_preflight_refusal_leaves_bytes_unchanged(self):
  before=list(self.j.records.iterdir());self.b.reject=True
  with self.assertRaises(JournalError):self.j.persist_request(REQ)
  self.assertEqual(list(self.j.records.iterdir()),before)
 def test_bad_or_repeated_config_never_appends_bytes(self):
  before=tuple((p.name,p.read_bytes()) for p in self.j.records.iterdir())
  with self.assertRaisesRegex(JournalFault,"already initialized"):self.j.initialize(CONFIG)
  self.assertEqual(tuple((p.name,p.read_bytes()) for p in self.j.records.iterdir()),before)
  self.j.close();root=Path(self.t.name)/"bad";b=Bridge();j=ReceiptJournal(root,b);j.open()
  with self.assertRaisesRegex(JournalError,"config"):
   j.initialize({**CONFIG,"issuer-eid":"x"*257})
  self.assertEqual(list(j.records.iterdir()),[]);j.close()
 def test_receipt_intent_reserves_decision_headroom(self):
  self.j.persist_request(REQ)
  with mock.patch("tools.receipt_journal.MAX_AGGREGATE",sum(p.stat().st_size for p in self.j.records.iterdir())+MAX_RECORD):
   with self.assertRaisesRegex(JournalFault,"headroom"):self.j.persist_receipt_intent("work:1","receipt:1")
 def test_postlink_uncertainty_fences_and_replays_visible_record(self):
  with self.assertRaises(JournalUncertain):self.j.publish("request-context",REQ,fault="postlink")
  self.assertTrue(self.j.fenced);self.j.close();b=Bridge();j=ReceiptJournal(Path(self.t.name)/"r",b);j.open()
  self.assertEqual([k for k,_ in b.records],["config","request-context"]);j.close()
 def test_exclusive_owner(self):
  other=ReceiptJournal(Path(self.t.name)/"r",Bridge())
  with self.assertRaises(JournalFault):other.open()
 def test_recovery_barrier_failure_releases_lock_and_normalizes(self):
  self.j.close();real=__import__('tools.receipt_journal',fromlist=['fsync_dir']).fsync_dir
  with mock.patch("tools.receipt_journal.fsync_dir",side_effect=OSError("barrier")):
   with self.assertRaisesRegex(JournalFault,"recovery failed"):ReceiptJournal(Path(self.t.name)/"r",Bridge()).open()
  fresh=ReceiptJournal(Path(self.t.name)/"r",Bridge());fresh.open();fresh.close()
 def test_public_raw_nonbytes_refused_before_acl2_call(self):
  class Store:
   def __init__(self):self.calls=0
   def call(self,_):self.calls+=1;raise AssertionError("ACL2 must not be called")
  bridge=object.__new__(Acl2ReceiptBridge);bridge.store=Store();bridge.initialized=True
  with self.assertRaises(JournalFault):bridge.receipt_adu("not-bytes")
  self.assertEqual(bridge.store.calls,0)
if __name__=="__main__":unittest.main()
