import tempfile
import unittest
from unittest import mock
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'tools'))
from tools import run_bp_receive, run_bp_ingress, run_store

class ReceiveTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(prefix='fn-bpreceive-')
  self.store=Path(self.tmp.name)/'store';self.inbox=Path(self.tmp.name)/'inbox';self.receipts=Path(self.tmp.name)/'receipts'
  run_store.Store(self.store,True).initialize();self.inventory={};self.deleted=[]
  self.article=b'Message-ID: <portable@fn.example>\r\nNewsgroups: fn.letters\r\n\r\nportable body\r\n'
 def tearDown(self): self.tmp.cleanup()
 def request(self,incarnation=b'origin-1',work_id=b'work-portable-1',destination=b'dtn://fn.lab/inbox',policy=b'bp-lab-policy-v0'):
  b=run_bp_ingress.Acl2BpIngress()
  try:
   b.call('(include-book "books/bp-adu")')
   msgid=b.extract_message_id(self.article);_,subject,_=run_store.metadata(msgid,self.article)
   def text(x):return "(fn-store-octets->string '"+b.literal(x)+")"
   fields=[work_id,subject,b'dtn://sender.lab',destination,policy,incarnation,b'wire-auth',b'terms-1']
   form='(fn-bpa-encode (fn-bpa-make-request '+' '.join(text(x) for x in fields)+" '"+b.literal(self.article)+'))'
   return run_store.acl2_octets(b.call(form))
  finally:b.close()
 def invoke(self,bid,**kwargs):
  return run_bp_receive.receive_bpa_request(store_root=self.store,inbox_root=self.inbox,receipt_root=self.receipts,bid=bid,source_eid="dtn://sender.lab",
   inventory=lambda:list(self.inventory),download=lambda x:self.inventory[x],delete=lambda x:(self.deleted.append(x),self.inventory.pop(x)),**kwargs)
 def test_staged_wrapper_accepts_then_new_bid_regenerates_without_charge(self):
  request=self.request();self.inventory['bid-1']=request
  first=self.invoke('bid-1');self.assertEqual(first.outcome,'accepted');self.assertTrue(first.receipt_adu);self.assertEqual(self.deleted,['bid-1'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
  self.inventory['bid-2']=request
  second=self.invoke('bid-2');self.assertEqual(second.outcome,'duplicate');self.assertEqual(second.receipt_adu,first.receipt_adu);self.assertEqual(self.deleted,['bid-1','bid-2'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_bad_subject_stays_staged(self):
  request=self.request().replace(b'sha256:',b'Sha256:',1);self.inventory['bid-bad']=request
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-bad')
  self.assertIn('bid-bad',self.inventory);self.assertEqual(self.deleted,[])
 def test_wrong_destination_or_policy_stays_staged_before_store_mutation(self):
  self.inventory['bid-destination']=self.request(destination=b'dtn://wrong.lab/inbox')
  self.inventory['bid-policy']=self.request(policy=b'wrong-policy')
  for bid in ('bid-destination','bid-policy'):
   with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke(bid)
   self.assertIn(bid,self.inventory)
  self.assertEqual(self.deleted,[])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(0,0,0))
  finally:b.close();store.close()
 def test_conflicting_context_stays_staged_without_second_store_record(self):
  self.inventory['bid-1']=self.request();self.invoke('bid-1')
  self.inventory['bid-conflict']=self.request(b'origin-conflict')
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-conflict')
  self.assertIn('bid-conflict',self.inventory);self.assertEqual(self.deleted,['bid-1'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_store_commit_before_context_reopen_binds_existing_exact_record(self):
  seeded={'raw-bid':self.article};deleted=[]
  result=run_bp_ingress.ingest_bpa_adu(store_root=self.store,journal_root=Path(self.tmp.name)/'seed-inbox',
   journal_module_path=ROOT/'tools/workflow_journal.py',bid='raw-bid',inventory=lambda:list(seeded),
   download=lambda bid:seeded[bid],delete=lambda bid:(deleted.append(bid),seeded.pop(bid)),source_eid='dtn://seed.lab')
  self.assertEqual(result.outcome,'accepted');self.assertEqual(deleted,['raw-bid'])
  self.inventory['bid-recover']=self.request()
  received=self.invoke('bid-recover');self.assertEqual(received.outcome,'accepted');self.assertTrue(received.receipt_adu)
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_pending_receipt_requires_explicit_matching_recovery_decision(self):
  self.inventory['bid-first']=self.request()
  original=run_bp_receive.ReceiptJournal.commit_receipt
  with mock.patch.object(run_bp_receive.ReceiptJournal,'commit_receipt',side_effect=RuntimeError('crash cut')):
   with self.assertRaises(RuntimeError):self.invoke('bid-first')
  self.assertIn('bid-first',self.inventory);self.assertEqual(self.deleted,[])
  self.inventory['bid-retry']=self.request()
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-retry')
  recovered=self.invoke('bid-retry',pending_outcome='committed')
  self.assertEqual(recovered.outcome,'duplicate');self.assertTrue(recovered.receipt_adu)
  self.assertEqual(self.deleted,['bid-retry'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_pending_other_work_blocks_new_store_mutation(self):
  self.inventory['bid-first']=self.request(work_id=b'work-first')
  with mock.patch.object(run_bp_receive.ReceiptJournal,'commit_receipt',side_effect=RuntimeError('crash cut')):
   with self.assertRaises(RuntimeError):self.invoke('bid-first')
  self.inventory['bid-other']=self.request(work_id=b'work-other')
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-other')
  self.assertIn('bid-other',self.inventory);self.assertEqual(self.deleted,[])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
if __name__=='__main__':unittest.main()
