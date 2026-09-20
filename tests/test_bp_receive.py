import tempfile
import zlib
import unittest
from unittest import mock
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'tools'))
from tools import bundle_bridge, run_bp_receive, run_bp_ingress, run_store, workflow_journal

# The ACL2 primary-block encoder builds every bundle used here; nothing in this
# file spells a BPv7 field.  `fn-bpi-host-bundle-prefix` returns the
# indefinite-array head and the certified primary-block encoding, and the test
# appends octets the boundary never interprets -- the break stop code standing
# in for the remaining blocks.
LAB_SOURCE=b'//sender.lab/'
LIVE_LIFETIME=10**15   # any admissible true time is inside it: :live
EXPIRED_LIFETIME=1000  # a 2000-era creation time is long past it: :expired

def lab_bundle(bridge, *, source=LAB_SOURCE, creation=1000, sequence=1,
               lifetime=LIVE_LIFETIME, flags=0, offset=None, total=None,
               tail=b'\xff'):
 def eid(ssp): return "(cons :dtn '"+bridge.literal(ssp)+")"
 def opt(v): return 'nil' if v is None else str(v)
 form=("(fn-bpi-host-bundle-prefix (fn-bpp-make-block {} 0 {} {} {} {} {} {} {} {}))"
       .format(flags, eid(b'//fn.lab/inbox'), eid(source), eid(b'//fn.lab/report'),
               creation, sequence, lifetime, opt(offset), opt(total)))
 return run_store.acl2_octets(bridge.call(form))+tail

def lab_bundles(specs):
 """Build several bundles in one ACL2 session rather than one each."""
 b=run_bp_ingress.Acl2BpIngress()
 try: return [lab_bundle(b, **spec) for spec in specs]
 finally: b.close()


class ReceiveTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(prefix='fn-bpreceive-')
  self.store=Path(self.tmp.name)/'store';self.inbox=Path(self.tmp.name)/'inbox';self.receipts=Path(self.tmp.name)/'receipts'
  run_store.Store(self.store,True).initialize();self.inventory={};self.bundles={};self.deleted=[]
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
 def stage(self,bid,adu,**spec):
  """Register one BPA bundle: its ADU for download, its octets for identity.

  Each BID gets its own creation sequence unless a test says otherwise, so
  these are distinct bundles that happen to be carried by one agent.
  """
  spec.setdefault('sequence',zlib.crc32(bid.encode('ascii'))+1)
  self.inventory[bid]=adu;self.bundles[bid]=lab_bundles([spec])[0]
  return self.bundles[bid]
 def invoke(self,bid,**kwargs):
  return run_bp_receive.receive_bpa_request(store_root=self.store,inbox_root=self.inbox,receipt_root=self.receipts,bid=bid,source_eid="dtn://sender.lab",
   inventory=lambda:list(self.inventory),download=lambda x:self.inventory[x],bundle=lambda x:self.bundles[x],
   delete=lambda x:(self.deleted.append(x),self.inventory.pop(x)),**kwargs)
 def staged_names(self):
  return sorted(path.name for path in (self.inbox/'inbound').iterdir())
 def test_staged_wrapper_accepts_then_new_bid_regenerates_without_charge(self):
  request=self.request();self.stage('bid-1',request)
  first=self.invoke('bid-1');self.assertEqual(first.outcome,'accepted');self.assertTrue(first.receipt_adu);self.assertEqual(self.deleted,['bid-1'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
  self.stage('bid-2',request)
  second=self.invoke('bid-2');self.assertEqual(second.outcome,'duplicate');self.assertEqual(second.receipt_adu,first.receipt_adu);self.assertEqual(self.deleted,['bid-1','bid-2'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_bad_subject_stays_staged(self):
  # The label lives inside the encoded identity now, so a wrong subject is a
  # wrong identity, not a wrong prefix.  The fixture asks the bridge for the
  # subject the receiver will derive and then breaks one digit of it.
  b=run_bp_ingress.Acl2BpIngress()
  try:msgid=b.extract_message_id(self.article);_,subject,_=run_store.metadata(msgid,self.article)
  finally:b.close()
  wrong=subject[:-1]+(b'0' if subject[-1:]!=b'0' else b'1')
  request=self.request().replace(subject,wrong,1);self.stage('bid-bad',request)
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-bad')
  self.assertIn('bid-bad',self.inventory);self.assertEqual(self.deleted,[])
 def test_wrong_destination_or_policy_stays_staged_before_store_mutation(self):
  self.stage('bid-destination',self.request(destination=b'dtn://wrong.lab/inbox'))
  self.stage('bid-policy',self.request(policy=b'wrong-policy'))
  for bid in ('bid-destination','bid-policy'):
   with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke(bid)
   self.assertIn(bid,self.inventory)
  self.assertEqual(self.deleted,[])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(0,0,0))
  finally:b.close();store.close()
 def test_conflicting_context_stays_staged_without_second_store_record(self):
  self.stage('bid-1',self.request());self.invoke('bid-1')
  self.stage('bid-conflict',self.request(b'origin-conflict'))
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-conflict')
  self.assertIn('bid-conflict',self.inventory);self.assertEqual(self.deleted,['bid-1'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_store_commit_before_context_reopen_binds_existing_exact_record(self):
  # The raw ingress commits the article to the Store under its own bundle and
  # its own staging journal; the receiver then meets an exact durable record
  # with no receipt context of its own.
  seeded={'raw-bid':self.article};deleted=[]
  seed_bundle=lab_bundles([dict(sequence=zlib.crc32(b'raw-bid')+1)])[0]
  result=run_bp_ingress.ingest_bpa_adu(store_root=self.store,journal_root=Path(self.tmp.name)/'seed-inbox',
   journal_module_path=ROOT/'tools/workflow_journal.py',bid='raw-bid',inventory=lambda:list(seeded),
   download=lambda bid:seeded[bid],bundle=lambda bid:seed_bundle,
   delete=lambda bid:(deleted.append(bid),seeded.pop(bid)),source_eid='dtn://seed.lab')
  self.assertEqual(result.outcome,'accepted');self.assertEqual(deleted,['raw-bid'])
  self.stage('bid-recover',self.request())
  received=self.invoke('bid-recover');self.assertEqual(received.outcome,'accepted');self.assertTrue(received.receipt_adu)
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_pending_receipt_requires_explicit_matching_recovery_decision(self):
  self.stage('bid-first',self.request())
  original=run_bp_receive.ReceiptJournal.commit_receipt
  with mock.patch.object(run_bp_receive.ReceiptJournal,'commit_receipt',side_effect=RuntimeError('crash cut')):
   with self.assertRaises(RuntimeError):self.invoke('bid-first')
  self.assertIn('bid-first',self.inventory);self.assertEqual(self.deleted,[])
  self.stage('bid-retry',self.request())
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-retry')
  recovered=self.invoke('bid-retry',pending_outcome='committed')
  self.assertEqual(recovered.outcome,'duplicate');self.assertTrue(recovered.receipt_adu)
  self.assertEqual(self.deleted,['bid-retry'])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_pending_other_work_blocks_new_store_mutation(self):
  self.stage('bid-first',self.request(work_id=b'work-first'))
  with mock.patch.object(run_bp_receive.ReceiptJournal,'commit_receipt',side_effect=RuntimeError('crash cut')):
   with self.assertRaises(RuntimeError):self.invoke('bid-first')
  self.stage('bid-other',self.request(work_id=b'work-other'))
  with self.assertRaises(run_bp_receive.BpReceiveError):self.invoke('bid-other')
  self.assertIn('bid-other',self.inventory);self.assertEqual(self.deleted,[])
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()
 def test_a_new_bid_for_the_same_bundle_stages_once_and_adds_no_article(self):
  """A redelivery is the same bundle however the agent renamed it."""
  request=self.request();self.stage('bid-1',request,sequence=7)
  first=self.invoke('bid-1');self.assertEqual(first.outcome,'accepted')
  names=self.staged_names();self.assertEqual(len(names),1)
  # A distinct BID, the same bundle octets: one staged frame, one article.
  self.inventory['bid-2']=request;self.bundles['bid-2']=self.bundles['bid-1']
  second=self.invoke('bid-2')
  self.assertEqual(second.outcome,'duplicate')
  self.assertEqual(second.receipt_adu,first.receipt_adu)
  self.assertEqual(self.staged_names(),names)
  store,b,records=run_bp_ingress.open_live_bp_store(self.store,False)
  try:self.assertEqual((len(records),b.article_count(),b.pin_count()),(1,1,1))
  finally:b.close();store.close()

 def test_two_identities_with_identical_payloads_are_two_staged_requests(self):
  """Identical bytes from two bundles are two requests, not one."""
  request=self.request()
  self.stage('bid-a',request,sequence=1);self.stage('bid-b',request,sequence=2)
  self.assertNotEqual(self.bundles['bid-a'],self.bundles['bid-b'])
  self.assertEqual(self.invoke('bid-a').outcome,'accepted')
  self.assertEqual(self.invoke('bid-b').outcome,'duplicate')
  self.assertEqual(len(self.staged_names()),2)

 def test_fragments_of_one_adu_are_not_duplicates_of_each_other(self):
  """Same source, timestamp and sequence; different offsets; two bundles."""
  first,second,whole=lab_bundles([
   dict(flags=1,offset=0,total=8),dict(flags=1,offset=4,total=8),dict()])
  bridge=bundle_bridge.BundleBridge()
  reports=[bridge.report(raw) for raw in (first,second,whole)]
  self.assertEqual([r.decision for r in reports],['live','live','live'])
  self.assertEqual([r.fragment_offset for r in reports],[0,4,None])
  self.assertEqual(len({r.identity for r in reports}),3)
  self.assertEqual(len({r.key for r in reports}),3)
  # And the ADU key they share is exactly what reassembly groups on.
  self.assertEqual({(r.source,r.creation_time,r.sequence) for r in reports},
                   {('dtn://sender.lab/',1000,1)})

 def test_an_expired_bundle_is_refused_and_its_bid_is_retained(self):
  self.stage('bid-old',self.request(),lifetime=EXPIRED_LIFETIME)
  result=self.invoke('bid-old')
  self.assertEqual(result.outcome,'refused-expired')
  self.assertIsNone(result.staged_path)
  self.assertIn('bid-old',self.inventory);self.assertEqual(self.deleted,[])
  self.assertFalse((self.inbox/'inbound').exists() and self.staged_names())

 def test_an_undecidable_expiry_fences_and_is_not_a_refusal(self):
  """A zero creation timestamp is unknown, not expired (RFC 9171 4.2.6)."""
  self.stage('bid-unknown',self.request(),creation=0)
  result=self.invoke('bid-unknown')
  self.assertEqual(result.outcome,'uncertain-expiry')
  self.assertIn('bid-unknown',self.inventory);self.assertEqual(self.deleted,[])

 def test_a_malformed_primary_block_is_refused_not_uncertain(self):
  self.inventory['bid-bad-block']=self.request()
  self.bundles['bid-bad-block']=b'\x9f\x01\xff'   # first item is a uint, not a block
  result=self.invoke('bid-bad-block')
  self.assertTrue(result.outcome.startswith('refused-identity:'),result.outcome)
  self.assertIn('bid-bad-block',self.inventory);self.assertEqual(self.deleted,[])
  # And octets that are not a bundle at all are a different refusal reason.
  self.inventory['bid-not-bundle']=self.request()
  self.bundles['bid-not-bundle']=b'not a bundle'
  self.assertEqual(self.invoke('bid-not-bundle').outcome,
                   'refused-identity:not-a-bundle')

 def test_an_anonymous_source_is_refused_as_unidentifiable(self):
  """RFC 9171 4.2.3: a dtn:none source is not uniquely identifiable."""
  b=run_bp_ingress.Acl2BpIngress()
  try:
   form=("(fn-bpi-host-bundle-prefix (fn-bpp-make-block 4 0 (cons :dtn '"
         +b.literal(b'//fn.lab/inbox')+") (list :dtn-none) (list :dtn-none)"
         " 1000 1 1000000 nil nil))")
   anonymous=run_store.acl2_octets(b.call(form))+b'\xff'
  finally:b.close()
  self.inventory['bid-anon']=self.request();self.bundles['bid-anon']=anonymous
  self.assertEqual(self.invoke('bid-anon').outcome,'refused-identity:anonymous')
  self.assertIn('bid-anon',self.inventory)

if __name__=='__main__':unittest.main()
