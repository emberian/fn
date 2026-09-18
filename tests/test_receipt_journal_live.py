import tempfile,unittest
from pathlib import Path
from tools import run_bp_ingress,run_store
from tools.receipt_bridge import Acl2ReceiptBridge
from tools.receipt_journal import ReceiptJournal
from tools.workflow_journal import JournalError,JournalUncertain
class ReceiptJournalLiveTests(unittest.TestCase):
 @staticmethod
 def sf(v):return "(fn-store-octets->string '("+" ".join(map(str,v)) + "))"
 def make_request(self,b,subject,article,work=b"work:1"):
  fields=[work,subject,b"dtn://sender.lab",b"dtn://fn.lab/inbox",b"policy:1",b"origin:1",b"auth:1",b"terms:1"]
  form="(fn-bpa-encode (fn-bpa-make-request "+" ".join(self.sf(x) for x in fields)+" '("+" ".join(map(str,article))+")))"
  return run_store.acl2_octets(b.call(form))
 def test_actual_store_request_decision_restart_and_regeneration(self):
  with tempfile.TemporaryDirectory(prefix="fn-bprj-") as d:
   root=Path(d)/"store";run_store.Store(root,True).initialize()
   article=b"Message-ID: <r@fn.example>\r\nNewsgroups: fn.test\r\n\r\nbody\r\n"
   store,b,records=run_bp_ingress.open_live_bp_store(root,True)
   try:
    msgid=b.extract_message_id(article);archive,subject,evidence=run_store.metadata(msgid,article)
    store.advance_frontier(b,b.next_txid());self.assertEqual(b.ingress_prepare(
     b"dtn://fn.lab/inbox",b"dtn://sender.lab",b"bid:1",300,archive,subject,evidence,
     run_store.conservative_charge(article),article),"prepared")
    record=b.pending_record();self.assertEqual(store.publish(b,len(records),record),"durable")
    store.fenced=True;self.assertEqual(store.finish(b),"durable")
    bridge=Acl2ReceiptBridge(b);j=ReceiptJournal(Path(d)/"receipt",bridge);j.open()
    j.initialize({"destination-eid":"dtn://fn.lab/inbox","policy-id":"policy:1","issuer-eid":"dtn://issuer/"})
    request=self.make_request(b,subject,article)
    values={"inbound-bid":"bid:1","request-adu":request,"store-record":record,"policy-authorized":True}
    j.persist_request(values)
    before=tuple((p.name,p.read_bytes()) for p in j.records.iterdir())
    bad=self.make_request(b,b"wrong",article,b"work:bad")
    with self.assertRaisesRegex(JournalError,"ACL2 rejected"):
     j.persist_request({**values,"inbound-bid":"bid:bad","request-adu":bad})
    self.assertEqual(tuple((p.name,p.read_bytes()) for p in j.records.iterdir()),before)
    with self.assertRaises(JournalUncertain):
     j.persist_receipt_intent("work:1","receipt:1",fault="postlink")
    j.close();j=ReceiptJournal(Path(d)/"receipt",bridge);j.open()
    self.assertEqual(j.receipt_adu(request),b"")
    j.decide_receipt("work:1","receipt:1","committed")
    receipt=j.receipt_adu(request);self.assertTrue(receipt)
    j.close();j=ReceiptJournal(Path(d)/"receipt",bridge);j.open()
    self.assertEqual(j.receipt_adu(request),receipt) # lost send/new BID regeneration
    self.assertEqual(b.article_count(),1);j.close()
   finally:b.close();store.close()
