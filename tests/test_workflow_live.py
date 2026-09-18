import hashlib, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from tools import run_store
from tools.workflow_bridge import Acl2WorkflowReplay
from tools.workflow_journal import JournalError, WorkflowJournal

CONFIG={"local-eid":"dtn://local/","peer-eid":"dtn://peer/","policy-id":"policy:1",
 "receipt-authority":"dtn://issuer/","bp-lifetime":3600,"incarnation":"inc:1",
 "authorization-context":"auth:1"}
class WorkflowLiveTests(unittest.TestCase):
 def test_real_node_enqueue_submit_restart_expiry_and_lost_outcome(self):
  with tempfile.TemporaryDirectory(prefix="fn-workflow-live-") as d:
   root=Path(d)/"store"; run_store.Store(root,True).initialize()
   payload=Path(d)/"article"; payload.write_bytes(b"article")
   self.assertEqual(run_store.command_post(SimpleNamespace(store=root,
    message_id="<a@example.invalid>",payload=payload,group=["fn.test"],charge=None,
    inject_fault=None)),0)
   store,acl2,_records=run_store.open_live_store(root,True)
   try:
    bridge=Acl2WorkflowReplay(acl2); journal=WorkflowJournal(Path(d)/"workflow",bridge)
    journal.open(); journal.initialize(CONFIG)
    subject="sha256:"+hashlib.sha256(b"article").hexdigest()
    archive="archive:"+hashlib.sha256(b"<a@example.invalid>\0"+subject.encode()).hexdigest()
    enqueue={"txid":10,"tx-generation":0,"work-id":"work:a","msgid":"<a@example.invalid>",
     "immutable-subject":subject,"archive-obligation-id":archive,
     "forward-obligation-id":"forward:a","peer-eid":"dtn://peer/",
     "policy-id":"policy:1","terms-id":"terms:1"}
    before=tuple(journal.records.iterdir())
    with self.assertRaisesRegex(JournalError,"ACL2 rejected"):
     journal.persist_enqueue({**enqueue,"immutable-subject":"wrong"},lambda _values: True)
    self.assertEqual(tuple(journal.records.iterdir()),before)
    journal.persist_enqueue(enqueue,lambda _values: True)
    attempt={"txid":11,"tx-generation":0,"work-id":"work:a","attempt-id":"attempt:1",
     "attempt-generation":0,"local-eid":"dtn://local/","peer-eid":"dtn://peer/",
     "policy-id":"policy:1","bp-lifetime":3600}
    called=[]; journal.persist_attempt_then_call(attempt,lambda: called.append("submit"))
    self.assertEqual(called,["submit"])
    self.assertFalse(bridge.take_submit(attempt))
    before=tuple((p.name,p.read_bytes()) for p in journal.records.iterdir())
    with self.assertRaisesRegex(JournalError,"ACL2 rejected"):
     journal.persist_attempt_then_call(attempt,lambda: called.append("stale"))
    self.assertEqual(tuple((p.name,p.read_bytes()) for p in journal.records.iterdir()),before)
    self.assertEqual(called,["submit"])
    journal.publish("transport",{"work-id":"work:a","attempt-id":"attempt:1",
     "attempt-generation":0,"status":"expired"})
    self.assertEqual(bridge.work_status("work:a"),"expired")
    journal.close(); journal=WorkflowJournal(Path(d)/"workflow",bridge); journal.open()
    self.assertEqual(bridge.work_status("work:a"),"expired")
    self.assertFalse(bridge.fenced())
    journal.publish_intent("attempt",{**attempt,"txid":12,"attempt-id":"attempt:2",
                                      "attempt-generation":1})
    journal.close(); journal=WorkflowJournal(Path(d)/"workflow",bridge); journal.open()
    self.assertTrue(bridge.fenced())
    before=tuple((p.name,p.read_bytes()) for p in journal.records.iterdir())
    with self.assertRaisesRegex(JournalError,"ACL2 rejected"):
     journal.publish_outcome(12,0,"ordinary","durable")
    self.assertEqual(tuple((p.name,p.read_bytes()) for p in journal.records.iterdir()),before)
    journal.recover_intent({"txid":12,"tx-generation":0},"absent")
    self.assertFalse(bridge.fenced())
    journal.close()
   finally: acl2.close(); store.close()
