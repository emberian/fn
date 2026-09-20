"""Submitting outbound work across a workflow journal restart.

The four-node lab could not submit after a reopen and read `absent` for every
replayed work id (`planning/lanes/HANDOFF-w3-media-lab.md`).  These cases pin
what a reopen must leave behind: the works the history enqueued, each with the
status the history last gave it, and a first attempt that ACL2 still admits.
"""
import tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from tools import run_store
from tools.workflow_bridge import Acl2WorkflowReplay
from tools.workflow_journal import JournalError, WorkflowJournal

CONFIG={"local-eid":"dtn://local/","peer-eid":"dtn://peer/","policy-id":"policy:1",
 "receipt-authority":"dtn://issuer/","bp-lifetime":3600,"incarnation":"inc:1",
 "authorization-context":"auth:1"}


class WorkflowRestartTests(unittest.TestCase):
 def setUp(self):
  self._dir=tempfile.TemporaryDirectory(prefix="fn-workflow-restart-")
  self.addCleanup(self._dir.cleanup)
  d=Path(self._dir.name)
  root=d/"store"; run_store.Store(root,True).initialize()
  payload=d/"article"; payload.write_bytes(b"article")
  self.assertEqual(run_store.command_post(SimpleNamespace(store=root,
   message_id="<a@example.invalid>",payload=payload,group=["fn.test"],charge=None,
   inject_fault=None)),0)
  store,acl2,_records=run_store.open_live_store(root,True)
  self.addCleanup(store.close); self.addCleanup(acl2.close)
  self.bridge=Acl2WorkflowReplay(acl2); self.workflow=d/"workflow"
  archive,subject,_evidence=run_store.metadata(b"<a@example.invalid>",b"article")
  self.enqueue={"txid":10,"tx-generation":0,"work-id":"work:a",
   "msgid":"<a@example.invalid>","immutable-subject":subject.decode("ascii"),
   "archive-obligation-id":archive.decode("ascii"),
   "forward-obligation-id":"forward:a","peer-eid":"dtn://peer/",
   "policy-id":"policy:1","terms-id":"terms:1"}
  self.attempt={"txid":11,"tx-generation":0,"work-id":"work:a",
   "attempt-id":"attempt:1","attempt-generation":0,"local-eid":"dtn://local/",
   "peer-eid":"dtn://peer/","policy-id":"policy:1","bp-lifetime":3600}

 def reopen(self):
  journal=WorkflowJournal(self.workflow,self.bridge); journal.open()
  self.addCleanup(journal.close)
  return journal

 def test_first_attempt_is_admitted_after_a_reopen(self):
  """The lab's blocker: enqueue, close, reopen, submit."""
  journal=self.reopen(); journal.initialize(CONFIG)
  journal.persist_enqueue(self.enqueue,lambda _values: True)
  journal.close()
  journal=self.reopen()
  self.assertEqual(self.bridge.work_status("work:a"),"outstanding")
  called=[]
  journal.persist_attempt_then_call(self.attempt,lambda: called.append("submit"))
  self.assertEqual(called,["submit"])

 def test_a_reopen_keeps_every_work_with_its_last_status(self):
  journal=self.reopen(); journal.initialize(CONFIG)
  journal.persist_enqueue(self.enqueue,lambda _values: True)
  journal.persist_attempt_then_call(self.attempt,lambda: None)
  journal.publish("transport",{"work-id":"work:a","attempt-id":"attempt:1",
   "attempt-generation":0,"status":"bpa-submit-replied"})
  journal.close()
  journal=self.reopen()
  self.assertEqual(self.bridge.work_status("work:a"),"restart-observed")

 def test_an_unknown_work_id_is_not_a_status(self):
  journal=self.reopen(); journal.initialize(CONFIG)
  journal.persist_enqueue(self.enqueue,lambda _values: True)
  journal.close(); self.reopen()
  self.assertEqual(self.bridge.work_status("work:never-enqueued"),"absent")

 def test_an_attempt_lifetime_other_than_the_configured_one_is_refused(self):
  """The lab submitted with a short lifetime; the model owns that equality."""
  journal=self.reopen(); journal.initialize(CONFIG)
  journal.persist_enqueue(self.enqueue,lambda _values: True)
  before=tuple(p.name for p in journal.records.iterdir())
  with self.assertRaisesRegex(JournalError,"durable history"):
   journal.persist_attempt_then_call({**self.attempt,"bp-lifetime":30},
                                     lambda: None)
  self.assertEqual(tuple(p.name for p in journal.records.iterdir()),before)


if __name__=="__main__":
 unittest.main()
