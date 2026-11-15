"""Source-only request/adoption route checks, with exact mutation controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
from sealer_checkpoint_request_port import EXPECTED,CORE
ROOT=Path(__file__).resolve().parents[1]
def defs(s):return {lr.emit(m.node.items[1],drop_comments=True):s[m.start:m.end] for m in lr.match('(defun ?name ?*body)',lr.parse(s).forms,deep=True)}
def require(book,s):
 if s!=EXPECTED[book]:raise ValueError('not the named actual request projection')
class Request(unittest.TestCase):
 def test_actual_source_is_exact_named_projection(self):
  for book,s in EXPECTED.items():require(book,(ROOT/'books'/(book+'.lisp')).read_text())
 def test_actual_legacy_observer_and_work_recipes_preserved(self):
  before=defs((ROOT/'tools/fixtures/sealer-checkpoint/events-before.lisp').read_text())
  after=defs(EXPECTED['machines-c-sealer-events'])
  for name in ('fn2-sealer-work','fn2-sealer-source-acquire','fn2-sealer-source-release','fn2-sealer-source-startable-p','fn2-sealer-boot-closed-p'):
   self.assertEqual(before[name],after[name],name)
 def test_no_prefix_or_read_receipt_before_maintenance_request(self):
  step=defs(EXPECTED['machines-c-sealer-events'])['fn2-sealer-step']
  self.assertLess(step.index('fn2-sealer-checkpoint-needed'),step.index('fn2-sealer-source-acquire'))
  s=(ROOT/'books/sealer-checkpoint-request.lisp').read_text()
  for text in ('*fn2-seal-phase-idle*','(equal (fn2-seals-held 0 fn2-seals) 0)',
               '(equal (fn2-seals-source-receipt 0 fn2-seals) 0)','fn2-sealer-loader-free-p','fn2-seal-pick','fn2-seal-compact-target'):
   self.assertIn(text,s)
 def test_resume_requires_actual_adoption_and_original_retirement(self):
  s=defs((ROOT/'books/sealer-checkpoint-request.lisp').read_text())['fn2-sealer-checkpoint-resumed-p']
  for text in ('*fn2-checkpoint-predecessor-phase-done*','*fn2-checkpoint-summary-phase-applied*','(< old-tag (fn2-checkpoint-summary-tag',
               '*fn2-csnapshot-phase-idle*','*fn2-c-source-writer-phase-idle*','completed-originals','owner-gen','candidate','cut-commit','cut-event'):
   self.assertIn(text,s)
 def test_requesting_machine_owns_no_windows(self):
  s=EXPECTED['machines-c-sealer-kind'];n=lr.match('(defmachine fn2-sealer ?*rest)',lr.parse(s).forms,deep=True)[0].node
  items=n.items;at=next(i for i,x in enumerate(items) if lr.emit(x,drop_comments=True)==':holds')
  self.assertNotIn(':checkpointing',lr.emit(items[at+1],drop_comments=True))
  self.assertIn('(:wake-row target)',EXPECTED['machines-c-sealer-events'])
  self.assertIn('fn2-checkpoint-master-snapshot-read-code',CORE)
 def test_pressure_and_wake_read_actual_namespace_not_host_flags(self):
  d=defs(EXPECTED['machines-c-sealer-events'])
  pending=d['fn2-sealer-checkpoint-pending-p']
  for x in ('fn2-sealer-snapshot-read-code','fn2-machine-kind','fn2-machine-generation-read-code',
            '(posp (fn2-machine-generation','fn2-machine-stopped','*fn2-sealer-state-checkpointing*'):
   self.assertIn(x,pending)
  for name in ('fn2-sealer-checkpoint-resume','fn2-sealer-checkpoint-wake-target'):
   self.assertIn('fn2-sealer-checkpoint-pending-p',d[name])
   self.assertIn('fn2-sealer-checkpoint-resumable-p',d[name])
  self.assertIn('(mv :ok (fn2-sealer-checkpoint-pending-p fn2-core))',d['fn2-sealer-checkpoint-pending-op'])
 def test_negative_reordered_acquire_and_removed_resume_gates_refused(self):
  for book,a,b in [('machines-c-sealer-events','(fn2-sealer-checkpoint-needed fn2-core)','(fn2-sealer-pending-p fn2-core)'),
                   ('machines-c-sealer-events','fn2-sealer-checkpoint-resume','fn2-sealer-source-acquire'),
                   ('machines-c-sealer-kind','(:checkpointing)', '(:stopped)')]:
   self.assertIn(a,EXPECTED[book])
   with self.assertRaises(ValueError):require(book,EXPECTED[book].replace(a,b,1))
if __name__=='__main__':unittest.main()
