"""Post-Fence transfer source controls; no ACL2 execution or persistence claim."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk
TREE=[read_sexp(f) for f in forms((ROOT/'books/release-inventory-transfer.lisp').read_text())]
def fun(name):return next(n for f in TREE for n in walk(f) if n[:2]==['defun',name])
class Transfer(unittest.TestCase):
 def test_actual_publication_and_allocated_identity_bind_source(self):
  source=fun('fn2-release-inventory-published-source-p')
  for name in ('fn2-event-producer-donep','fn2-release-publication-source','fn2-checkpoint-lifecycle-ownerp','fn2-release-inventory-source-terminal-p','fn2-release-inventory-ref-hash-p'):
   self.assertIn(name,str(source))
  page=fun('fn2-release-inventory-installed-page-p')
  self.assertIn('*fn2-extent-state-allocated*',str(page))
  self.assertNotIn('*fn2-extent-state-reserved*',str(page))
  for name in ('fn2-checkpoint-construction-native-p','fn2-checkpoint-page-verified-owner-gen','fn2-checkpoint-page-verified-ordinal','fn2-checkpoint-page-verified-completed-bytes'):
   self.assertIn(name,str(page))
 def test_settled_only_exact_three_drops_no_target_or_free(self):
  body=fun('fn2-release-evidence-transfer-transition');nodes=list(walk(body))
  drops=[n for n in nodes if n and n[0]=='fn2-alloc-edge-drop']
  self.assertEqual([n[1] for n in drops],['d-edge','i-edge','j-edge'])
  self.assertTrue(all(n[-3]==':obligation' for n in drops))
  for name in ('fn2-release-evidence-row-owned-p','*fn2-release-evidence-phase-persisted*','*fn2-release-evidence-phase-settled*','fn2-release-evidence-candidate-bound'):
   self.assertIn(name,str(body))
  for forbidden in ('fn2-release-evidence-extent','fn2-alloc-free','fn2-alloc-release','fn2-extents-set-state','fn2-checkpoint-source-edge'):
   self.assertNotIn(forbidden,[n[0] for n in nodes if n])
 def test_source_dominates_mutation_and_sweep_is_bounded(self):
  op=next(n for f in TREE for n in walk(f) if n[:2]==['fn2-release-inventory-operation','fn2-release-inventory-transfer-step'])
  nodes=list(walk(op));names=[n[0] for n in nodes if n]
  self.assertLess(names.index('fn2-release-inventory-published-source-p'),names.index('fn2-release-evidence-transfer-transition'))
  self.assertEqual(names.count('fn2-release-evidence-transfer-transition'),1)
  self.assertNotIn('fn2-release-inventory-transfer-step',names)
  for name in ('fn2-release-inventory-build-transfer-cursor','fn2-release-inventory-build-rows-count',':exhausted',':evidence'):
   self.assertIn(name,str(op))
 def test_rearm_requires_full_transfer_and_has_no_independent_reset(self):
  terminal=fun('fn2-release-inventory-transfer-terminal-p')
  self.assertIn('fn2-release-inventory-source-terminal-p',str(terminal))
  self.assertIn(['=',['fn2-release-inventory-build-transfer-cursor','0','fn2-release-inventory-build'],['fn2-release-inventory-build-rows-count','0','fn2-release-inventory-build']],list(walk(terminal)))
  self.assertNotIn('fn2-release-inventory-build-init',str(TREE))
if __name__=='__main__':unittest.main()
