"""Private real-index RELEASE mutation; no runtime/admission qualification."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def operation(text,name):
 return next(f for raw in forms(text) if (f:=read_sexp(raw))[:2]==['fn2-release-replay-settlement-function',name])
def calls(x,name):return [v for v in walk(x) if v and v[0]==name]
def mutation_order(text):
 f=operation(text,'fn2-release-target-settlement-progress')
 body=f[3];assert body[0]=='b*'
 names=[]
 for binding in body[1]:
  if len(binding)==2:
   for name in ('fn2-alloc-identity-commit-free','fn2-checkpoint-owned-release-clear','fn2-release-evidence-set-phase'):
    if calls(binding[1],name):names.append(name)
 return names
class ActualSettlement(unittest.TestCase):
 def setUp(self):self.text=(ROOT/'books/release-replay-settlement.lisp').read_text()
 def test_canonical_index_progress_and_atomic_cleanup(self):
  f=operation(self.text,'fn2-release-target-settlement-progress')
  for name in ('fn2-alloc-identity-owner-p','fn2-alloc-identity-prepare-free','fn2-alloc-identity-free-pending-p',
               'fn2-alloc-identity-step','fn2-alloc-identity-free-ready-p','fn2-alloc-identity-commit-free'):
   self.assertTrue(calls(f,name),name)
  expected=['fn2-alloc-identity-commit-free','fn2-checkpoint-owned-release-clear','fn2-release-evidence-set-phase']
  self.assertEqual(mutation_order(self.text),expected)
  mutant=self.text.replace('(fn2-checkpoint-owned-release-clear target fn2-checkpoint-construction)',
                           '(fn2-alloc-free target fn2-extents)',1)
  self.assertNotEqual(mutation_order(mutant),expected)
  self.assertNotIn('(fn2-alloc-free ',self.text)
  self.assertNotIn('(defcost ',self.text)
 def test_preflight_uses_exact_persisted_evidence_cut_and_ledger(self):
  f=operation(self.text,'fn2-release-target-settlement-code')
  for name in ('fn2-release-evidence-row-matches','fn2-release-evidence-row-owned-p',
               'fn2-alloc-release-under-cut-code','fn2-checkpoint-owned-release-ledger-code'):
   self.assertTrue(calls(f,name),name)
  text=str(f)
  for marker in ('*fn2-release-evidence-phase-persisted*','*fn2-extent-state-retire-pending*',
                 'fn2-allocation-release-retirement'):
   self.assertIn(marker,text)
  self.assertIn(['=',['fn2-alloc-freeze-phase','fn2-extents'],'4'],list(walk(f)))
  # Selected recovery phase4 itself has a positive retained snapshot token;
  # the live-snapshot predicate cannot be negated here without vacuity.
  self.assertNotIn('fn2-alloc-snapshot-activep',text)
 def test_source_generation_is_not_tag_or_cut_and_holds_survive(self):
  f=operation(self.text,'fn2-release-target-settlement-progress')
  self.assertIn(['source',['fn2-allocation-release-replay-generation','0','fn2-allocation-release']],list(walk(f)))
  phase=calls(f,'fn2-release-evidence-set-phase')
  self.assertEqual(phase,[['fn2-release-evidence-set-phase','journal','*fn2-release-evidence-phase-settled*','fn2-release-evidence']])
  self.assertNotIn('fn2-release-evidence-set-live',self.text)
  self.assertNotIn('fn2-alloc-edge-drop',self.text)
 def test_one_kernel_with_distinct_actual_suffix_cursor_contract(self):
  common=operation(self.text,'fn2-release-target-settlement-code')
  self.assertFalse(calls(common,'fn2-allocation-release-replay-base'))
  self.assertFalse(calls(common,'fn2-allocation-release-replay-roff'))
  suffix=operation(self.text,'fn2-release-replay-settlement-code')
  for name in ('fn2-allocation-release-replay-base','fn2-allocation-release-replay-roff',
               'fn2-allocation-release-replay-rend','fn2-allocation-release-replay-next'):
   self.assertTrue(calls(suffix,name),name)
  self.assertTrue(calls(suffix,'fn2-release-target-settlement-current-code'))
  progress=operation(self.text,'fn2-release-replay-settlement-progress')
  self.assertTrue(calls(progress,'fn2-release-target-settlement-current-progress'))
  self.assertFalse(calls(progress,'fn2-alloc-identity-commit-free'))
  self.assertEqual(self.text.count('(fn2-alloc-identity-commit-free '),1)
 def test_all_readonly_inputs_have_generated_type_and_wfp_domain(self):
  domain=next(read_sexp(raw) for raw in forms(self.text) if read_sexp(raw)[:2]==['defun','fn2-release-replay-settlement-hyps'])
  self.assertIn('"P"',next(raw for raw in forms(self.text) if 'defun fn2-release-replay-settlement-hyps' in raw))
  self.assertIn('"-WFP"',next(raw for raw in forms(self.text) if 'defun fn2-release-replay-settlement-hyps' in raw))
  self.assertTrue(calls(domain,'fn2-release-replay-settlement-hyps'))
  unit=(ROOT/'tests/release-replay-settlement-unit.lisp').read_text()
  for name in ('fn2-release-replay-settlement-current-code','fn2-alloc-ownership-invp',
               'fn2-alloc-identity-refines-p','fn2-rrsu-snapshot','fn2-aiu-adopt'):
   self.assertIn(name,unit)
  for mode in (':actor',':source',':target',':ledger',':protector',':not-persisted',':descriptor'):
   self.assertIn('(assert-event (fn2-rrsu-test '+mode+'))',unit)
if __name__=='__main__':unittest.main()
