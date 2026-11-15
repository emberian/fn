"""Actual constructor/consumer source controls; ACL2 fixture is not executed."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def definition(file,name):
 return next(n for s in forms((ROOT/file).read_text()) for n in walk(read_sexp(s)) if n[:2]==['defun',name])
class ReusedSeal(unittest.TestCase):
 def test_actual_constructor_clears_before_new_proposal_frontier(self):
  f=definition('books/commit.lisp','fn2-commit-prepare-root')
  reset=['fn2-commit-root-set-seal-ready','physical','0','fn2-commit-root']
  self.assertIn(reset,list(walk(f)))
  self.assertIn(['fn2-commit-directory-new-row','batch','fn2-commit-root'],list(walk(f)))
 def test_consumer_requires_new_ready_bit_beyond_exact_tag(self):
  f=definition('books/commit-directory.lisp','fn2-commit-directory-predecessor-seal-slot')
  self.assertIn(['=',['fn2-commit-root-seal-ready','row','fn2-commit-root'],'0'],list(walk(f)))
  witness=definition('tests/commit-reused-seal-ready-unit.lisp','fn2-crsr-body')
  for name in ('fn2-commit-prepare-root','fn2-crsr-get','fn2-corep','fn2-core-wfp'):
   self.assertIn(name,str(witness))
  self.assertIn(['eq','after',':more'],list(walk(witness)))
  self.assertIn(['eq','without-reset',':ok'],list(walk(witness)))
if __name__=='__main__':unittest.main()
