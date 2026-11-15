"""Source controls for actual journal physical namespace capture, not ACL2 execution."""
from pathlib import Path
import sys, unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def definition(file,name):
 return next(n for s in forms((ROOT/'books'/file).read_text()) for n in walk(read_sexp(s)) if n[:2]==['defun',name])
class PhysicalSource(unittest.TestCase):
 def test_exact_getter_never_promotes_base_or_current_namespace(self):
  f=definition('commit-directory.lisp','fn2-commit-directory-physical-source')
  calls=list(walk(f))
  self.assertIn(['eq','code',':ok'],calls)
  for name in ('fn2-commit-directory-lookup','fn2-commit-root-physical-history','fn2-commit-root-physical-incarnation'):
   self.assertIn(name,str(f))
  self.assertNotIn('fn2-origin-history',str(f))
 def test_actual_live_and_recovery_producers_supply_the_pair(self):
  live=definition('commit.lisp','fn2-commit-prepare-root')
  recovery=definition('recovery-machine.lisp','fn2-recovery-link')
  self.assertIn(['fn2-commit-root-set-physical-history','physical',['fn2-origin-history','fn2-origin'],'fn2-commit-root'],list(walk(live)))
  self.assertIn(['fn2-commit-root-set-physical-incarnation','physical',['fn2-origin-history-incarnation','fn2-origin'],'fn2-commit-root'],list(walk(live)))
  self.assertIn(['fn2-rec-cand-history','p','fn2-rec-cand'],list(walk(recovery)))
  self.assertIn(['fn2-rec-cand-history-incarnation','p','fn2-rec-cand'],list(walk(recovery)))
 def test_reused_tag_cannot_publish_an_old_computed_seal(self):
  live=definition('commit.lisp','fn2-commit-prepare-root')
  reset=['fn2-commit-root-set-seal-ready','physical','0','fn2-commit-root']
  self.assertIn(reset,list(walk(live)))
  def has_reset(f):return reset in list(walk(f))
  from copy import deepcopy
  bad=deepcopy(live)
  def remove(n):
   if not isinstance(n,list):return n
   return ['fn2-commit-root'] if n==reset else [remove(x) for x in n]
  self.assertFalse(has_reset(remove(bad)))
if __name__=='__main__':unittest.main()
