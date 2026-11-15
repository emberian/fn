"""Source binding of the actual E lifecycle, not execution or authority proof."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def source(name):return (ROOT/'books'/name).read_text()
def function(name,fn):
 return next(n for f in forms(source(name)) for n in walk(read_sexp(f)) if n[:2]==['defun',fn])
class EvidenceLifecycle(unittest.TestCase):
 def test_one_mapping_stores_and_matches_original_record_tuple(self):
  s=source('release-evidence.lisp')
  mapping=next(read_sexp(f)[2][1] for f in forms(s) if read_sexp(f)[:2]==['defconst','*fn2-release-evidence-inventory-bindings*'])
  self.assertEqual([r[0] for r in mapping],['journal-history','journal-incarnation','event','extent','epoch','allocation','retirement','installation-history','installation-incarnation','installation-extent','installation-epoch','installation-allocation'])
  self.assertIn('fn2-release-evidence-inventory-matches',str(function('release-evidence.lisp','fn2-release-evidence-row-matches')))
  self.assertIn('fn2-release-evidence-inventory-put',str(function('release-evidence.lisp','fn2-release-evidence-claim-transition')))
  self.assertIn('fn2-release-evidence-inventory-put-forms *fn2-release-evidence-inventory-bindings*',s)
 def test_actual_live_and_cold_sources_stamp_persisted_after_authentication(self):
  live=function('allocation-release-coordinator.lisp','fn2-allocation-release-install-member')
  cold=function('recovery-release.lisp','fn2-rp-release-own-evidence')
  for f in (live,cold):self.assertIn('fn2-release-evidence-mark-persisted',str(f))
  for name in ('fn2-machine-cb-fence-ok','fn2-release-member-fields-match-p'):
   self.assertIn(name,str(live))
  self.assertIn('fn2-allocation-release-installation-matches',str(cold))
  stamp=function('release-evidence.lisp','fn2-release-evidence-mark-persisted')
  self.assertIn(['=',['fn2-release-evidence-phase','journal','fn2-release-evidence'],'*fn2-release-evidence-phase-claimed*'],list(walk(stamp)))
  self.assertIn('fn2-release-evidence-row-matches',str(stamp))
 def test_original_namespaces_come_from_actual_sources(self):
  live=function('allocation-release-coordinator.lisp','fn2-release-live-claim')
  self.assertIn('fn2-origin-history-incarnation',str(live))
  staged=function('release-evidence.lisp','fn2-release-evidence-claim-children')
  self.assertIn('fn2-commit-directory-physical-source',str(staged))
  cold=function('recovery-release.lisp','fn2-rp-release-own-evidence')
  self.assertIn('fn2-allocation-release-replay-history',str(cold))
  self.assertIn('fn2-allocation-release-replay-incarnation',str(cold))
if __name__=='__main__':unittest.main()
