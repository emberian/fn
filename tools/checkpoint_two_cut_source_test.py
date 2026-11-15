"""Source-only controls; multi-generation and DELETE runtime remain unexecuted."""
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class TwoCut(unittest.TestCase):
 def test_real_start_transport_cleanup(self):
  s=(ROOT/'tests/checkpoint-live-two-cut-support.lisp').read_text()
  for p in ('fn2-cln-prefix-to-held','fn2-clc-published-held-p','fn2-clc-full-live-source-p','fn2-cln-pump','fn2-ccp-live-complete-p'):
   self.assertIn('('+p+' ',s)
  self.assertIn('(fn2-cln-pump nil cap',s)
 def test_complete_observes_actual_combined_terminal(self):
  s=(ROOT/'tests/checkpoint-live-two-cut-support.lisp').read_text()
  for p in ('fn2-checkpoint-cbase-row-promised-p','fn2-checkpoint-summary-authority-row-complete-p','fn2-alloc-freeze-phase','fn2-csnapshot-phase','fn2-c-source-control-phase'):
   self.assertIn('('+p+' ',s)
  self.assertIn('*fn2-checkpoint-summary-phase-applied*',s)
  self.assertIn('*fn2-checkpoint-summary-authority-phase-idle*',s)
 def test_no_state_seed_or_deletion_substitute(self):
  s=(ROOT/'tests/checkpoint-live-two-cut-support.lisp').read_text()
  for p in ('-put ','update-fn2-','fn2-successor-put','fn2-icu-withdraw','fn2-commit-admit','fn2-core-init'):
   self.assertNotIn(p,s)
  self.assertIn('DELETE producer is not present',s)
 def test_next_cut_requires_actual_previous_catalog_and_new_publication(self):
  s=(ROOT/'tests/checkpoint-live-two-cut-support.lisp').read_text()
  next=s[s.index('(defun fn2-clt-next-held'):]
  self.assertLess(next.index('(fn2-clt-completed-p checkpoint'),next.index('(fn2-clc-prefix-to-held '))
  self.assertIn('(< checkpoint next)',next)
  self.assertIn('(fn2-clc-full-live-source-p fn2-core)',next)
if __name__=='__main__':unittest.main()
