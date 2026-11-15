"""Source-only controls for actual typed terminal; no runtime result claim."""
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class Finish(unittest.TestCase):
 def test_actual_antecedents_precede_first_mutation(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  s=s[s.index('(defun fn2-checkpoint-live-replace-finish'):]
  write=s.index('(fn2-checkpoint-live-promote-evidence 0')
  for predicate in ('fn2-checkpoint-live-catalog-current-p','fn2-checkpoint-cbase-row-identity-p','fn2-c-source-writer-exclusive-p','fn2-checkpoint-summary-authority-row-current-p','fn2-run-load-readiness-live-complete-current-p'):
   self.assertLess(s.index('('+predicate+' '),write)
  self.assertIn('*fn2-checkpoint-summary-authority-phase-complete*',s[:write])
  self.assertIn('*fn2-checkpoint-summary-phase-retired*',s[:write])
  self.assertNotIn('((unless',s[write:])
 def test_reopen_preserves_monotone_endpoint_namespace(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  clear=s[s.index('(fn2-c-source-control (fn2-c-source-control-put 0'):]
  for field in ('next-receipt','readers'):
   self.assertNotIn('('+field+' ',clear)
  self.assertNotIn('fn2-c-source-readers-put',s)
  self.assertIn('(wake-pending 0)',clear)
  self.assertNotIn('writer-end',s)
 def test_no_new_resources_and_wire_identity_preserved(self):
  s=(ROOT/'books/checkpoint-live-finish.lisp').read_text()
  for forbidden in ('pool-reserve','block-read','run-installed-put','run-installed-set-wire-run'):
   self.assertNotIn(forbidden,s)
  self.assertIn('(+ *fn2-event-frontier-bytes* (* 3 *fn2-commit-digest-bytes*))',s)
  self.assertIn('(published (max (fn2-id-engine-published',s)
 def test_connected_actual_fixture(self):
  s=(ROOT/'tests/checkpoint-live-finish-unit.lisp').read_text()
  for call in ('fn2-clc-body :positive','fn2-checkpoint-summary-authority-live-begin-op','fn2-checkpoint-summary-authority-live-step-op','fn2-run-load-readiness-live-begin-op','fn2-run-load-readiness-owned-step','fn2-checkpoint-live-replace-finish-op'):
   self.assertIn('('+call,s)
  self.assertIn('(eq refused :source) (equal before (fn2-clf-snapshot fn2-core))',s)
  self.assertNotIn('-put ',s)
if __name__=='__main__':unittest.main()
