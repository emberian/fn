from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class Install(unittest.TestCase):
 def setUp(self):self.s=(ROOT/'books/checkpoint-live-install.lisp').read_text()
 def test_each_step_requires_actual_subject_and_exclusive(self):
  self.assertIn('(fn2-checkpoint-live-catalog-current-p ',self.s)
  self.assertIn('(fn2-checkpoint-cbase-row-identity-p 1 ',self.s)
  self.assertIn('(fn2-c-source-writer-exclusive-p ',self.s)
  self.assertIn(':promised-read fn2-alloc-edges)',self.s)
  self.assertNotIn('verifiedp',self.s)
 def test_existing_transition_then_receipt_no_soft_failure_gap(self):
  p=self.s.index('(fn2-run-install-physical r ')
  refusal=self.s.index('((unless (eq code :ok))',p)
  receipt=self.s.index('(fn2-checkpoint-metadata-manifest-put i (catalog-installed-tag tag)',refusal)
  advance=self.s.index('(cursor (+ 1 i)) (target 0) (installed count)',receipt)
  self.assertLess(refusal,receipt);self.assertLess(receipt,advance)
  self.assertNotIn('((unless',self.s[receipt:advance])
 def test_one_probe_per_turn_and_priority_before_install(self):
  self.assertIn('(fn2-checkpoint-summary-set-target 1 (+ 1 r)',self.s)
  self.assertIn('(fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-free-count 1 fn2-checkpoint-summary)',self.s)
  self.assertIn('(fn2-run-installed-run i fn2-run-installed)',self.s)
 def test_no_old_release_or_reopen(self):
  for x in ['fn2-run-retire','fn2-seal-release-row','fn2-pool-release','update-fn2-c-source-control-next-receipt','fn2-c-source-control-put']:
   self.assertNotIn('('+x+' ',self.s)
  self.assertNotIn('phase-applied*',self.s)
 def test_real_installed_check_includes_full_reference(self):
  for f in ['schema','wire-run','top','entries','unit','epoch','counter','hash-0','hash-7']:
   self.assertIn('(fn2-run-installed-'+f+' r fn2-run-installed)',self.s)
if __name__=='__main__':unittest.main()
