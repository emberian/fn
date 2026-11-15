"""Actual source-only inactive-bank delegation and scoped master rewrite."""
from pathlib import Path
import json
import unittest
import lisp_rewrite as lr
import checkpoint_bank_fit_rewrite as change
ROOT=Path(__file__).resolve().parents[1]
class Capacity(unittest.TestCase):
 def test_only_canonical_retained_scan(self):
  s=(ROOT/'books/checkpoint-live-capacity.lisp').read_text()
  self.assertIn('(fn2-checkpoint-bank-admission-ready-p token kind owner generation',s)
  for child in ('fn2-checkpoint-bank-admission-begin','fn2-checkpoint-bank-admission-step'):
   self.assertIn(':child '+child,s)
  for forbidden in ('update-','sources free','section row','fn2-checkpoint-source-overlay','fn2-checkpoint-source-run','adoption-demand','fn2-pool-reserve','fn2-run-install'):
   # run-installed type/getter is a required readonly input, not run-install.
   self.assertNotIn(forbidden+' ' if forbidden=='fn2-run-install' else forbidden,s)
 def test_master_admits_before_reserve_and_releases_cut_on_shortage(self):
  s=(ROOT/'books/checkpoint-master-arms.lisp').read_text()
  body=s[s.index('  (:source-fit-overlays '):s.index('  (:directory ')]
  self.assertLess(body.index('(fn2-checkpoint-live-bank-begin-op'),body.index('(fn2-checkpoint-live-bank-step-op'))
  self.assertLess(body.index('(fn2-checkpoint-live-bank-step-op'),body.index('(fn2-checkpoint-live-fit-step-op'))
  self.assertIn('((:fit) (:next :reserve)',body)
  self.assertIn('((:resources) (:next :abort-empty)',body)
  self.assertNotIn(':acquire',body)
  abort=s[s.index('  (:abort-empty '):s.index('  (:abort-snapshot ')]
  self.assertIn('fn2-checkpoint-master-abort-empty-ready-op',abort)
  self.assertIn('fn2-csnapshot-release row-token',abort)
 def test_exact_two_arm_scope_idempotent(self):
  before=json.loads((ROOT/'tools/fixtures/checkpoint-bank-fit-before.json').read_text())['source_fit_arms']
  wrapper='(defmachine-arms fn2-checkpoint-master :declare :arms ('+before+' (:foreign (keep (x y)))))'
  after=change.transform(wrapper)
  self.assertIn('(:foreign (keep (x y)))',after)
  self.assertEqual(change.transform(after),after)
  self.assertNotIn('row-fit-sources',after)
  with self.assertRaises(ValueError):change.transform(wrapper.replace('(:source-fit-runs :on-refusal','(:missing :on-refusal',1))
 def test_retained_receipt_has_exact_real_identity(self):
  s=(ROOT/'books/checkpoint-bank-admission.lisp').read_text()
  for field in ('cut-commit','cut-event','active-phase','active-tag','active-bank','resident-limit','bank-capacity'):
   self.assertIn('fn2-checkpoint-bank-admission-'+field,s)
  self.assertIn('fn2-checkpoint-bank-admission-ready-p',s)
  self.assertIn('(fn2-run-installed-physical r fn2-run-installed) 0',s)
if __name__=='__main__':unittest.main()
