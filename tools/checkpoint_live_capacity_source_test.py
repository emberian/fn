from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class Capacity(unittest.TestCase):
 def test_counts_same_actual_selector(self):
  selector=(ROOT/'books/checkpoint-metadata-source.lisp').read_text()
  fit=(ROOT/'books/checkpoint-live-capacity.lisp').read_text()
  for p in ['fn2-checkpoint-source-overlay-p row fn2-overlays','fn2-checkpoint-source-run-p row fn2-run-installed']:
   self.assertIn('('+p+')',selector);self.assertIn('('+p+')',fit)
 def test_real_master_checks_before_resources_or_writes(self):
  s=(ROOT/'books/checkpoint-master-arms.lisp').read_text()
  self.assertIn('(fit-sources 0) (fit-free 0)) (:next :source-fit-overlays)',s)
  start=s.index('  (:source-fit-runs ');end=s.index('  (:directory ',start);body=s[start:end]
  self.assertIn('((:fit)',body);self.assertIn('(:next :reserve)',body)
  self.assertIn('((:no-space :exhausted) (:next :abort-empty)',body)
  self.assertNotIn(':acquire',body)
  abort=s[s.index('  (:abort-empty '):s.index('  (:abort-snapshot ')]
  self.assertIn('fn2-checkpoint-master-abort-empty-ready-op',abort)
  self.assertIn('fn2-csnapshot-release row-token',abort)
 def test_only_resource_demand_changes_at_exact_eof(self):
  s=(ROOT/'books/checkpoint-live-capacity.lisp').read_text()
  self.assertEqual(s.count('(update-'),1)
  self.assertIn('((= row (fn2-run-installed-rows fn2-run-installed))',s)
  self.assertIn('(if (< free sources) sources 0)',s)
  for op in ['fn2-run-install','fn2-run-retire','fn2-pool-release','fn2-alloc-free']:
   self.assertNotIn('('+op+' ',s)
 def test_existing_sealer_grant_observes_demand_after_cut_release(self):
  s=(ROOT/'books/sealer.lisp').read_text()
  self.assertIn('(< free (fn2-run-installed-adoption-demand fn2-run-installed))',s)
  grant=(ROOT/'books/machines-c-sealer-events.lisp').read_text()
  self.assertIn('(fn2-seal-compact-pending-p fn2-seals fn2-run-installed fn2-pool)',grant)
  self.assertIn('(not (equal (mv-nth 0 (fn2-csnapshot-state fn2-core)) *fn2-csnapshot-phase-held*))',grant)
 def test_profile_geometry_not_stored_history_bound(self):
  s=(ROOT/'books/checkpoint-live-capacity.lisp').read_text()
  self.assertIn('(< row (fn2-overlays-rows fn2-overlays))',s)
  self.assertIn('(< row (fn2-run-installed-rows fn2-run-installed))',s)
  self.assertNotIn(' 64',s);self.assertNotIn(' 36',s)
if __name__=='__main__':unittest.main()
