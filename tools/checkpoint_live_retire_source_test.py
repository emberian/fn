"""Source controls; actual compacted producer/runtime fixtures remain owed."""
from pathlib import Path
import unittest
from checkpoint_live_old_identity import FIELDS
ROOT=Path(__file__).resolve().parents[1]
class Retire(unittest.TestCase):
 def test_original_inventory_not_one_old_per_output(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  self.assertIn('(fn2-checkpoint-predecessor-identity-p i',s)
  self.assertIn('(fn2-checkpoint-predecessors-row i',s)
  self.assertNotIn('catalog-old-',s)
  self.assertNotIn('catalog-source-row',s)
  for field,_ in FIELDS:
   if field=='ufirst':continue
   actual={'allocation':'counter','tag':'catalog-tag'}.get(field,field)
   self.assertIn(f'(= (fn2-run-installed-{actual} r fn2-run-installed) (fn2-checkpoint-predecessors-old-{field} i fn2-checkpoint-predecessors))',s)
 def test_one_mapping_scan_direct_rank_lookup(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  self.assertIn('*fn2-checkpoint-predecessor-phase-mapping*',s)
  self.assertIn('(root-token token) (root-extent i)',s)
  self.assertIn('(at (if (posp rank) (- rank 1) n))',s)
  self.assertIn('(fn2-checkpoint-predecessors-root-extent at',s)
  self.assertIn('(not (= (fn2-checkpoint-predecessors-root-token at',s)
 def test_actual_durable_gate_before_shared_release(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text();s=s[s.index('(defun fn2-checkpoint-live-replace-retire-step'):]
  for p in ('fn2-checkpoint-live-catalog-current-p','fn2-checkpoint-cbase-row-identity-p','fn2-c-source-writer-exclusive-p','fn2-checkpoint-source-reader-detachedp'):
   self.assertLess(s.index('('+p+' '),s.index('(fn2-ov-freeze '))
  for call in ('fn2-ov-freeze','fn2-seal-retire','fn2-run-retire','fn2-seal-release-row','fn2-checkpoint-summary-row-retire-row','fn2-checkpoint-cbase-row-release-step'):
   self.assertIn('('+call+' ',s)
  self.assertNotIn('(fn2-pool-release ',s);self.assertNotIn('(fn2-alloc-free ',s)
 def test_actual_B_geometry_and_empty_proof_no_fake_root(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  self.assertIn('(fn2-seal-retire (fn2-commit-rows fn2-commit) r fn2-overlays fn2-pool)',s)
  self.assertIn('fn2-core-commit ',s)
  self.assertIn('(= (fn2-checkpoint-predecessors-empty-verified i fn2-checkpoint-predecessors) 1)',s)
  self.assertIn('(and (= rank 0) (= (fn2-checkpoint-predecessors-old-entries',s)
 def test_no_done_before_old_base_drain(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  tail=s[s.index('((= stage *fn2-live-replace-stage-old-base*)'):]
  self.assertLess(tail.index('(fn2-checkpoint-cbase-row-release-step'),tail.index('*fn2-checkpoint-predecessor-phase-done*'))
  self.assertIn('((unless (eq code :released))',tail)
if __name__=='__main__':unittest.main()
