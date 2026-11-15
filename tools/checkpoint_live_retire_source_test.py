"""Source-only controls; real publication/release fixture remains unexecuted."""
from pathlib import Path
import unittest
from checkpoint_live_old_identity import FIELDS
ROOT=Path(__file__).resolve().parents[1]
class Retire(unittest.TestCase):
 def test_full_original_run_identity(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  for field,_ in FIELDS:
   actual={'allocation':'counter','tag':'catalog-tag'}.get(field,field)
   self.assertIn(f'(= (fn2-run-installed-{actual} r fn2-run-installed) (fn2-checkpoint-metadata-manifest-catalog-old-{field} e fn2-checkpoint-metadata-manifest))',s)
 def test_actual_source_and_exclusion_before_effects(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  step=s[s.index('(defun fn2-checkpoint-live-replace-retire-step'):]
  for required in ('fn2-checkpoint-live-catalog-current-p','fn2-checkpoint-cbase-row-identity-p','fn2-c-source-writer-exclusive-p'):
   self.assertLess(step.index('('+required+' '),step.index('(fn2-ov-freeze '))
  self.assertLess(step.index('(fn2-checkpoint-live-installed-p '),step.index('(fn2-ov-freeze '))
 def test_shared_release_only_transitions(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  for call in ('fn2-ov-freeze','fn2-seal-retire','fn2-run-retire','fn2-seal-release-row','fn2-checkpoint-summary-row-retire-row','fn2-checkpoint-cbase-row-release-step'):
   self.assertIn('('+call+' ',s)
  for forbidden in ('fn2-pool-reserve','fn2-alloc-free','fn2-block-read','phase-applied','phase-idle*) (writer'):
   self.assertNotIn(forbidden,s)
 def test_source_constructor_resets_retire_receipt(self):
  s=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  self.assertIn('(catalog-old-stage 0) (catalog-installed-tag 0)',s)
  fixture=(ROOT/'tests/checkpoint-live-catalog-unit.lisp').read_text()
  self.assertIn('(fn2-clc-retire-drain 100000 0 fn2-core)',fixture)
  self.assertIn('(eq retired :resources) (posp retire-progress) retained',fixture)
 def test_canonical_credited_arena_return_uses_actual_B_geometry(self):
  s=(ROOT/'books/checkpoint-live-retire.lisp').read_text()
  self.assertIn('(fn2-seal-retire (fn2-commit-rows fn2-commit) r fn2-overlays fn2-pool)',s)
  self.assertIn('fn2-core-commit)',s)
  self.assertNotIn('(fn2-idc-arena-return',s)
  self.assertNotIn('(fn2-pool-release ',s)
if __name__=='__main__':unittest.main()
