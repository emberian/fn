"""Source controls only: actual compaction producer/hook fixture is owed."""
from pathlib import Path
import unittest
from checkpoint_live_old_identity import FIELDS
ROOT=Path(__file__).resolve().parents[1]
class Inventory(unittest.TestCase):
 def test_every_actual_original_identity_retained(self):
  s=(ROOT/'books/checkpoint-predecessors.lisp').read_text()
  for field,_ in FIELDS:
   self.assertIn('(old-'+field+' (if (= kind 0)',s)
   actual={'allocation':'counter','tag':'catalog-tag'}.get(field,field)
   self.assertIn('(fn2-run-installed-'+actual+' r fn2-run-installed)',s)
  self.assertIn('(fn2-checkpoint-compaction-source-tuple kind r fn2-overlays fn2-run-installed)',s)
 def test_source_key_is_atomic_once(self):
  s=(ROOT/'books/checkpoint-predecessors.lisp').read_text()
  b=s[s.index('(defun fn2-checkpoint-predecessor-source-key'):s.index('(defun fn2-checkpoint-predecessor-source-end')]
  self.assertIn('*fn2-checkpoint-compaction-phase-equal-lower*',b)
  self.assertIn('(< (fn2-checkpoint-predecessors-last-round i fn2-checkpoint-predecessors) round)',b)
  self.assertLess(b.index('(< (fn2-checkpoint-predecessors-seen'),b.index('(seen (+ 1'))
  self.assertLess(b.index('(seen (+ 1'),b.index('*fn2-checkpoint-compaction-phase-seek*'))
  self.assertNotIn('((unless',b[b.index('(seen (+ 1'):])
 def test_end_and_complete_enforce_original_count(self):
  s=(ROOT/'books/checkpoint-predecessors.lisp').read_text()
  b=s[s.index('(defun fn2-checkpoint-predecessor-source-end'):]
  self.assertIn('(= (fn2-checkpoint-predecessors-seen i fn2-checkpoint-predecessors) (fn2-checkpoint-predecessors-old-entries i fn2-checkpoint-predecessors))',b)
  self.assertIn('*fn2-checkpoint-compaction-phase-park*',b)
  self.assertIn('(iff live owned)',b)
  self.assertIn('(posp (fn2-checkpoint-predecessors-output-rank i fn2-checkpoint-predecessors))',b)
 def test_geometry_has_all_rows_and_no_fixed_source_count(self):
  s=(ROOT/'books/checkpoint-metadata-resources.lisp').read_text()
  for field in (':identity-overlays',':identity-runs',':extent-slots'):
   self.assertIn(field,s[s.index('(defun fn2-checkpoint-predecessor-rows'):])
  self.assertIn(':profilep (fn2-checkpoint-predecessor-profilep profile)',s)
  self.assertIn('(unsigned-byte-p 32 (fn2-checkpoint-predecessor-rows profile))',s)
  for child in ('checkpoint-predecessors','checkpoint-predecessor-control','checkpoint-compaction'):
   self.assertIn('fn2-core-'+child,s)
  lower=(ROOT/'books/checkpoint-predecessors.lisp').read_text()
  self.assertNotIn('(< count 8)',lower)
  self.assertNotIn('fn2-alloc-free',lower)
 def test_empty_obligations_are_retained_until_actual_end(self):
  s=(ROOT/'books/checkpoint-predecessors.lisp').read_text()
  capture=s[s.index('(defun fn2-checkpoint-predecessor-capture-step'):s.index('(defun fn2-checkpoint-predecessor-empty-next')]
  self.assertIn('(semantic-live (if semantic 1 0))',capture)
  self.assertIn('(empty-verified 0)',capture)
  self.assertIn('(ended 0)',capture)
  self.assertIn('(mv :captured',capture)
  end=s[s.index('(defun fn2-checkpoint-predecessor-empty-end'):s.index('(defun fn2-checkpoint-predecessor-source-key')]
  self.assertIn('*fn2-checkpoint-compaction-phase-empty-end*',end)
  self.assertIn('(posp (fn2-checkpoint-compaction-empty-headers',end)
  self.assertIn('(ended 1) (empty-verified 1) (output-rank 0)',end)
  self.assertNotIn('output-rank rank',end)
if __name__=='__main__':unittest.main()
