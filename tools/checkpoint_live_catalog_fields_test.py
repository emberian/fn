from pathlib import Path
import unittest
from checkpoint_live_catalog_fields import declarations,captures
ROOT=Path(__file__).resolve().parents[1]
class Capture(unittest.TestCase):
 def test_generated_words_equal_actual_source(self):
  state=(ROOT/'books/checkpoint-metadata-manifest-state.lisp').read_text()
  emit=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  self.assertIn(declarations(),state);self.assertIn(captures(),emit)
  self.assertEqual(declarations().count(':u32'),8)
  self.assertEqual(captures().count('fn2-checkpoint-page-verified-word'),8)
 def test_accepted_emit_is_atomic_capture_boundary(self):
  s=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  start=s.index('(defun fn2-checkpoint-metadata-manifest-emit ')
  end=s.index('(defun fn2-checkpoint-metadata-manifest-page ',start)
  s=s[start:end]
  pre=s.index('(fn2-checkpoint-metadata-manifest-emit-mv :catalog)')
  add=s.index('(fn2-run-build-add mb base')
  accepted=s.index('((unless (eq code :ok))',add)
  capture=s.index('(fn2-checkpoint-metadata-manifest-put extent',accepted)
  advance=s.index('(fn2-checkpoint-source-put 0',capture)
  self.assertLess(pre,add);self.assertLess(accepted,capture);self.assertLess(capture,advance)
  self.assertNotIn('((unless',s[capture:advance])
 def test_capture_disjoint_and_current(self):
  s=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  self.assertIn('(posp token)',s)
  self.assertIn('(not (equal (fn2-checkpoint-metadata-manifest-catalog-token extent fn2-checkpoint-metadata-manifest) token))',s)
  self.assertIn('(catalog-source-row (fn2-checkpoint-source-row 0 fn2-checkpoint-source))',s)
  self.assertIn('(catalog-source-order (fn2-checkpoint-source-order 0 fn2-checkpoint-source))',s)
 def test_actual_constructor_uses_whole_fresh_extent(self):
  m=(ROOT/'books/checkpoint-metadata.lisp').read_text()
  c=(ROOT/'books/checkpoint-construction-owner.lisp').read_text()
  self.assertIn('*fn2-run-page-size* fn2-csnapshot fn2-checkpoint-construction',m)
  self.assertIn('(fn2-run-build-page-kind b level slot gen (* extent *fn2-storage-extent-units*)',m)
  self.assertIn('(equal (fn2-checkpoint-construction-live next fn2-checkpoint-construction) 0)',c)
  self.assertIn('(equal (fn2-extents-state next fn2-extents) *fn2-extent-state-free*)',c)
  self.assertIn('(live 1) (token token)',c)
  geometry=(ROOT/'books/run-geometry.lisp').read_text()
  storage=(ROOT/'books/format-base.lisp').read_text()
  self.assertIn('(defconst *fn2-run-page-size* *fn2-format-page-size*)',geometry)
  self.assertIn('(defconst *fn2-storage-extent-bytes* *fn2-format-page-size*)',storage)
 def test_capacity_tracks_actual_extent_geometry(self):
  s=(ROOT/'books/checkpoint-metadata-resources.lisp').read_text()
  self.assertIn('(fn2-checkpoint-metadata-manifest-init (fn2-b-capacity :extent-slots 16 profile)',s)
if __name__=='__main__':unittest.main()
