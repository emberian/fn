import json
from pathlib import Path
import unittest
from run_loader_prefix_rewrite import project,RULES
from run_loader_room_rewrite import project as room_project
ROOT=Path(__file__).resolve().parents[1]
class Prefix(unittest.TestCase):
 def test_exact_named_projection(self):
  saved=json.loads((ROOT/'tools/fixtures/run-physical-park/prefix.json').read_text())
  for name in RULES:
   actual=(ROOT/'books'/name).read_text()
   expected=project(name,saved[name])
   if name=='run-physical-resources.lisp':expected=room_project(expected)
   self.assertEqual(expected,actual)
   with self.assertRaises(ValueError):project(name,actual)
 def test_initializer_uses_the_same_canonical_b_prefix(self):
  geometry=(ROOT/'books/run-physical-geometry.lisp').read_text()
  resource=(ROOT/'books/run-physical-resources.lisp').read_text()
  self.assertIn('(prefix (fn2-b-run-loader-row 0 profile))',geometry)
  self.assertIn('(fn2-run-load-checker-init 0 (fn2-b-run-loader-row 0 profile)',resource)
  self.assertIn('(<= 4 (fn2-b-run-loader-row 0 profile))',geometry)
  self.assertNotIn('(+ 4 (fn2-b-upload-windows profile))',geometry+resource)
 def test_lower_geometry_checks_hash_context_count(self):
  s=(ROOT/'books/run-physical-readiness.lisp').read_text()
  self.assertIn('(+ 4 (fn2-run-load-geometry-upload-hash-rows 0 fn2-run-load-geometry))',s)
  self.assertNotIn('fn2-run-load-geometry-uploads',s)
if __name__=='__main__':unittest.main()
