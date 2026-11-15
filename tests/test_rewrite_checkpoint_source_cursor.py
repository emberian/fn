#!/usr/bin/env python3
"""Private source-selector class controls; no ACL2 evaluation."""
from pathlib import Path
import sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from rewrite_checkpoint_source_cursor import transform
class SourceCursor(unittest.TestCase):
 def test_actual_accessor_class_and_idempotence(self):
  old='(let ((c (- (fn2-run-loads-rows fn2-run-loads) 1)) (d (- (fn2-run-cursors-rows fn2-run-cursors) 1))) (mv c d))'
  new,n=transform(old);self.assertEqual(n,2);self.assertEqual(new.count('fn2-b-checkpoint-source-cursor-from-rows'),2)
  self.assertEqual(transform(new),(new,0))
 def test_foreign_row_geometry_untouched(self):
  old='(let ((c (- (fn2-run-paths-rows fn2-run-paths) 1)) (d (- rows 1))) (mv c d))'
  self.assertEqual(transform(old),(old,0))
 def test_two_private_tail_rows_exist_before_named_selection(self):
  new,n=transform('(< 0 (fn2-run-loads-rows fn2-run-loads))')
  self.assertEqual((new,n),('(<= 2 (fn2-run-loads-rows fn2-run-loads))',1))
  self.assertEqual(transform(new),(new,0))
 def test_fixture_mode_is_explicit(self):
  self.assertEqual(transform('(- rows 1)',True),('(fn2-b-checkpoint-source-cursor-from-rows rows)',1))
if __name__=='__main__':unittest.main()
