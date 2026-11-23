#!/usr/bin/env python3
"""Actual producer/consumer source mapping for the raw commitment threshold."""
from pathlib import Path
import subprocess
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def matches(file,pattern): return lr.match(pattern,lr.parse(ROOT/file).forms)
class RawThreshold(unittest.TestCase):
 def test_derived_actual_raw_span(self):
  self.assertEqual(len(matches('books/upload-kind.lisp','(defconst *fn2-upload-raw-bytes* (* *fn2-commit-write-resources* *fn2-commit-unit-bytes*))')),1)
  self.assertEqual(len(matches('books/article-manifest.lisp','(defun fn2-am-manifestp (total) ?declare (< *fn2-upload-raw-bytes* (nfix total)))')),1)
  self.assertEqual(len(matches('books/ordered.lisp','(defconst *fn2-article-location-hashes-max* (* 32 *fn2-commit-write-resources*))')),1)
  self.assertTrue(matches('books/upload.lisp','(< unit *fn2-commit-write-resources*)'))
 def test_same_predicate_connects_actual_consumers(self):
  for f,name in [('books/upload.lisp','fn2-upload-page-bytes'),('books/txn.lisp','fn2-txn-put-article'),
                 ('books/recovery-payload.lisp','fn2-recovery-manifest-unit')]:
   ms=matches(f,'(defun '+name+' ?*body)');self.assertEqual(len(ms),1)
   self.assertTrue(lr.match('(fn2-am-manifestp ?n)',[ms[0].node]),name)
  self.assertTrue(matches('books/assembly-callbacks-d-upload.lisp','(fn2-am-manifestp total)'))
 def test_admission_bound_unchanged(self):
  old=subprocess.check_output(['git','show','dfc12386f:books/upload.lisp'],cwd=ROOT,text=True)
  before=lr.parse(old);after=lr.parse(ROOT/'books/upload.lisp')
  for name in ['fn2-upload-bound','fn2-upload-input-bound']:
   a=lr.match('(defun '+name+' ?*body)',before.forms);b=lr.match('(defun '+name+' ?*body)',after.forms)
   self.assertEqual(len(a),len(b))
   if a: self.assertEqual(old[a[0].start:a[0].end],after.text[b[0].start:b[0].end])
  self.assertTrue(matches('tests/upload-raw-threshold-unit.lisp','(fn2-urt-constructor 32768 fn2-core)'))
if __name__=='__main__':unittest.main()
