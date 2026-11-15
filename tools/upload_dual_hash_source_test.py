#!/usr/bin/env python3
"""Paired actual upload/sealer consumers of the authoritative B hash map."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def function(file,name):
 p=lr.parse(ROOT/file);ms=lr.match('(defun '+name+' ?*body)',p.forms)
 if len(ms)!=1:raise AssertionError((name,len(ms)))
 return p.text[ms[0].start:ms[0].end],ms[0].node
class DualHash(unittest.TestCase):
 def test_actual_paired_selectors(self):
  for name,helper in [('fn2-upload-hasher','fn2-b-upload-source-hash-row'),
                      ('fn2-upload-stored-hasher','fn2-b-upload-stored-hash-row')]:
   text,node=function('books/upload.lisp',name)
   self.assertTrue(lr.match('('+helper+' (fn2-machine-slot id fn2-core))',[node]))
   self.assertIn('fn2-upload-snapshot-read-code',text)
  text,node=function('books/machines-c-sealer.lisp','fn2-seal-genesis')
  self.assertTrue(lr.match('(crow (fn2-b-sealer-hash-row profile))',[node]))
 def test_stored_arm_selects_its_context(self):
  text=(ROOT/'books/upload-stream-stage.lisp').read_text()
  self.assertIn('(fn2-upload-stored-hasher id fn2-core)',text)
  self.assertIn('(fn2-upload-stored-hash hrow',text)
  self.assertNotIn('(fn2-upload-hasher id fn2-core)',text)
 def test_block_hash_copies_atomic_scratch(self):
  text,node=function('books/upload.lisp','fn2-upload-block-hash')
  for piece in ['fn2-b-block-read-row','fn2-block-hash-into','fn2-digest-store','*fn2-upload-page-hash*']:
   self.assertIn(piece,text)
  self.assertLess(text.index('fn2-block-hash-into'),text.index('fn2-digest-store'))
  self.assertNotIn('(row ls lg',text)
  self.assertFalse(lr.match('(defun fn2-upload-block-hash-run ?*body)',lr.parse(ROOT/'books/upload.lisp').forms))
 def test_short_cv_does_not_read_scratch_after_yield(self):
  text,node=function('books/upload.lisp','fn2-upload-block-cv')
  short=lr.match('(if (not (equal blen *fn2-commit-unit-bytes*)) ?short ?full)',[node])
  self.assertEqual(len(short),1)
  branch=short[0].captures['short'];b=lr.parse(ROOT/'books/upload.lisp').text[branch.start:branch.end]
  self.assertIn('fn2-core-copy-range',b)
  self.assertNotIn('fn2-digest',b)
  self.assertNotIn('fn2-b3',b)
  self.assertIn('fn2-b3-subtree-cv-into',text)
 def test_new_arm_operand_has_cost(self):
  p=lr.parse(ROOT/'books/upload.lisp')
  self.assertEqual(len(lr.match('(defcost fn2-upload-stored-hasher ?*body)',p.forms)),1)
  text=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  self.assertNotIn('(fn2-upload-block-hash hrow',text)
  self.assertNotIn('(fn2-upload-block-cv hrow',text)
if __name__=='__main__':unittest.main()
