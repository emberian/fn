#!/usr/bin/env python3
"""Actual source producer/manifest consumer wiring; no ACL2 execution."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def form(file,head,name):
 p=lr.parse(ROOT/file);m=lr.match('('+head+' '+name+' ?*body)',p.forms)
 if len(m)!=1:raise AssertionError((file,name,len(m)))
 return p.text[m[0].start:m[0].end],m[0].node
class SourceLifetime(unittest.TestCase):
 def test_same_reserved_digest_area(self):
  s,_=form('books/upload.lisp','defconst','*fn2-upload-page-source*')
  self.assertIn('(+ *fn2-upload-page-stored-source* *fn2-upload-digest-octets*)',s)
  s,_=form('books/upload.lisp','defconst','*fn2-upload-page-location-hashes*')
  self.assertIn('(+ *fn2-upload-page-stored-source* 64)',s)
 def test_actual_owner_and_transition(self):
  s,_=form('books/upload.lisp','defun','fn2-upload-save-source')
  for piece in ['fn2-upload-snapshot-read-code','fn2-machine-generation','*fn2-upload-state-stored-hash*',
                '(equal (fn2-upload-row-mstep id fn2-core) 1)',
                '(equal (fn2-upload-row-stored-hashed id fn2-core) 0)',
                '*fn2-upload-lease-held*','fn2-core-copy-range','*fn2-upload-page-source*']:
   self.assertIn(piece,s)
  source=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  a=source.index('(:stored-hash :on-refusal');b=source.index('(:location-hash :on-refusal',a);s=source[a:b]
  self.assertLess(s.index('fn2-upload-save-source'),s.index('fn2-upload-stored-hash'))
  self.assertIn('(mstep (if (equal done total) 0 2))',s)
 def test_manifest_reads_retained_source(self):
  s,node=form('books/upload.lisp','defun','fn2-upload-manifest-begin')
  self.assertIn('total ls lg *fn2-upload-page-source*',s)
  self.assertNotIn('fn2-upload-digest-at',s)
  self.assertNotIn('c0',s)
  self.assertTrue(lr.match('(fn2-am-put-header ?*args)',[node]))
 def test_real_control_preserves_accept_cursor(self):
  s,_=form('tests/upload-source-lifetime-unit.lisp','defun','fn2-uslt-await')
  self.assertIn('(fn2-cw-adapter-one accepted clients store fn2-core)',s)
  self.assertIn('(fn2-uslt-await (- fuel 1) target accepted clients store fn2-core)',s)
if __name__=='__main__':unittest.main()
