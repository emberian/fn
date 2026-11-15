#!/usr/bin/env python3
"""Source completeness and real continuation cuts; not assertion execution."""
from pathlib import Path
import unittest,lisp_rewrite as lr
R=Path(__file__).resolve().parents[1]
class Provider(unittest.TestCase):
 def test_imported_provider_and_retained_assertion(self):
  s=(R/'tests/upload-source-lifetime-unit.lisp').read_text()
  self.assertIn('(include-book "manifest-binding-served-unit")',s)
  self.assertTrue((R/'tests/manifest-binding-served-unit.lisp').is_file())
  self.assertEqual(len(lr.match('(assert-event ?*body)',lr.parse(s).forms)),1)
  self.assertIn('(equal original (fn-blake3 source))',s)
  self.assertIn('(equal stored (fn-blake3 (append prefix source)))',s)
 def test_actual_cuts_and_no_obsolete_corruption(self):
  s=(R/'tests/upload-source-lifetime-unit.lisp').read_text()
  for word in ['*fn2-upload-state-stream-final*','*fn2-upload-state-stream-repack*','*fn2-upload-state-stream-root-write*',':root-reused','(eq stale-owner :fault)','(eq stale :fault)']:
   self.assertIn(word,s)
  for word in ['*fn2-upload-state-stored-hash*','*fn2-upload-state-location-hash*','fn2-upload-digest-at','fn2-upload-save-source','(fn2-upload-hash-begin']:
   self.assertNotIn(word,s)
 def test_registered_consumer_remains(self):
  s=(R/'tests/txn-retained-source-served-unit.lisp').read_text()
  self.assertIn('(include-book "upload-source-lifetime-unit")',s)
  self.assertEqual(len(lr.match('(assert-event ?*body)',lr.parse(s).forms)),1)
if __name__=='__main__':unittest.main()
