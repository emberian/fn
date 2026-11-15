#!/usr/bin/env python3
"""Check the geometry change is one appended cursor, not a source-row move."""
import unittest
from pathlib import Path
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
S=(ROOT/'books/machines-b.lisp').read_text()
def body(name):return lr.match('(defun '+name+' ?*body)',lr.parse(S).forms,deep=False)[0].node.items[-1]
def tree(n):return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
class ArchiveGeometry(unittest.TestCase):
 def test_original_source_formula_and_appended_archive(self):
  self.assertEqual(tree(body('fn2-b-checkpoint-source-cursor')),
   ('+',('nfix',('fn2-profile-t','profile')),('*',('+','1','*fn2-b-range-source-cursors*'),('fn2-b-read-rows','profile')),'*fn2-b-seal-source-cursors*'))
  self.assertEqual(tree(body('fn2-b-event-archive-cursor')),('+','1',('fn2-b-checkpoint-source-cursor','profile')))
  self.assertEqual(tree(body('fn2-b-run-cursor-rows')),('+','1',('fn2-b-event-archive-cursor','profile')))
 def test_bridges_and_named_profile_equalities(self):
  for stem,n in [('checkpoint-source','2'),('event-archive','1')]:
   self.assertEqual(tree(body('fn2-b-'+stem+'-cursor-from-rows')),('nfix',('-',('nfix','rows'),n)))
   t=lr.match('(defthm fn2-b-'+stem+'-cursor-from-profile-rows ?*body)',lr.parse(S).forms,deep=False)[0].node
   self.assertEqual(tree(t.items[2]),('equal',('fn2-b-'+stem+'-cursor-from-rows',('fn2-b-run-cursor-rows','profile')),('fn2-b-'+stem+'-cursor','profile')))
 def test_all_cursor_carriers_and_checkers_share_K(self):
  for p,name in [('machines-c.lisp','fn2-run-cursors-init'),('run-physical-resources.lisp','fn2-run-loads-init'),('machines-c.lisp','fn2-checkpoint-summary-leases-init')]:
   s=(ROOT/'books'/p).read_text()
   calls=lr.match('('+name+' ?*args)',lr.parse(s).forms)
   self.assertTrue(any(tree(c.node.items[1])==('fn2-b-run-cursor-rows','profile') for c in calls))
  self.assertIn('(+ 9 (fn2-b-upload-windows profile) (fn2-b-run-cursor-rows profile) (fn2-b-ctl-rows profile))',S)
if __name__=='__main__':unittest.main()
