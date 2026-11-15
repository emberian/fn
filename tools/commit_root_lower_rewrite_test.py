#!/usr/bin/env python3
"""Declaration identity and honest source-order controls, not ACL2 admission."""
import unittest
from pathlib import Path
import lisp_rewrite as lr
import commit_root_lower_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def pick(s,p):return lr.match(p,lr.parse(s).forms,deep=False)[0].node
def tree(n):return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
class CommitRootLower(unittest.TestCase):
 def test_actual_declaration_is_preserved_exactly(self):
  old=read('tools/fixtures/commit-root-lower-machines.lisp')
  machines,directory,lower=rw.transform(old,'(include-book "machines-b")\n(defun untouched () 1)\n')
  p='(defcolumns fn2-commit-root ?*body)'
  self.assertEqual(tree(pick(old,p)),tree(pick(lower,p)))
  self.assertEqual(tree(pick(lower,p)),tree(pick(read('books/commit-root-state.lisp'),p)))
  self.assertFalse(lr.match(p,lr.parse(machines).forms,deep=False))
  for name in ('before','after'):self.assertIn('*unrelated-'+name+'*',machines)
  self.assertIn('(defun untouched () 1)',directory)
 def test_future_fields_are_preserved(self):
  old=read('tools/fixtures/commit-root-lower-machines.lisp').replace('((installed :u60)','((future-field :u60) (installed :u60)')
  _,_,lower=rw.transform(old,'(include-book "machines-b")')
  self.assertEqual(tree(pick(old,'(defcolumns fn2-commit-root ?*b)')),tree(pick(lower,'(defcolumns fn2-commit-root ?*b)')))
 def test_missing_or_duplicate_subject_is_rejected(self):
  s=read('tools/fixtures/commit-root-lower-machines.lisp')
  for bad in ('',s+s):
   with self.assertRaises(ValueError):rw.transform(bad,'(include-book "machines-b")')
  with self.assertRaises(ValueError):rw.transform(s,'(include-book "other")')
 def test_actual_directory_depends_only_on_lower_carrier(self):
  directory=read('books/commit-directory.lisp')
  self.assertTrue(lr.match('(include-book "commit-root-state")',lr.parse(directory).forms,deep=False))
  self.assertFalse(lr.match('(include-book "machines-b")',lr.parse(directory).forms,deep=False))
  self.assertEqual(len(lr.match('(include-book "commit-root-state")',lr.parse(read('books/machines-b.lisp')).forms,deep=False)),1)
if __name__=='__main__':unittest.main()
