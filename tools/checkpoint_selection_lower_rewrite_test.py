#!/usr/bin/env python3
"""Exact predicate extraction and local include DAG; not ACL2 admission."""
import re
import unittest
from pathlib import Path
import lisp_rewrite as lr
import checkpoint_selection_lower_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def definition(s,name):
 m=lr.match('(defun '+name+' ?*body)',lr.parse(s).forms,deep=False)
 if len(m)!=1: raise ValueError(name)
 n=m[0].node
 return s[n.start:n.end]
def closure(root):
 done=set()
 def walk(p,stack):
  if p in stack: raise AssertionError('include cycle: '+' -> '.join(str(x.relative_to(ROOT)) for x in stack+[p]))
  if p in done:return
  if not p.exists():raise AssertionError('missing '+str(p))
  for line in p.read_text().splitlines():
   m=re.match(r'\s*\(include-book "([^"]+)"',line)
   if m and ':dir' not in line:walk((p.parent/(m[1]+'.lisp')).resolve(),stack+[p])
  done.add(p)
 walk(ROOT/root,[])
 return done
class SelectionLower(unittest.TestCase):
 def test_six_actual_predicates_exactly_unchanged(self):
  for book in rw.GROUPS:
   old=(ROOT/('tools/fixtures/'+book+'-lower-before.lisp')).read_text()
   upper,lower=rw.extract(old,book)
   self.assertEqual(upper,(ROOT/('books/'+book+'.lisp')).read_text())
   self.assertEqual(lower,(ROOT/('books/'+book+'-identity.lisp')).read_text())
   for name in rw.names(book):
    self.assertEqual(definition(old,name),definition(lower,name))
    self.assertFalse(lr.match('(defun '+name+' ?*b)',lr.parse(upper).forms,deep=False))
 def test_missing_duplicate_rejected(self):
  for b in rw.GROUPS:
   s=(ROOT/('tools/fixtures/'+b+'-lower-before.lisp')).read_text()
   for bad in ('',s+s):
    with self.assertRaises(ValueError):rw.extract(bad,b)
 def test_projection_has_only_lower_identity_dependency(self):
  paths=closure('books/checkpoint-projection-state.lisp')
  for name in ('boot-kind','checkpoint-selected-source','checkpoint-recovery-census'):
   self.assertNotIn(ROOT/('books/'+name+'.lisp'),paths)
 def test_actual_boot_and_sealer_fixture_include_dags(self):
  for p in ('books/boot-kind.lisp','tests/sealer-source-quiescence-unit.lisp'):closure(p)
if __name__=='__main__':unittest.main()
