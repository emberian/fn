#!/usr/bin/env python3
"""Structural controls for extracting, rather than copying, the served loader."""
import unittest
from pathlib import Path
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def fn(s,name):return lr.match('(defun '+name+' ?*body)',lr.parse(s).forms,deep=False)[0].node
def tree(n):return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
def normalize(n):
 t=tree(n)
 def go(t):
  if not isinstance(t,tuple):return t
  if t and t[0]=='fn2-run-load-sourcep':return ('fn2-run-load-boundp',*t[1:4])
  return tuple(go(x) for x in t)
 return go(t)
class BoundExtraction(unittest.TestCase):
 def test_original_physical_transition_bodies_are_identical(self):
  for part,suffix in [('io','issue'),('step','step')]:
   old=fn(read('tools/fixtures/run-physical-bound/'+part+'.lisp'),'fn2-run-load-'+suffix)
   new=fn(read('books/run-physical-bound-'+part+'.lisp'),'fn2-run-bound-'+suffix)
   self.assertEqual(normalize(old.items[-1]),tree(new.items[-1]))
 def test_each_wrapper_checks_authority_then_calls_one_engine(self):
  for part,suffix in [('io','issue'),('step','step')]:
   n=fn(read('books/run-physical-'+part+'.lisp'),'fn2-run-load-'+suffix)
   self.assertEqual(len(lr.match('(fn2-run-load-sourcep ?*args)',[n])),1)
   self.assertEqual(len(lr.match('(fn2-run-bound-'+suffix+' ?*args)',[n])),1)
   self.assertFalse(lr.match('(fn2-block-read-children ?*args)',[n]))
   self.assertFalse(lr.match('(fn2-format-run ?*args)',[n]))
   self.assertEqual(n.items[-1].items[0].low,'cond')
   # Original budget refusal retains priority over authority refusal.
   self.assertIn(':yield',str(tree(n.items[-1].items[1])))
   self.assertIn(':source',str(tree(n.items[-1].items[2])))
 def test_original_source_predicate_is_partitioned_losslessly(self):
  old=fn(read('tools/fixtures/run-physical-bound/source.lisp'),'fn2-run-load-sourcep')
  common=fn(read('books/run-physical-bound.lisp'),'fn2-run-load-boundp')
  wrapper=fn(read('books/run-physical-source.lisp'),'fn2-run-load-sourcep')
  before=list(map(tree,old.items[-1].items[1:]))
  after=list(map(tree,common.items[-1].items[1:]))+list(map(tree,wrapper.items[-1].items[2:]))
  self.assertCountEqual(before,after)
 def test_shared_engines_have_no_catalog_authority_formals(self):
  for part,suffix in [('io','issue'),('step','step')]:
   n=fn(read('books/run-physical-bound-'+part+'.lisp'),'fn2-run-bound-'+suffix)
   args=[x.low for x in n.items[2].items]
   self.assertFalse(any('summary' in x or x=='fn2-run-installed' for x in args))
   self.assertEqual(len(args),len(set(args)))
 def test_actual_harvest_body_is_shared_unchanged(self):
  old=fn(read('tools/fixtures/run-physical-bound/io.lisp'),'fn2-run-load-harvest')
  new=fn(read('books/run-physical-bound-io.lisp'),'fn2-run-load-harvest')
  self.assertEqual(tree(old),tree(new))
  self.assertFalse(lr.match('(defun fn2-run-load-harvest ?*body)',lr.parse(read('books/run-physical-io.lisp')).forms,deep=False))
 def test_verification_and_read_only_exist_once(self):
  paths=['books/run-physical-'+x+'.lisp' for x in ['io','step','bound-io','bound-step']]
  forms=[f for p in paths for f in lr.parse(read(p)).forms]
  self.assertEqual(len(lr.match('(fn2-block-read-children ?*args)',forms)),1)
  self.assertEqual(len(lr.match('(fn2-format-run ?*args)',forms)),1)
  self.assertEqual(len(lr.match('(fn2-checkpoint-semantic-page-read-header ?*args)',forms)),1)
if __name__=='__main__':unittest.main()
