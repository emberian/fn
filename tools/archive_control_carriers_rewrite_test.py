#!/usr/bin/env python3
"""Controls for exact pending archive ownership through the actual worker cone."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
from archive_control_carriers_rewrite import transform
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def pick(s,p):return lr.match(p,lr.parse(s).forms,deep=False)[0].node
def tree(n):return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
class ArchiveControlCarriers(unittest.TestCase):
 def setUp(self):
  self.before=[read('tools/fixtures/archive-control-'+n+'.lisp') for n in ['producer','work','control']]
  self.after=transform(*self.before)
 def test_owner_decision_moves_without_body_drift(self):
  old=pick(self.before[2],'(defun fn2-event-archive-ownerp ?*body)')
  new=pick(self.after[1],'(defun fn2-event-archive-ownerp ?*body)')
  self.assertEqual(tree(old),tree(new))
  self.assertFalse(lr.match('(defun fn2-event-archive-ownerp ?*body)',lr.parse(self.after[2]).forms,deep=False))
 def test_readonly_control_is_explicit_once_and_outputs_are_unchanged(self):
  for oldmatch in lr.match('(fn2-event-archive-operation ?name ?children ?outputs ?*body)',lr.parse(self.before[1]).forms,deep=False):
   name=oldmatch.captures['name'].low
   n=pick(self.after[1],'(fn2-event-archive-operation '+name+' ?*body)')
   self.assertEqual([x.low for x in n.items[2].items].count('fn2-event-archive'),1)
   self.assertEqual(tree(n.items[3]),tree(oldmatch.captures['outputs']))
 def test_actual_calls_match_new_builder_predicate_arity(self):
  for text in self.after[1:]:
   for match in lr.match('(fn2-event-archive-builderp ?*args)',lr.parse(text).forms):
    self.assertEqual(len(match.node.items)-1,11)
    self.assertEqual(match.node.items[1].low,'fn2-event-archive')
  n=pick(self.after[1],'(defun fn2-event-archive-builderp ?*body)')
  self.assertEqual(len(n.items[2].items),11)
  self.assertIn('fn2-event-archive-ownerp',str(tree(n.items[-1])))
  self.assertIn('*fn2-event-archive-phase-members*',str(tree(n.items[-1])))
  self.assertIn('*fn2-event-archive-phase-manifest*',str(tree(n.items[-1])))
 def test_control_registration_precedes_worker_costs(self):
  p=self.after[0]
  child=pick(p,'(fn2-sealer-child fn2-core-event-archive ?*body)')
  op=pick(p,'(defmacro fn2-event-archive-operation ?*body)')
  self.assertLess(child.start,op.start)
  self.assertFalse(lr.match('(fn2-sealer-child fn2-core-event-archive ?*body)',lr.parse(self.after[2]).forms,deep=False))
if __name__=='__main__':unittest.main()
