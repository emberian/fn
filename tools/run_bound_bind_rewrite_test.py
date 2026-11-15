"""Exact old binding tail/source admission controls, without ACL2 evaluation."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import run_bound_bind_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def tree(n):return n.low if hasattr(n,'low') else tuple(tree(x) for x in n.items)
class Bind(unittest.TestCase):
 def setUp(self):
  self.before=(ROOT/'tools/fixtures/run-physical-bind-source-before.lisp').read_text()
  self.source=(ROOT/'books/run-physical-source.lisp').read_text()
  self.lower=(ROOT/'books/run-physical-bound-bind.lisp').read_text()
 def test_exact_replay_and_idempotence(self):
  self.assertEqual(rw.transform(self.before),(self.source,self.lower))
  self.assertEqual(rw.transform(self.source),(self.source,None))
 def test_authority_and_lease_admission_are_unchanged(self):
  old=rw.one(self.before,'(defun fn2-run-load-bind ?*body)').items[-1].items[1].items
  new=rw.one(self.source,'(defun fn2-run-load-bind ?*body)').items[-1].items[1].items
  self.assertEqual([tree(x) for x in old[:-3]],[tree(x) for x in new[:-1]])
  self.assertEqual(len(lr.match('(fn2-run-bound-bind ?*args)',[new[-1]])),1)
  self.assertLess(self.source.index('(fn2-checkpoint-summary-acquire'),self.source.index('(fn2-run-bound-bind c'))
 def test_same_concrete_effects_and_namespace(self):
  old=lr.match('(fn2-run-loads-put c ?*body)',lr.parse(self.before).forms)[0].node
  new=lr.match('(fn2-run-loads-put c ?*body)',lr.parse(self.lower).forms)[0].node
  def ns(n):
   t=tree(n)
   def visit(t):
    if t==('fn2-checkpoint-summary-history','0','fn2-checkpoint-summary'):return 'history'
    if t==('fn2-checkpoint-summary-incarnation','0','fn2-checkpoint-summary'):return 'incarnation'
    return tuple(visit(x) for x in t) if isinstance(t,tuple) else t
   return visit(t)
  self.assertEqual(ns(old),tree(new))
  self.assertNotIn('fn2-checkpoint-summary',self.lower)
  self.assertNotIn('event-archive',self.lower)
  self.assertEqual(len(lr.match('(fn2-pool-reset ?*args)',lr.parse(self.lower).forms)),1)
 def test_admission_drift_is_refused(self):
  with self.assertRaises(ValueError):rw.transform(self.before.replace('(fn2-pool-reset','(other-reset',1))
if __name__=='__main__':unittest.main()
