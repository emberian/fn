"""Exact boot-face class threading and authenticated cold page claims."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_reach_bind_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def tree(n):
 if hasattr(n,'low'):return n.low
 if hasattr(n,'prefix'):return (n.prefix,tree(n.node))
 return tuple(tree(x) for x in n.items)
def one(s,p):
 m=lr.match(p,lr.parse(s).forms)
 if len(m)!=1:raise ValueError(p)
 return m[0].node
class Reach(unittest.TestCase):
 def test_exact_existing_face_class_replay(self):
  old=read('tools/fixtures/event-archive-cold-boot-before-reach.lisp');after,count=rw.transform(old)
  self.assertEqual(count,7);self.assertEqual(rw.transform(after),(after,0))
  current=read('books/event-archive-cold-boot.lisp')
  for m in lr.match('(defcost ?name ?*body)',lr.parse(after).forms,deep=False):
   p='(defcost '+m.captures['name'].low+' ?*body)'
   self.assertEqual(tree(m.node),tree(one(current,p)))
  self.assertEqual(tree(one(after,'(defun fn2-boot-checkpoint-archive-owner-p ?*body)')),tree(one(current,'(defun fn2-boot-checkpoint-archive-owner-p ?*body)')))
  for name in ['begin','arm','received','check']:
   p='(defun fn2-boot-checkpoint-archive-'+name+' ?*body)'
   self.assertEqual(tree(one(old,p)),tree(one(current,p)),name)
 def test_existing_role_policies_preserved_and_new_cold_role_bounded(self):
  old=one(read('tools/fixtures/event-archive-reach-map-state-before.lisp'),'(defun fn2-checkpoint-restore-reach-map-state-p ?*body)')
  current=one(read('books/checkpoint-restore-reach.lisp'),'(defun fn2-checkpoint-restore-reach-map-state-p ?*body)')
  branch=current.items[-1].items[-1]
  self.assertEqual(tree(branch.items[3]),tree(old.items[-1].items[-1]))
  self.assertEqual(tree(branch.items[1]),('equal','role','*fn2-checkpoint-restore-reach-role-event-archive*'))
  self.assertEqual(tree(branch.items[2]),('member-equal','state',('list','*fn2-extent-state-reserved*','*fn2-extent-state-allocated*','*fn2-extent-state-retire-pending*')))
 def test_page_claim_is_after_real_verifier_and_before_parser(self):
  s=read('books/event-archive-cold-reach.lisp')
  f=one(s,'(fn2-event-archive-operation fn2-event-archive-cold-step-reach ?*body)')
  self.assertTrue(lr.match('(if (eq code :ready) ?*body)',[f]))
  gate=lr.match('(fn2-event-archive-reached-page-p ?*args)',[f])[0].node
  step=lr.match('(fn2-event-archive-cold-cursor-step ?*args)',[f])[0].node
  self.assertLess(gate.start,step.start)
  self.assertTrue(lr.match('(equal (fn2-event-archive-source-generation 1 fn2-event-archive) (fn2-checkpoint-restore-reach-control-generation 0 fn2-checkpoint-restore-reach-control))',lr.parse(s).forms))
  h=one(s,'(fn2-event-archive-operation fn2-event-archive-cold-header-reach ?*body)')
  verified=lr.match('(fn2-event-archive-cold-header-step ?*args)',[h])[0].node
  claim=lr.match('(fn2-checkpoint-restore-reach-claim ?*args)',[h])[0].node
  self.assertLess(verified.start,claim.start)
 def test_real_boot_header_guard_and_generation(self):
  s=read('books/event-archive-cold-boot.lisp')
  f=one(s,'(defun fn2-boot-checkpoint-archive-header ?*body)')
  self.assertTrue(lr.match('(equal (fn2-machine-phase id fn2-core) *fn2-boot-state-checkpoint-root-verify*)',[f]))
  self.assertTrue(lr.match('(equal (fn2-machine-root-cursor id fn2-core) *fn2-format-page-size*)',[f]))
  self.assertTrue(lr.match('(fn2-boot-checkpoint-archive-header-raw fn2-core)',[f]))
  owner=one(s,'(defun fn2-boot-checkpoint-archive-owner-p ?*body)')
  self.assertTrue(lr.match('(fn2-event-archive-cold-reach-current-p ?*args)',[owner]))
if __name__=='__main__':unittest.main()
