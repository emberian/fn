"""Actual BEGIN owns named MK initialization, with exact child/core threading."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_frontier_begin_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def one(s,p):return lr.match(p,lr.parse(s).forms)[0].node
class Begin(unittest.TestCase):
 def test_checked_class_replay_and_idempotence(self):
  for name,fn,patterns in [
   ('cursor',rw.cursor,['(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)']),
   ('boot',rw.boot,['(defcost fn2-boot-checkpoint-archive-begin ?*body)','(defun fn2-boot-checkpoint-archive-begin ?*body)'])]:
   before=read('tools/fixtures/event-archive-cold-'+name+'-before-frontier.lisp');after=fn(before)
   self.assertEqual(fn(after),after)
   current=read('books/event-archive-cold-'+name+'.lisp')
   for pattern in patterns:
    a=one(after,pattern);b=one(current,pattern)
    self.assertEqual(after[a.start:a.end],current[b.start:b.end])
 def test_private_row_ready_before_real_initialization(self):
  s=read('books/event-archive-cold-cursor.lisp')
  f=one(s,'(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)')
  self.assertEqual(len(lr.match('(fn2-mk-init event-row fn2-mk)',[f])),1)
  for p in ['(event-row (fn2-b-event-row (fn2-fc-rows fn2-fc)))','(< 0 event-row)',
            '(fn2-mk-ready event-row fn2-mk fn2-digests)','(fn2-b3-ready event-row fn2-b3 fn2-digests)']:
   self.assertTrue(lr.match(p,[f]),p)
  init=lr.match('(fn2-mk-init event-row fn2-mk)',[f])[0].node
  root=lr.match('(fn2-event-archive-cold-start-root ?*args)',[f])[0].node
  self.assertLess(init.start,root.start)
  self.assertFalse(lr.match('(fn2-mk-init 0 fn2-mk)',[f]))
 def test_actual_core_constructor_receives_all_mutable_outputs(self):
  s=read('books/event-archive-cold-boot.lisp');f=one(s,'(defun fn2-boot-checkpoint-archive-begin ?*body)')
  view=lr.match('(stobj-let ?*body)',[f])[0].node
  self.assertIn('fn2-mk',[n.low for n in view.items[2].items])
  call=lr.match('(fn2-event-archive-cold-cursor-begin ?*args)',[f])[0].node
  self.assertEqual([n.low for n in call.items[-3:]],rw.EXTRA)
if __name__=='__main__':unittest.main()
