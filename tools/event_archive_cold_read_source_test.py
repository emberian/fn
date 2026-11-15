"""Saved issued address/completion binding on actual candidate read faces."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
def tree(n):
 if hasattr(n,'low'):return n.low
 if hasattr(n,'prefix'):return (n.prefix,tree(n.node))
 return tuple(tree(x) for x in n.items)
class Read(unittest.TestCase):
 def test_one_saved_subject_recipe_copies_and_compares(self):
  s=read('books/event-archive-cold-read.lisp')
  mapping=calls(s,'(defconst *fn2-event-archive-read-scalars* ?*body)')[0].node.items[2].node.items
  fields={n.items[0].low for n in mapping}
  self.assertEqual(fields,{'read-sector','read-unit','read-epoch','read-allocation','read-schema','read-run','read-level','read-page','read-page-gen','read-scratch','read-scratch-gen','read-owner-kind','read-owner-slot','read-owner-gen','read-candidate','read-checkpoint','read-history','read-incarnation'})
  self.assertIn(',@*fn2-event-archive-read-scalars*',s)
  self.assertIn('(fn2-event-archive-read-equalities *fn2-event-archive-read-scalars*)',s)
  self.assertTrue(calls(s,'(fn2-event-archive-read-bytes-current-p 0 c fn2-run-loads fn2-event-archive)'))
  self.assertIn('(fn2-event-archive-read-hashi i fn2-event-archive)',s)
  self.assertIn('(fn2-event-archive-read-descriptori i fn2-event-archive)',s)
 def test_completion_uses_saved_offset_and_real_boot_observation(self):
  s=read('books/event-archive-cold-boot.lisp')
  function=calls(s,'(defun fn2-boot-checkpoint-archive-received ?*body)')[0].node
  body=s[function.start:function.end]
  for p in ['(equal (fn2-machine-offset id fn2-core) (fn2-event-archive-read-offset 1 fn2-event-archive))',
            '(equal (fn2-machine-pending id fn2-core) 1)','(equal (fn2-machine-event-ready id fn2-core) 1)',
            '(equal (fn2-machine-outcome id fn2-core) *fn2-outcome-done*)','(equal (fn2-machine-count id fn2-core) *fn2-commit-unit-bytes*)',
            '(equal (fn2-machine-stage id fn2-core) 12)']:
   self.assertTrue(calls(body,p),p)
  self.assertIn('*fn2-boot-state-checkpoint-archive-copy*',body)
  self.assertTrue(calls(body,'(fn2-event-archive-cold-read-current-p ?*args)'))
  self.assertTrue(calls(body,'(fn2-run-loads-set-phase c *fn2-run-load-phase-copy* fn2-run-loads)'))
  for name in ['fn2-issue-read-children','fn2-block-read-children']:
   self.assertFalse(calls(s,'('+name+' ?*args)'))
 def test_armed_cursor_cannot_advance(self):
  s=read('books/event-archive-cold-cursor.lisp')
  gate=calls(s,'(when (equal (fn2-event-archive-read-armed 1 fn2-event-archive) 1))')[0].node
  for name in ['fn2-run-bound-bind','fn2-run-bound-step','fn2-run-scan-step']:
   self.assertLess(gate.start,calls(s,'('+name+' ?*args)')[0].node.start)
 def test_actual_existing_read_transport_preserves_address(self):
  s=read('books/boot.lisp');forms=lr.parse(s).forms
  for phase in [':read',':read-result']:
   nodes=[n for n in lr.match('('+phase+' ?*body)',forms) if len(n.node.items)>=2 and
          (getattr(n.node.items[1],'low',None)==':on-refusal' if phase==':read' else
           hasattr(n.node.items[1],'items') and getattr(n.node.items[1].items[0],'low',None)==':cond')]
   self.assertEqual(len(nodes),1)
   # The existing issued read consumes row-offset and these two arms never
   # assign it. Parent routing must preserve this property at stage12.
   self.assertFalse(lr.match('(offset ?value)',[nodes[0].node]))
  self.assertTrue(calls(s,'(fn2-issue-read row-offset row-rx-slot row-rx-gen ?*rest)'))
 def test_interleaving_control_issues_and_completes_real_descriptor(self):
  s=read('tests/event-archive-cold-read-unit.lisp')
  for name in ['fn2-event-archive-cold-read-arm','fn2-issue-read-children','fn2-pool-adapter-write','fn2-outbox-ack','fn2-post-result','fn2-harvest-one']:
   self.assertTrue(calls(s,'('+name+' ?*args)'),name)
  for mode in [':current',':sector',':unit',':hash',':descriptor']:
   self.assertTrue(calls(s,'(assert-event (fn2-eari-test '+mode+'))'))
  body=calls(s,'(defun fn2-eari-body ?*body)')[0].node
  issued=lr.match('(fn2-eari-issue ?*args)',[body])[0].node
  changed=lr.match('(fn2-eari-mutate ?*args)',[body])[0].node
  completed=lr.match('(fn2-eari-complete ?*args)',[body])[0].node
  self.assertLess(issued.start,changed.start);self.assertLess(changed.start,completed.start)
if __name__=='__main__':unittest.main()
