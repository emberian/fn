#!/usr/bin/env python3
"""Actual cursor source-shape controls; no ACL2 admission/runtime claim."""
from pathlib import Path
import unittest
import lisp_rewrite as l
ROOT=Path(__file__).resolve().parents[1]
SRC=(ROOT/'books/cursor.lisp').read_text()
LEAF=(ROOT/'books/cursor-source-observer.lisp').read_text()
KIND=(ROOT/'books/cursor-kind.lisp').read_text()
class CursorRequest(unittest.TestCase):
 def test_every_start_routes_blocked(self):
  parsed=l.parse(SRC); starts=[]
  for m in l.match('(:do ?outs ?call ?*opts)',parsed.forms):
   call=m.captures['call']
   if isinstance(call,l.Lst) and call.items and getattr(call.items[0],'low','') in ['fn2-read-range','fn2-read-scan','fn2-read-lookup','fn2-read-identity']:
    text=SRC[m.start:m.end];starts.append(text);self.assertIn('(:more)',text)
  self.assertEqual(len(starts),10)
 def test_acquire_before_parse_or_working_lease(self):
  select=SRC.split('(:select :on-refusal',1)[1].split('(:seek :on-refusal',1)[0]
  self.assertLess(select.index('fn2-cursor-request-acquire'),select.index('fn2-cursor-parse'))
  self.assertIn('(:set (observer-serial receipt))',select)
  self.assertNotIn('fn2-cursor-lease',select)
 def test_generation_and_phase_are_actual_table(self):
  self.assertEqual(LEAF.count('(equal generation (fn2-cursor-generation slot fn2-cursor-table))'),2)
  self.assertIn('*fn2-cursor-state-select*',LEAF)
  self.assertIn('*fn2-cursor-state-draining*',LEAF)
 def test_atomic_bind_and_failed_admission_rollback(self):
  acquire=LEAF.split('(defun fn2-cursor-request-release-children')[0]
  self.assertLess(acquire.index('fn2-c-source-reader-acquire'),acquire.index('fn2-read-parent-bind-pair'))
  self.assertIn('(if (equal expected 0)',acquire)
  self.assertIn('fn2-c-source-reader-release endpoint receipt',acquire)
 def test_terminal_before_release_and_recycle(self):
  release=LEAF.split('(defun fn2-cursor-request-release-children',1)[1]
  for guard in ['(fn2-cursor-pending slot fn2-cursor-table) 0','(fn2-cursor-turn slot fn2-cursor-table) 1','*fn2-cursor-lease-none*']:
   self.assertIn(guard,release)
  self.assertLess(release.index('fn2-read-parent-clear-pair'),release.index('(fn2-c-source-reader-release'))
  draining=SRC.split('(:draining :on-refusal',1)[1].split('(:retired',1)[0]
  self.assertLess(draining.index('fn2-cursor-request-release'),draining.index('(generation (if retire'))
 def test_only_busy_is_resumable_admission(self):
  read=(ROOT/'books/machines-c-read.lisp').read_text()
  self.assertIn('(if (eq code :busy) :more :fault)', LEAF)
  self.assertIn('(if (eq code :busy) :more :state)', read)
  self.assertNotIn("(member-eq code '(:busy :exhausted))", LEAF+read)
 def test_receipt_cleared_at_admission_and_recycle(self):
  self.assertIn('(observer-serial :u60)',KIND)
  self.assertIn('cursor observer-serial))',KIND)
  self.assertIn('(observer-serial 0)',SRC)
if __name__=='__main__':unittest.main()
