"""Actual borrowed candidate cursor/read-kernel controls; no IO execution."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_visit_rewrite as visit
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
class Cursor(unittest.TestCase):
 def test_existing_operation_generator_symbol_case_is_preserved(self):
  old=read('tools/fixtures/event-archive-operation-before.lisp').rstrip()
  expected=old.replace(' `(progn',' (let* ((fn (if (consp name) (car name) name))\n        (formals (append (if (consp name) (cdr name) nil) children)))\n `(progn',1)
  expected=expected.replace('(defun ,name ,children','(defun ,fn ,formals').replace('(fn2-checkpoint-root1-preserves ,name ,children','(fn2-checkpoint-root1-preserves ,fn ,formals').replace('(fn2-columns-sym name "-OP") :child ,name','(fn2-columns-sym fn "-OP") :child ,fn')+')'
  s=read('books/event-archive-producer.lisp');node=lr.match('(defmacro fn2-event-archive-operation ?*body)',lr.parse(s).forms,deep=False)[0].node
  self.assertEqual(s[node.start:node.end],visit.operation(expected))
 def test_boot_borrow_handles_and_private_source_derived_root(self):
  s=read('books/event-archive-cold-cursor.lisp')
  self.assertTrue(calls(s,'(fn2-event-archive-cold-source-p fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)'))
  for check in ['(not (equal scratch page))','(eq (fn2-pool-workspace-code scratch sgen kind owner gen fn2-pool) :ok)',
                '(equal (fn2-checkpoint-restore-reader-slot 0 fn2-checkpoint-restore-reader) (fn2-event-archive-header-slot 1 fn2-event-archive))']:
   self.assertIn(check,s)
  self.assertTrue(calls(s,'(fn2-run-load-admission-begin fn2-run-loads)'))
  self.assertTrue(calls(s,'(lease-mode *fn2-run-load-lease-mode-candidate-borrowed*)'))
  self.assertTrue(calls(s,'(fn2-b-event-archive-cursor-from-rows (fn2-run-loads-rows fn2-run-loads))'))
  self.assertFalse(calls(s,'(fn2-run-install-physical ?*args)'))
  self.assertFalse(calls(s,'(fn2-checkpoint-summary-acquire ?*args)'))
 def test_one_shared_physical_bind_hash_parser_transition(self):
  s=read('books/event-archive-cold-cursor.lisp')
  for name in ['fn2-run-bound-bind','fn2-run-bound-step','fn2-run-scan-step']:
   self.assertEqual(len(calls(s,'('+name+' ?*args)')),1,name)
  for name in ['fn2-issue-read-children','fn2-block-read-children','fn2-format-run','fn2-run-layout-decode','fn2-pool-release']:
   self.assertFalse(calls(s,'('+name+' ?*args)'))
  # This slice cannot acknowledge transport completion from an argument.
  self.assertNotIn('*fn2-run-load-phase-copy*',s)
 def test_manifest_entry_freezes_before_another_cursor_transition(self):
  s=read('books/event-archive-cold-cursor.lisp')
  freeze=calls(s,'(when (equal (fn2-event-archive-entry-pending 1 fn2-event-archive) 1))')[0].node
  scan=calls(s,'(fn2-run-scan-step ?*args)')[0].node
  self.assertLess(freeze.start,scan.start)
  self.assertTrue(calls(s,'(if (eq code :entry) (fn2-event-archive-set-entry-pending 1 1 fn2-event-archive) fn2-event-archive)'))
if __name__=='__main__':unittest.main()
