"""Actual source constructors/cleanup wiring; source-only, no ACL2 admission."""
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class SourceReaderBoundary(unittest.TestCase):
 def setUp(self):
  self.loader=(ROOT/'books/checkpoint-source-loader.lisp').read_text()
  self.release=(ROOT/'books/checkpoint-metadata-release.lisp').read_text()
 def test_borrow_derives_windows_and_advances_admission_before_claim(self):
  text=self.loader.split('(defun fn2-checkpoint-source-reader-borrow ',1)[1].split('(fn2-run-load-frames',1)[0]
  self.assertLess(text.index('(fn2-run-load-admission-begin'),text.index('(fn2-run-loads-put'))
  for name in ('fn2-checkpoint-source-reader-windowsp','fn2-checkpoint-source-reader-isolatedp','borrow-token token','*fn2-checkpoint-source-page-window*','*fn2-checkpoint-source-read-window*'):
   self.assertIn(name,text)
  self.assertNotIn('fn2-pool-reserve',text)
 def test_detach_requires_return_and_never_frees_working_windows(self):
  text=self.loader.split('(defmacro fn2-checkpoint-source-reader-detach-owned-body',1)[1].split('(defun fn2-checkpoint-source-reader-finish',1)[0]
  for name in ('fn2-checkpoint-source-reader-attachedp','fn2-checkpoint-source-reader-windowsp','fn2-run-loads-pending','fn2-checkpoint-summary-release','(borrow-token 0)'):
   self.assertIn(name,text)
  self.assertNotIn('fn2-pool-release',text)
 def test_public_release_requires_detached_job_before_working_release(self):
  self.assertLess(self.release.index('(fn2-checkpoint-source-reader-detachedp'),self.release.index('(fn2-checkpoint-working-release-step'))
  for table in ('fn2-core-run-loads','fn2-core-run-cursors','fn2-core-checkpoint-summary-leases'):
   self.assertIn(table,self.release)
 def test_named_source_cursor_and_wire_priority_are_separate(self):
  for path in ('checkpoint-source-loader.lisp','checkpoint-metadata-driver.lisp'):
   text=(ROOT/'books'/path).read_text()
   self.assertNotIn('(- (fn2-run-loads-rows fn2-run-loads) 1)',text)
   self.assertNotIn('(- (fn2-run-cursors-rows fn2-run-cursors) 1)',text)
   self.assertIn('fn2-b-checkpoint-source-cursor-from-rows',text)
  self.assertIn('fn2-run-installed-wire-run',self.loader)
  self.assertIn('fn2-run-cursors-priority',self.loader)
 def test_prepared_fixture_does_not_assert_physical_completion(self):
  text=(ROOT/'tests/checkpoint-source-reader-borrow-unit.lisp').read_text()
  self.assertIn(':borrowed',text)
  self.assertIn('fn2-checkpoint-source-reader-borrow',text)
  self.assertNotIn('(phase *fn2-run-load-phase-ready*)',text)
if __name__=='__main__':unittest.main()
