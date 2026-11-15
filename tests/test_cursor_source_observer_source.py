"""Actual D callback/source controls; no ACL2 evaluation or runtime claim."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from lisp_source import forms, read_sexp
from cursor_source_storage import transform
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def source():return (ROOT/'books/cursor.lisp').read_text()
def arms():
 return next(read_sexp(f) for f in forms(source()) if f.startswith('(defmachine-arms fn2-cursor :children'))
def named(name):return next(x for x in walk(arms()) if x and x[0]==name)
class CursorObserver(unittest.TestCase):
 def test_storage_union_transformation_preserves_budget_and_rejects_drift(self):
  current=(ROOT/'books/cursor-kind.lisp').read_text()
  self.assertEqual(current.count('(storage :held)'),6)
  old=current.replace('(storage :held)','(query-bundle :held)')
  self.assertEqual(transform(old),current)
  with self.assertRaises(ValueError):transform(old.replace('(query-bundle :held)','(lease :held)',1))
 def test_admission_observes_before_physical_count_and_pool(self):
  select=named(':select');s=str(select)
  self.assertLess(s.index('fn2-c-source-read-acquire'),s.index('fn2-cursor-physical-sources'))
  self.assertLess(s.index('fn2-cursor-physical-sources'),s.index('fn2-run-page-bundle-reserve'))
  self.assertIn(['equal','physical','0'],list(walk(select)))
  self.assertIn([':goto','resident-admit'],list(walk(select)))
  self.assertIn([':goto','source-release-refuse'],list(walk(select)))
 def test_resident_metadata_has_no_bundle_and_articles_pre_admit(self):
  resident=named('resident-admit');s=str(resident)
  self.assertNotIn('fn2-run-page-bundle-reserve',s)
  self.assertIn('fn2-cursor-lease-reserve',s)
  self.assertNotIn(':park',s)
  self.assertIn([':next',':seek'],list(walk(resident)))
  # No late reserve in render after a response may already have begun.
  self.assertNotIn('fn2-cursor-lease-reserve',str(named('art-lease')))
 def test_both_pool_refusals_release_actual_observer_before_reply(self):
  f=named('source-release-refuse');s=str(f)
  self.assertLess(s.index('fn2-c-source-read-release'),s.index('fn2-cursor-reply-of'))
  self.assertIn([':wake-row','target'],list(walk(f)))
  finish=named('source-release-finish')
  self.assertIn([':next',':draining'],list(walk(finish)))
  main=named(':finish');s=str(main)
  self.assertLess(s.index('fn2-read-release'),s.index('source-release-finish'))
  self.assertIn([':goto','run-load-drain'],list(walk(main)))
 def test_standalone_and_borrowed_release_paths_are_distinct(self):
  for name in ('art-fail','art-end',':finish'):
   f=named(name)
   branch=next(x for x in walk(f) if x and x[0]==':if' and x[1]==['equal','row-query-bundle','*fn2-cursor-query-bundle-none*'])
   self.assertIn('fn2-cursor-lease-release',str(branch[2]))
   self.assertEqual(branch[3],[])
  drain=str(named('run-load-drain'))
  self.assertIn('fn2-run-page-release',drain)
  self.assertIn('*fn2-cursor-storage-none*',drain)
if __name__=='__main__':unittest.main()
