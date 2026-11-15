#!/usr/bin/env python3
"""Actual physical-sealer callback seams, source-only controls."""
import sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
def text(p):return (ROOT/p).read_text()
def fun(p,n):
 s=text(p);m=lr.match('(defun '+n+' ?*b)',lr.parse(s).forms,deep=True)
 if len(m)!=1:raise AssertionError(n)
 x=m[0].node;return s[x.start:x.end]
class SealerPhysical(unittest.TestCase):
 def test_no_resident_bundle_regression(self):
  s=fun('books/sealer.lisp','fn2-seal-start')
  self.assertLess(s.index(':need-loader'),s.index('(fn2-pool-reserve'))
  self.assertIn('(posp (fn2-seal-physical-inputs',s)
 def test_atomic_profile_derived_recipe(self):
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-load-reserve')
  self.assertLess(s.index('fn2-sealer-copy-roomp'),s.index('fn2-run-load-region-reserve'))
  self.assertIn('*fn2-b-seal-source-cursors*',s)
  self.assertIn('(mv :ok 0 fn2-seals',s)
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-copy-roomp')
  self.assertIn('fn2-pool-reservable-count',s);self.assertNotIn('class-countsi',s)
 def test_actual_receipt_gates_admission_and_miss(self):
  for n in ('fn2-sealer-load-reserve','fn2-sealer-load-owner'):
   self.assertIn('(fn2-sealer-loader-observed-p',fun('books/sealer-physical-loader.lisp',n))
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-loader-observed-p')
  self.assertIn('fn2-c-source-reader-current-p',s);self.assertIn('fn2-seals-source-receipt',s)
 def test_both_key_source_and_cursor_use_actual_ml_owner(self):
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-load-owner')
  for x in ('fn2-run-load-range-miss','(fn2-range-sources-cursor s','(fn2-range-sources-put s (okind kind) (oslot owner) (ogen generation))','(fn2-run-cursors-put c (okind kind) (oslot owner) (ogen generation))'):self.assertIn(x,s)
 def test_copy_freezes_actual_source_tuple_before_consume(self):
  s=fun('books/sealer.lisp','fn2-seal-merge-next')
  self.assertLess(s.index('(source-kind'),s.index('(fn2-range-consume'))
  s=fun('books/sealer.lisp','fn2-seal-merge-add')
  self.assertLess(s.index('(fn2-run-entry-rehome-step'),s.index('(fn2-run-build-add'))
  self.assertIn('(fn2-seals-copy-state 0 fn2-seals) 2',s)
 def test_rehome_has_both_actual_owner_checks_and_bounded_copy(self):
  s=fun('books/run-entry-rehome.lisp','fn2-run-entry-rehome-step')
  for x in ('nil sk ss sg fn2-pool','t dk ds dg fn2-pool','(min budget 4096','fn2-run-entry-copy-owned'):self.assertIn(x,s)
  s=fun('books/run-entry-rehome.lisp','fn2-run-entry-copy-owned')
  self.assertIn('fn2-pool-read src sgen soff sk ss sg',s)
  self.assertIn('fn2-pool-write dst dgen doff byte dk ds dg',s)
 def test_actual_issue_and_completion_wake_only(self):
  s=text('books/machines-c-sealer-events.lisp')
  self.assertIn('(:issue (fn2-run-page-read row-load-cursor',s)
  self.assertIn(':observes ((:read-result (:wake)))',s)
  self.assertNotIn('fn2-run-load-harvest',s)
  for n in ('fn2-run-page-bind','fn2-run-page-step','fn2-sealer-load-owner-op'):self.assertIn(n,s)
 def test_actual_drain_before_source_release(self):
  s=fun('books/machines-c-sealer-events.lisp','fn2-sealer-source-release')
  self.assertLess(s.index('fn2-sealer-loader-free-p'),s.index('fn2-c-source-reader-release'))
  s=text('books/machines-c-sealer-events.lisp')
  for n in ('fn2-sealer-copy-release-op','fn2-sealer-load-member-release-op','fn2-run-page-release'):self.assertIn(n,s)
 def test_codec_derived_conservative_cost(self):
  s=text('books/machines-c-sealer-kind.lisp')
  self.assertIn('(* *fn2-b-seal-source-cursors* *fn2-c-read-callback-bytes*)',s)
  self.assertIn(':bytes *fn2-sealer-turn-bytes*',s)
if __name__=='__main__':unittest.main()
