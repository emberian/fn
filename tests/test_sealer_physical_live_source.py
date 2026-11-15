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
 def test_miss_adapter_rebinds_only_actual_cursor_before_verification(self):
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-load-owner')
  for x in ('fn2-run-load-range-miss','(fn2-range-sources-cursor s','(fn2-run-cursors-put c (okind kind) (oslot owner) (ogen generation))'):self.assertIn(x,s)
  self.assertNotIn('(fn2-range-sources-put',s)
 def test_shared_authenticated_head_constructor_owns_physical_view(self):
  s=text('books/range.lisp')
  self.assertIn('(fn2-run-cursors-physical c fn2-run-cursors)',s)
  self.assertIn('(fn2-run-cursors-okind c fn2-run-cursors)',s)
  self.assertIn('(fn2-run-cursors-oslot c fn2-run-cursors)',s)
  self.assertIn('(fn2-run-cursors-ogen c fn2-run-cursors)',s)
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
 def test_stable_nineteen_recipe_and_same_owned_tail(self):
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-copy-class-need')
  self.assertIn('(+ 1 *fn2-b-seal-source-cursors*)',s)
  self.assertIn('(equal class hash)',s)
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-load-reserve')
  for x in ('prefix-hash-live 1','prefix-page-live 1','*fn2-seal-hash-bytes*','*fn2-run-layout-max-entry-bytes*'):self.assertIn(x,s)
  start=fun('books/sealer.lisp','fn2-seal-start')
  self.assertIn('(fn2-seal-open-owned',start)
  self.assertNotIn('(fn2-run-build-start',start)
  self.assertIn('fn2-seals-prefix-hash-live',start)
  old=text('tools/fixtures/sealer-start-before-owned.lisp')
  owned=fun('books/sealer.lisp','fn2-seal-open-owned')
  def call(source):
   m=lr.match('(fn2-run-build-start ?*args)',lr.parse(source).forms,deep=True)
   self.assertEqual(len(m),1);n=m[0].node;return source[n.start:n.end]
  self.assertEqual(call(old),call(owned))
  self.assertIn('(prefix-hash-live 0)',owned)
  self.assertIn('(fn2-seal-prefix-owned-p fn2-seals fn2-pool)',start)
  proof=fun('books/sealer.lisp','fn2-seal-prefix-owned-p')
  for x in ('prefix-hash-gen','prefix-page-gen','fn2-pool-workspace-code','fn2-pool-cap','fn2-pool-fill'):self.assertIn(x,proof)
 def test_first_page_consumes_owned_handle_without_reservation(self):
  s=fun('books/sealer.lisp','fn2-seal-take-page')
  self.assertIn('(if (= (fn2-seals-prefix-page-live 0 fn2-seals) 1)',s)
  self.assertIn('(mv :ok (fn2-seals-prefix-page-slot',s)
  self.assertIn('(fn2-seal-take-page-owned',s)
  s=fun('books/sealer.lisp','fn2-seal-take-page-owned')
  for x in ('fn2-pool-workspace-code','fn2-pool-cap slot','fn2-seals-set-prefix-page-live'):self.assertIn(x,s)
 def test_unused_recipe_windows_drain_before_observer_release(self):
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-copy-release')
  for i in range(3):self.assertIn('(fn2-sealer-recipe-return-one '+str(i),s)
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-loader-free-p')
  self.assertIn('fn2-seals-prefix-hash-live',s);self.assertIn('fn2-seals-prefix-page-live',s)
 def test_recipe_pool_wait_follows_exact_observer_release(self):
  s=text('books/machines-c-sealer-events.lisp')
  release=s.index('(:do (code target targetgen) (fn2-sealer-source-release)')
  wait=s.index('(:park :pool pclass')
  self.assertLess(release,wait)
  self.assertIn('(retry-pool 1)',s)
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-copy-wait-class')
  self.assertIn('fn2-pool-reservable-count',s);self.assertIn('fn2-sealer-copy-class-need',s)
 def test_actual_issue_and_completion_wake_only(self):
  s=text('books/machines-c-sealer-events.lisp')
  self.assertIn('(:issue (fn2-run-page-read row-load-cursor',s)
  self.assertIn(':observes ((:read-result (:wake)))',s)
  self.assertNotIn('fn2-run-load-harvest',s)
  for n in ('fn2-run-page-bind','fn2-run-page-step','fn2-sealer-load-owner-op'):self.assertIn(n,s)
 def test_closing_does_not_close_actual_physical_pin_path(self):
  issue=fun('books/machines-b.lisp','fn2-pinned-block-io-children')
  self.assertIn('(fn2-alloc-edge-add',issue)
  self.assertNotIn('fn2-alloc-snapshot-activep',issue)
  edge=fun('books/alloc.lisp','fn2-alloc-edge-add')
  self.assertNotIn('fn2-alloc-snapshot-activep',edge)
  self.assertIn('*fn2-alloc-edges*',edge)
  work=fun('books/machines-c-sealer-events.lisp','fn2-sealer-work')
  self.assertIn('*fn2-csnapshot-phase-held*',work)
  self.assertNotIn('*fn2-csnapshot-phase-closing*',work)
 def test_actual_drain_before_source_release(self):
  s=fun('books/machines-c-sealer-events.lisp','fn2-sealer-source-release')
  self.assertLess(s.index('fn2-sealer-loader-free-p'),s.index('fn2-c-source-reader-release'))
  s=text('books/machines-c-sealer-events.lisp')
  for n in ('fn2-sealer-copy-release-op','fn2-sealer-load-member-release-op','fn2-run-page-release'):self.assertIn(n,s)
 def test_resident_successor_cannot_release_durable_backing_promise(self):
  s=fun('books/sealer-physical-loader.lisp','fn2-sealer-load-retire')
  self.assertIn('fn2-checkpoint-summary-row-retire-row',s)
  for x in ('fn2-checkpoint-cbase-row-release-step','fn2-checkpoint-cbase-release-step','fn2-checkpoint-cbase-release-op','fn2-checkpoint-cbase-holds-put','fn2-checkpoint-cbase-holds-set-'):self.assertNotIn(x,s)
  book=text('books/sealer-physical-loader.lisp')
  self.assertIn("(getpropc 'fn2-sealer-load-retire 'stobjs-out",book)
  self.assertNotIn('(fn2-checkpoint-cbase-release',book)
 def test_readonly_drain_face_has_no_fabricated_core_result(self):
  fixture=text('tests/sealer-physical-admission-unit.lisp')
  self.assertIn('((mv code c) (fn2-sealer-load-drain-op',fixture)
  self.assertNotIn('((mv code c fn2-core) (fn2-sealer-load-drain-op',fixture)
  lower=fun('books/sealer-physical-loader.lisp','fn2-sealer-load-drain')
  self.assertIn('(mv :owner 0)',lower)
  self.assertNotIn('(update-',lower)
 def test_codec_derived_conservative_cost(self):
  s=text('books/machines-c-sealer-kind.lisp')
  self.assertIn('(* *fn2-b-seal-source-cursors* *fn2-c-read-callback-bytes*)',s)
  self.assertIn(':bytes *fn2-sealer-turn-bytes*',s)
if __name__=='__main__':unittest.main()
