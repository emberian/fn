"""Atomic published-source retirement class; source controls, ACL2 unrun."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import seal_overlay_draining_rewrite as d
from identity_arena_draining_projection import before_current
ROOT=Path(__file__).resolve().parents[1]
def one(p,s):return d.one(p,s)
class Draining(unittest.TestCase):
 def test_fixed_class_reproduces_and_is_idempotent(self):
  self.assertEqual(sum(map(len,d.BEFORE.values())),6)
  for file,items in d.BEFORE.items():
   actual=before_current(file,(ROOT/file).read_text())
   for pattern,before in items.items():
    n=one(pattern,actual);self.assertEqual(actual[n.start:n.end],d.target(pattern,before))
   self.assertEqual(d.transform(file,actual),actual)
 def test_appended_phase_preserves_existing_phase_values(self):
  s=(ROOT/'books/overlay.lisp').read_text()
  self.assertTrue(lr.match('(:enum fn2-overlay-phase (:free :active :frozen :private :spare :draining))',lr.parse(s).forms))
 def test_atomic_install_precheck_precedes_all_source_changes(self):
  s=(ROOT/'books/sealer.lisp').read_text();n=one('(defun fn2-seal-install ?*body)',s)
  gate=lr.match('(equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*)',[n])[0]
  retire=lr.match('(fn2-seal-retire-runs ?*args)',[n])[0]
  install=lr.match('(fn2-seal-install-run ?*args)',[n])[0]
  drain=lr.match('(fn2-overlays-set-phase o *fn2-overlay-phase-draining* fn2-overlays)',[n])[0]
  finish=lr.match('(fn2-seals-set-phase 0 *fn2-seal-phase-overlay-return* fn2-seals)',[n])[0]
  self.assertLess(gate.start,retire.start);self.assertLess(retire.start,install.start)
  self.assertLess(install.start,drain.start);self.assertLess(drain.start,finish.start)
  self.assertFalse(lr.match('(fn2-overlays-put ?*args)',[n]))
 def test_cleanup_requires_draining_empty_legacy_retire_is_preserved(self):
  s=(ROOT/'books/sealer.lisp').read_text();cleanup=one('(defun fn2-seal-overlay-return ?*body)',s)
  self.assertTrue(lr.match('(equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-draining*)',[cleanup]))
  retire=one('(defun fn2-seal-retire ?*body)',s)
  self.assertTrue(lr.match('(member-equal phase (list *fn2-overlay-phase-frozen* *fn2-overlay-phase-draining*))',[retire]))
  release=lr.match('(fn2-idc-arena-return ?*args)',[retire])[0];advance=lr.match('(fn2-ov-advance o phase *fn2-overlay-phase-free* fn2-overlays)',[retire])[0]
  self.assertLess(release.start,advance.start)
  start=one('(defun fn2-seal-start ?*body)',s)
  self.assertTrue(lr.match('(not (posp (fn2-overlays-count o fn2-overlays)))',[start]))
 def test_selection_and_reuse_domains_exclude_draining(self):
  range_src=(ROOT/'books/range.lisp').read_text();n=one('(defun fn2-range-add-overlays ?*body)',range_src)
  self.assertTrue(lr.match('(list *fn2-overlay-phase-active* *fn2-overlay-phase-frozen*)',[n]))
  overlay=(ROOT/'books/overlay.lisp').read_text();n=one('(defun fn2-ov-start ?*body)',overlay)
  self.assertTrue(lr.match('(equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-free*)',[n]))
 def test_resident_credit_negative_is_not_arena_return_authority(self):
  fixture=(ROOT/'tests/seal-release-row-held-unit.lisp').read_text();self.assertIn('Hypothesis-removal control',fixture)
  provider=(ROOT/'books/identity-arena-credit.lisp').read_text()
  self.assertTrue(lr.match('(fn2-pool-reserve-credit ?*args)',lr.parse(provider).forms))
  self.assertIn('(fn2-idc-arena-credit-layout-p o commitrows class fn2-overlays fn2-pool)',provider)
  # The resident run test removes the noncredit run-page origin premise;
  # new arena credit authority does not authorize a run-cache page return.
  self.assertIn('fn2-srh-resident-credit-body',fixture)
  self.assertIn('fn2-pool-credit-configure',fixture)
  sealer=(ROOT/'books/sealer.lisp').read_text()
  release=one('(defun fn2-seal-release-row ?*body)',sealer)
  self.assertTrue(lr.match('(fn2-pool-release ?*args)',[release]))
  self.assertFalse(lr.match('(fn2-idc-arena-return ?*args)',[release]))
  actor=(ROOT/'books/machines-c-sealer-events.lisp').read_text()
  self.assertFalse(lr.match('((:credit) (:charge ?*args))',lr.parse(actor).forms))
if __name__=='__main__':unittest.main()
