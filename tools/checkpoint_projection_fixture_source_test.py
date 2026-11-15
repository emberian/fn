"""Focused source controls, not ACL2 admission or executable fixture results."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class ProjectionFixture(unittest.TestCase):
 def setUp(self):
  self.forms=lr.parse((ROOT/'tests/checkpoint-projection-unit.lisp').read_text()).forms
  self.body=lr.match('(defun fn2-cpu-body ?*body)',self.forms,deep=False)[0].node
 def test_setup_edge_binding_never_uses_result_code(self):
  bindings=lr.match('(fn2-alloc-edges (if (eq mode :collision) ?yes fn2-alloc-edges))',[self.body])
  self.assertEqual(len(bindings),1)
  self.assertNotIn('code',lr.flat(bindings[0].node).lower().split())
  self.assertFalse(lr.match('(fn2-alloc-edges (if (eq mode :duplicate-identity) ?*body))',[self.body]))
 def test_duplicate_expectation_is_a_final_mode_clause(self):
  self.assertTrue(lr.match('((eq mode :duplicate-identity) (and (eq code :identity) ?*rest))',[self.body]))
 def test_count_refusal_compares_full_generated_snapshots(self):
  snap=lr.match('(defun fn2-cpu-snapshot ?*body)',self.forms,deep=False)[0].node
  for table in ('fn2-checkpoint-projection','fn2-checkpoint-selected-source','fn2-extents','fn2-alloc-edges'):
   self.assertTrue(lr.match(f'({table}-logical-snapshot {table})',[snap]))
  self.assertTrue(lr.match('((eq mode :counts) (and counts-antecedent (eq code :totals) (equal before ?after)))',[self.body]))
 def test_actual_clear_then_forgery_then_snapshot_then_drive(self):
  flat=lr.flat(self.body).lower()
  points=[flat.index('(fn2-cpu-clear '),flat.index('(fn2-checkpoint-projection-set-retired-count '),flat.index('(before '),flat.index('(fn2-cpu-drive ')]
  self.assertEqual(points,sorted(points))
  clear=lr.match('(defun fn2-cpu-clear ?*body)',self.forms,deep=False)[0].node
  self.assertTrue(lr.match('(fn2-checkpoint-projection-step ?*args)',[clear]))
  self.assertTrue(lr.match('(= (fn2-alloc-identity-phase fn2-extents) *fn2-alloc-identity-phase-clearing*)',[clear]))
 def test_guard_inventory_equals_actual_step_carriers(self):
  domain=lr.match('(fn2-cpu-step-domain ?*carriers)',[self.body])[0].node
  runtime=lr.match('(defun fn2-checkpoint-projection-step ?*body)',lr.parse((ROOT/'books/checkpoint-projection.lisp').read_text()).forms,deep=False)[0].node
  self.assertEqual([lr.flat(x) for x in domain.items[1:]],[lr.flat(x) for x in runtime.items[2].items])
  self.assertTrue(lr.match('(fn2-checkpoint-projection-current-p ?*args)',[self.body]))
  self.assertTrue(lr.match('(fn2-alloc-identity-owner-p ?*args)',[self.body]))
 def test_all_mode_assertions_retained(self):
  for mode in ('nil',':owner',':generation',':descriptor',':collision',':duplicate-identity',':counts'):
   self.assertTrue(lr.match(f'(assert-event (fn2-cpu-run {mode}))',self.forms))
if __name__=='__main__':unittest.main()
