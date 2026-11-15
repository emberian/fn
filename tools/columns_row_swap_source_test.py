"""Canonical-schema row generator and bounded global-state effect controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
R=Path(__file__).resolve().parents[1]
class Swap(unittest.TestCase):
 def test_actual_canonical_declaration_is_the_recipe(self):
  source=(R/'books/columns-row-swap.lisp').read_text();forms=lr.parse(source).forms
  self.assertTrue(lr.match('(fn2-decl-get :columns (fn2-decl-row ?identity (w state)))',forms))
  self.assertIn("'(:columns ,name)",source)
  self.assertIn('(defcolumn-row-swap fn2-checkpoint-summary)',(R/'books/checkpoint-live-adoption-state.lisp').read_text())
 def test_concrete_body_and_named_logical_boundary(self):
  source=(R/'books/columns-row-swap.lisp').read_text()
  self.assertIn('"-REFINES-ROW-MODEL"',source)
  self.assertIn('(defun-nx fn2-columns-row-swap-model',source)
  self.assertIn('fn2-columns-swap-saves name cols',source)
  self.assertNotIn('fn2-columns-extra-specs',source)
 def test_generator_reads_both_rows_before_replacing_that_value(self):
  source=(R/'books/columns-row-swap.lisp').read_text()
  self.assertLess(source.index('fn2-columns-swap-saves name cols)',source.index('(defun fn2-columns-row-swap-events')),source.index('fn2-columns-swap-writes name cols nil)',source.index('(defun fn2-columns-row-swap-events')))
 def test_prepared_actual_guard_and_global_effect_fixture(self):
  source=(R/'tests/checkpoint-live-row-swap-unit.lisp').read_text()
  self.assertIn('(fn2-checkpoint-summary-swap-rows 0 1 fn2-checkpoint-summary)',source)
  self.assertIn('(fn2-live-adoption-swap-descriptors 0 fn2-checkpoint-summary)',source)
  self.assertIn('(and antecedent rows-swapped globals-unchanged',source)
  self.assertIn('(fn2-checkpoint-summary-next-tag fn2-checkpoint-summary) 33',source)
if __name__=='__main__':unittest.main()
