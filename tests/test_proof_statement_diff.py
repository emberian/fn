"""Mutation checks for the proof-only source contract."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from proof_statement_diff import compare


class Statements(unittest.TestCase):
    BASE = '(defthm t1 (equal (f x) x) :rule-classes nil :hints (("Goal" :by old)))'

    def test_hint_only_and_local_addition(self):
        changed = self.BASE.replace(':by old', ':by new')
        changed += '\n(local (defthm helper (equal x x)))'
        self.assertEqual(compare(self.BASE, changed)[1:], (['helper'], []))

    def test_formula_rules_locality_and_removal_fail(self):
        mutations = [self.BASE.replace('(f x)', '(g x)'),
                     self.BASE.replace(':rule-classes nil', ':rule-classes :rewrite'),
                     '(local ' + self.BASE + ')', '']
        for changed in mutations:
            with self.subTest(changed=changed):
                self.assertTrue(compare(self.BASE, changed)[2])

    def test_added_definition_is_not_a_local_lemma(self):
        self.assertTrue(compare('', '(local (defun f (x) x))')[2])

    def test_definition_and_macro_body_bytes(self):
        for head in ['defun', 'defmacro']:
            original = f'({head} f (x) (cons x x))'
            self.assertTrue(compare(original, original.replace('(cons x x)', '(list x)'))[2])
        self.assertTrue(compare(self.BASE, self.BASE.replace('(equal (f x) x)', '(equal  (f x) x)'))[2])

    def test_guard_hints_only(self):
        original = '(defun f (x) (declare (xargs :guard t :guard-hints (("Goal" :by a)))) x)'
        self.assertFalse(compare(original, original.replace(':by a', ':by b'))[2])

    def test_moving_event_inside_encapsulate(self):
        self.assertFalse(compare(self.BASE, '(encapsulate () ' + self.BASE + ')')[2])

    def test_hint_keywords_in_executable_data_remain_semantic(self):
        for body in ['(list :hints 1)', "'(:guard-hints 1)"]:
            original = f'(defun f (x) {body})'
            self.assertTrue(compare(original, original.replace('1', '2'))[2])
