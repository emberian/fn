"""Fixtures for the unchanged-event wire-lines extraction."""
import unittest
from tools.wire_lines_extract import extract, transform, NAMES


class WireLinesExtractTests(unittest.TestCase):
    def test_preserves_exact_forms_and_unselected_source(self):
        before = '; retained\n(defun one (x) ; inner\n x)\n(local (defthm one t))\n(defthm two (equal "(x)" "(x)"))\n'
        rest, forms = extract(before, ['two', 'one'])
        self.assertEqual(forms, ['(defthm two (equal "(x)" "(x)"))', '(defun one (x) ; inner\n x)'])
        self.assertEqual(rest, '; retained\n\n(local (defthm one t))\n\n')

    def test_refuses_missing_duplicate_and_nested_only(self):
        for source, names in [('(defun a () nil)', ['missing']),
                              ('(defun a () nil)(defun a () t)', ['a']),
                              ('(local (defthm a t))', ['a']),
                              ('(defun a () nil)', ['a', 'a'])]:
            with self.subTest(source=source, names=names), self.assertRaises(ValueError):
                extract(source, names)

    def test_family_selection_moves_every_event_unchanged(self):
        forms = ['(defun ' + name + ' (x) x)' for name in NAMES]
        source = '(include-book "octet-text")\n' + '\n'.join(forms)
        rest, shared = transform(source)
        self.assertEqual(rest.count('(include-book "wire-lines")'), 1)
        for form in forms:
            self.assertNotIn(form, rest)
            self.assertEqual(shared.count(form), 1)
        with self.assertRaises(ValueError):
            transform(rest)
