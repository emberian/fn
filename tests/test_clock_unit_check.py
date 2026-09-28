"""tools/clock_unit_check.py: what it flags and what it leaves alone."""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
import clock_unit_check as cuc  # noqa: E402


def sites(text):
    out = []
    cuc.sites_in(cuc.forms(text), out)
    return [op for _, op in out]


class ClockUnitCheckTests(unittest.TestCase):
    def test_arithmetic_on_a_field_is_flagged(self):
        self.assertEqual(sites("(defun f (s) (+ (fn-clock-wall s) 1000))"), ["+"])
        self.assertEqual(sites("(defun f (s) (floor (nfix (fn-clock-wall s)) 1000))"), ["floor"])
        self.assertEqual(sites("(defun f (s e) (< (fn-clock-monotonic s) e))"), ["<"])

    def test_moving_a_field_is_not_arithmetic(self):
        self.assertEqual(sites("(defun f (s) (g (fn-clock-wall s)))"), [])
        self.assertEqual(sites("(defun f (s) (+ (h (fn-clock-wall s)) 1))"), [])

    def test_statements_comments_and_strings_are_skipped(self):
        self.assertEqual(sites("(defthm t1 (< (fn-clock-wall s) (+ 1 (fn-clock-wall s))))"), [])
        self.assertEqual(sites("; (+ (fn-clock-wall s) 1)\n(defun f () \"(+ (fn-clock-wall s) 1)\")"), [])

    def test_the_baseline_only_shrinks(self):
        found = {"books/a.lisp": [(1, "+"), (2, "+")]}
        self.assertTrue(cuc.judge(found, {"books/a.lisp": 1}))
        self.assertTrue(cuc.judge(found, {"books/a.lisp": 3}))
        self.assertTrue(cuc.judge(found, {}))
        self.assertEqual(cuc.judge(found, {"books/a.lisp": 2}), [])


if __name__ == "__main__":
    unittest.main()
