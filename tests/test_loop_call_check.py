"""tools/loop_call_check.py: which host loops count as per-iteration call/lock sites."""
import tempfile
import unittest
from pathlib import Path

from tools import loop_call_check as c


def sites_of(text):
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "x.lisp"
        p.write_text(text)
        return [(s["defun"], s["loop"], s["does"]) for s in c.scan([p])]


class SiteTests(unittest.TestCase):
    def test_a_loop_dispatching_to_acl2_is_a_site(self):
        self.assertEqual(
            sites_of("(defun f (n) (dotimes (i n) (fnn-core-pool 'fn-get i)))"),
            [("f", "dotimes", "call")])

    def test_a_loop_taking_a_lock_is_a_site(self):
        self.assertEqual(
            sites_of("(defun f (xs) (dolist (x xs) (fnn-with-observed-mutex (l :extent) (g x))))"),
            [("f", "dolist", "lock")])

    def test_a_loop_that_does_neither_is_not(self):
        self.assertEqual(sites_of("(defun f (xs) (dolist (x xs) (print x)))"), [])

    def test_a_call_outside_any_loop_is_not(self):
        self.assertEqual(sites_of("(defun f (x) (fnn-core 'fn-a x))"), [])

    def test_the_tree_is_at_its_baseline(self):
        self.assertEqual(c.main([]), 0)


if __name__ == "__main__":
    unittest.main()
