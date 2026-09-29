"""tools/raw_depth_check.py: raw Lisp tail positions, local functions, threads, the baseline."""
import tempfile
import unittest
from pathlib import Path

from tools import raw_depth_check as r


def rows_of(text):
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "host" / "native").mkdir(parents=True)
        (root / "host" / "native" / "x.lisp").write_text(text)
        rows, _size = r.findings(root)
        return {row["function"]: row for row in rows}


class RawTailTests(unittest.TestCase):
    def test_a_cons_around_the_recursion_is_found(self):
        self.assertIn("f", rows_of("(defun f (x) (if (consp x) (cons (car x) (f (cdr x))) nil))"))

    def test_an_accumulator_loop_is_not(self):
        self.assertEqual(rows_of("(defun f (x acc) (if (consp x) (let ((y (car x)))"
                                 " (f (cdr x) (cons y acc))) acc))"), {})

    def test_a_special_binding_is_not_a_tail_context(self):
        self.assertIn("f", rows_of("(defun f (x) (let ((*depth* 1)) (if x (f (cdr x)) nil)))"))

    def test_handler_case_and_loop_bodies_are_not_tail(self):
        self.assertIn("f", rows_of("(defun f (x) (handler-case (f (cdr x)) (error () nil)))"))
        self.assertIn("f", rows_of("(defun f (x) (dolist (y x) (f y)))"))

    def test_mutual_recursion_through_a_callee(self):
        found = rows_of("(defun a (x) (progn (b x) nil)) (defun b (x) (when x (a (cdr x))))")
        self.assertIn("a", found)
        self.assertNotIn("b", found)  # b's call to a is its tail

    def test_a_labels_function_is_its_own_definition(self):
        found = rows_of("(defun f (xs) (labels ((walk (x) (if x (1+ (walk (cdr x))) 0)))"
                        " (walk xs)))")
        self.assertIn("f/walk", found)
        self.assertNotIn("f", found)

    def test_a_new_threads_function_runs_on_its_own_stack(self):
        self.assertEqual(rows_of("(defun f (s) (sb-thread:make-thread (lambda () (f s))) s)"), {})

    def test_a_lambda_argument_runs_on_this_stack(self):
        self.assertIn("f", rows_of("(defun f (s) (call-with s (lambda () (f s))) s)"))


class RawBaselineTests(unittest.TestCase):
    ROW = {"function": "f", "where": "host/native/x.lisp:1", "nontail_calls": ["f"],
           "component": ["f"]}

    def test_an_unlisted_finding_fails(self):
        p = r.check([self.ROW], {"bounded": {}, "debt": {}}, constants=set())
        self.assertTrue(p and "raw_depth_baseline.json" in p[0])

    def test_operator_data_is_not_a_bound(self):
        p = r.check([self.ROW], {"bounded": {"f": "walks the operator's peer table"},
                                 "debt": {}}, constants=set())
        self.assertTrue(any("names no bound" in x for x in p))

    def test_a_named_constant_is(self):
        self.assertEqual(r.check([self.ROW], {"bounded": {"f": "depth <= *fn-x*"}, "debt": {}},
                                 constants={"*fn-x*"}), [])

    def test_a_listed_function_that_no_longer_recurses_fails(self):
        p = r.check([], {"bounded": {}, "debt": {"f": "D27: a walk"}}, constants=set())
        self.assertTrue(any("no longer" in x for x in p))

    def test_the_tree_is_clean(self):
        rows, _ = r.findings()
        self.assertEqual(r.check(rows, r.load_baseline()), [])


if __name__ == "__main__":
    unittest.main()
