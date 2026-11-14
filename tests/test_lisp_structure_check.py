import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from lisp_structure_check import check_source


class LispStructureCheck(unittest.TestCase):
    def test_valid_binding_tests_and_template(self):
        self.assertEqual(check_source("""
        (defun f (x) (b* (((unless (if x t nil)) :no)
                          ((mv code value) (g x)))
                         (if code value nil)))
        (defmacro m () `(let* ((x (if a b c))) (cond (x x) (t nil))))
        """), [])

    def test_balanced_but_nested_binding_is_rejected(self):
        source = "(b* (((unless good) bad ((unless next) stop) (x value))) x)"
        self.assertTrue(any("binding 0" in error for error in check_source(source)))

    def test_each_expression_shape_has_teeth(self):
        for source in ("(if test then)", "(cond (test))", "(let ((x y z)) x)",
                       "(let* (((x y) z)) x)", "(b* ((x y)) x extra)"):
            with self.subTest(source=source):
                self.assertTrue(check_source(source))

    def test_quoted_data_and_lexical_parentheses_are_ignored(self):
        self.assertEqual(check_source("'(if a b) ; (if bad\n (f #\\( \"(if bad)\")"), [])

    def test_literal_macro_event_emitter_is_checked(self):
        self.assertTrue(check_source("(defmacro events () '(progn (defun f (x) (if x t))))"))
        self.assertEqual(check_source("(defmacro events () '(progn (defun f (x) (if x t nil))))"), [])
        self.assertEqual(check_source("(defconst *data* '(progn (if x t))) (defun data () '(progn (if x t)))"), [])

    def test_real_cond_sibling_nesting_is_rejected(self):
        self.assertTrue(check_source("(cond (first (if a b c) (second d)) (t e))"))


if __name__ == "__main__":
    unittest.main()
