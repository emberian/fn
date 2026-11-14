import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from lisp_structure_check import ACL2_MV_LIMIT, check_source
import lisp_source


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

    def test_dynamic_template_bindings_validate_the_generator(self):
        self.assertEqual(check_source("(defmacro m () `(let* ,(bindings x) (if a b c)))"), [])
        self.assertEqual(check_source("(defmacro m () `(let* (,@(bindings x) (a b)) a))"), [])
        self.assertTrue(check_source("(defmacro m () `(let* ,(if x y) a))"))
        self.assertTrue(check_source("(defmacro m () `(let* (,@(if x y)) a))"))
        self.assertTrue(check_source("(defmacro m () `(let* ((a b c)) a))"))

    def test_real_cond_sibling_nesting_is_rejected(self):
        self.assertTrue(check_source("(cond (first (if a b c) (second d)) (t e))"))

    def test_acl2_mv_limit_counts_values_not_host_cl_capacity(self):
        self.assertEqual(ACL2_MV_LIMIT, 32)
        self.assertEqual(check_source("(mv " + " ".join(["x"] * 32) + ")"), [])
        errors = check_source("(mv " + " ".join(["x"] * 33) + ")")
        self.assertTrue(any("MV returns 33 values" in error for error in errors))

    def test_frozen_actual_root1_output_shapes_are_rejected(self):
        path = Path(__file__).parent / "fixtures/lisp_structure/root1-mv-oversized.lisp"
        errors = check_source(path.read_text())
        self.assertEqual(len(errors), 3)
        self.assertEqual(sum("returns 38 values" in error for error in errors), 1)
        self.assertEqual(sum("returns 40 values" in error for error in errors), 2)

    def test_readonly_inputs_are_not_counted_as_outputs(self):
        inputs = " ".join(f"s{i}" for i in range(37))
        self.assertEqual(check_source(
            f"(defun f ({inputs}) (declare (xargs :stobjs ({inputs})))"
            " (mv code s0 s1 s2))"), [])

    def test_reduced_count_only_root1_keeps_all_readonly_inputs(self):
        path = Path(__file__).parent / "fixtures/lisp_structure/root1-mv-reduced-count-only.lisp"
        source = path.read_text()
        forms = lisp_source.read_all(source, strict=True)
        self.assertEqual(len(forms[0].items[2].items), 37)
        self.assertEqual(len(forms[1].items[2].items), 29)
        self.assertEqual(check_source(source), [])

    def test_known_list_splices_and_lexical_aliases(self):
        children = " ".join(f"s{i}" for i in range(30))
        source = f"(defconst *outputs* '({children}))"
        self.assertEqual(check_source(source +
            "(defmacro m () (let ((outputs *outputs*)) `(mv code ,@outputs)))"), [])
        errors = check_source(source +
            "(defmacro m () (let* ((outputs *outputs*) (more (append outputs '(a b))))"
            " `(mv code ,@more)))")
        self.assertTrue(any("returns 33 values" in error for error in errors))

    def test_unknown_splice_is_explicitly_unresolved(self):
        errors = check_source("(defmacro m (outputs) `(mv code ,@outputs))")
        self.assertTrue(any("output count unresolved" in error for error in errors))
        self.assertFalse(any("MV returns" in error for error in errors))
        errors = check_source("(defmacro m (outputs) `(mv " + " ".join(["x"] * 33) +
                              " ,@outputs))")
        self.assertTrue(any("returns at least 33 values" in error for error in errors))

    def test_shadowed_lists_do_not_invent_known_macro_outputs(self):
        prefix = "(defconst outputs '(" + " ".join(["x"] * 37) + "))"
        for expression in (
            "(defmacro m (outputs) `(mv code ,@outputs))",
            "(defmacro m () (let ((outputs (unknown))) `(mv code ,@outputs)))",
            "(defmacro m () (mv-let (outputs) (unknown) `(mv code ,@outputs)))",
            "(defmacro m () (lambda (outputs) `(mv code ,@outputs)))",
        ):
            with self.subTest(expression=expression):
                errors = check_source(prefix + expression)
                self.assertTrue(any("output count unresolved" in error for error in errors))
                self.assertFalse(any("MV returns" in error for error in errors))

    def test_generated_formals_do_not_shadow_generator_splices(self):
        source = "(defconst *outputs* '(" + " ".join(["x"] * 33) + "))"
        errors = check_source(source +
            "(defmacro m () (let ((outputs *outputs*))"
            " `(defun f (outputs) (mv ,@outputs))))")
        self.assertTrue(any("returns 33 values" in error for error in errors))
        self.assertFalse(any("unresolved" in error for error in errors))

    def test_direct_quoted_macro_result_is_code_but_quoted_data_is_not(self):
        wide = "(mv " + " ".join(["x"] * 33) + ")"
        self.assertTrue(check_source(f"(defmacro m () '{wide})"))
        self.assertEqual(check_source(
            f"(defconst *data* '{wide}) (defun data () '{wide})"
            f"(defmacro quoted-data () ''{wide})"), [])

    def test_case_and_known_quoted_list_building(self):
        source = "(ACL2::DEFCONST *OUTPUTS* '(" + " ".join(["x"] * 31) + "))"
        errors = check_source(source +
            "(DEFMACRO m () (LET* ((xs (CONS 'a *OUTPUTS*))) `(ACL2::MV code ,@xs)))")
        self.assertTrue(any("returns 33 values" in error for error in errors))
        self.assertEqual(check_source(
            "(defconst *outputs* `(a b)) (defmacro m () `(mv ,@*outputs*))"), [])

    def test_nested_template_splices_are_not_claimed_expanded(self):
        errors = check_source("(defconst *xs* '(a b)) (defmacro m () ``(mv ,@*xs*))")
        self.assertTrue(any("output count unresolved" in error for error in errors))

    def test_escaped_symbol_aliases_are_not_folded_together(self):
        source = "(defconst |Xs| '(" + " ".join(["x"] * 33) + "))"
        errors = check_source(source + "(defmacro m () `(mv ,@|xs|))")
        self.assertTrue(any("output count unresolved" in error for error in errors))
        self.assertFalse(any("MV returns" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
