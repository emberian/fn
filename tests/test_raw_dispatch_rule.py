"""tools/raw_dispatch_rule.py: the raw host reaches a book function only
through the dispatcher (Codex r28-F1, by construction).

Each refusal on a minimal raw source, and the shapes the rule accepts."""
from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger, raw_dispatch_rule as rule  # noqa: E402

BOOK = {"fn-open", "fn-step", "fn-pred", "create-fn-cat"}

# The base dispatcher, as host/native/io.lisp defines it (its body is the
# rule's allow-listed internal; here it only needs its lambda list).
PRELUDE = """
(defun fnn-call (name &rest args) (apply (fnn-dispatch-function name) args))
(defun fnn-dispatch-function (name) name)
(defun fnn-core (name &rest args) (first (apply #'fnn-call name args)))
(defun fnn-fault (fmt &rest args) (error "~?" fmt args))
"""


def scan(source: str):
    forms = ledger.Reader(PRELUDE + source).top_level()
    return rule.scan_sources({"host/native/t.lisp": forms}, set(BOOK))


def rules(source: str, context: str | None = None) -> list[str]:
    return sorted({s.rule for s in scan(source).sites
                   if context is None or s.context == context
                   if s.context not in ("fnn-call", "fnn-dispatch-function")})


class Accepted(unittest.TestCase):
    def test_quoted_dispatch(self):
        self.assertEqual(rules("(defun h (x) (fnn-core 'fn-step x))"), [])

    def test_conditional_literal_names(self):
        self.assertEqual(rules("(defun h (k x) (fnn-core (if k 'fn-step 'fn-open) x))"), [])

    def test_let_bound_literal_name_used_only_as_a_name(self):
        self.assertEqual(rules("(defun h (k x) (let* ((w (case k (:a 'fn-step) (t 'fn-open)))"
                               " (y (fnn-core w x))) y))"), [])

    def test_derived_dispatcher(self):
        s = scan("(defun my-core (name &rest args) (apply #'fnn-core name args))"
                 "(defun h (x) (my-core 'fn-step x))")
        self.assertIn("my-core", s.dispatchers)
        self.assertEqual([x for x in s.sites if x.context in ("my-core", "h")], [])

    def test_apply_of_a_dispatcher(self):
        self.assertEqual(rules("(defun h (args) (apply #'fnn-core 'fn-step args))"), [])

    def test_local_dispatcher(self):
        self.assertEqual(rules("(defun h (x) (flet ((pool (name &rest a) (apply #'fnn-core name a)))"
                               " (pool 'fn-step x)))"), [])

    def test_label_and_key_positions(self):
        self.assertEqual(rules("(defun where-fault (where) (fnn-fault \"bad ~a\" where))"
                               "(defun h (x) (where-fault 'fn-step)"
                               " (assoc 'fn-cat x) (eq x 'fn-open))"), [])

    def test_host_function_values(self):
        self.assertEqual(rules("""
(defvar *hook* nil)
(defun g (x) x)
(defun run (f x) (funcall f x))
(defun h (x)
  (setq *hook* #'g)
  (funcall *hook* x)
  (run #'g x)
  (run (lambda (y) y) x)
  (dolist (f (list #'g (lambda (y) y))) (funcall f x))
  (mapcar #'g x))"""), [])

    def test_table_resolution(self):
        self.assertEqual(rules("(defun h (x) (funcall (fnn-dispatch-function 'fn-step) x))"), [])

    def test_keyword_intern(self):
        self.assertEqual(rules("(defun h (s) (intern s :keyword))"), [])


class Refused(unittest.TestCase):
    def test_funcall_of_a_quoted_book_symbol(self):
        self.assertIn("NAME", rules("(defun h (x) (funcall 'fn-open x))"))
        self.assertIn("CALL", rules("(defun h (x) (funcall 'fn-open x))"))

    def test_apply_of_a_book_function_object(self):
        self.assertEqual(rules("(defun h (x) (apply #'fn-open x))"), ["CALL", "NAME"])

    def test_book_symbol_in_quoted_data(self):
        self.assertEqual(rules("(defparameter *t* '((a . fn-open)))"), ["NAME"])

    def test_book_symbol_as_a_template_head(self):
        self.assertEqual(rules("(defmacro m (x) `(fn-open ,x))"), ["NAME"])

    def test_symbol_variable_reaching_a_call(self):
        # the symbol is made by a dispatched result: an ACL2 value is untraced
        self.assertEqual(rules("(defun h (x) (let ((f (fnn-core 'fn-pred x))) (funcall f x)))"),
                         ["CALL"])

    def test_callback_parameter_given_a_book_symbol(self):
        found = rules("(defun run (f x) (funcall f x)) (defun h (x) (run 'fn-open x))")
        self.assertIn("CALL", found)
        self.assertIn("NAME", found)

    def test_special_set_to_an_untraced_value(self):
        self.assertIn("CALL", rules("(defvar *hook* nil)"
                                    "(defun h (x) (setq *hook* (fnn-core 'fn-pred x))"
                                    " (funcall *hook* x))"))

    def test_local_reassigned_after_binding(self):
        self.assertIn("CALL", rules("(defun g (x) x)"
                                    "(defun h (x) (let ((f #'g)) (setq f (fnn-core 'fn-pred x))"
                                    " (funcall f x)))"))

    def test_variable_dispatcher_name(self):
        self.assertEqual(rules("(defun h (n x) (fnn-core (car n) x))", "h"), ["NAMEVAR"])

    def test_name_variable_used_elsewhere(self):
        found = rules("(defun h (x) (let ((w 'fn-step)) (fnn-core w x) (funcall w x)))")
        self.assertIn("NAMEVAR", found)
        self.assertIn("NAME", found)

    def test_symbol_construction(self):
        self.assertEqual(rules("(defun h (s) (intern s \"ACL2\"))"), ["MAKE"])
        self.assertEqual(rules("(defun h (s) (find-symbol s \"ACL2\"))"), ["MAKE"])
        self.assertEqual(rules("(defun h (s) (read-from-string s))"), ["MAKE"])

    def test_world_and_function_cell_reads(self):
        self.assertEqual(rules("(defun h (n) (symbol-function n))"), ["WORLD"])
        self.assertEqual(rules("(defun h () (table-alist 'fn-interfaces (w *the-live-state*)))"),
                         ["WORLD"])
        self.assertEqual(rules("(defun h (n) (eval (list n)))"), ["WORLD"])
        self.assertEqual(rules("(defun h (f) (setf (symbol-function 'fn-open) f))"),
                         ["NAME", "WORLD"])
        self.assertEqual(rules("(defun h (f) (sb-int:encapsulate 'fn-open 'x f))"),
                         ["NAME", "WORLD"])

    def test_function_cell_of_a_raw_name_is_accepted(self):
        self.assertEqual(rules("(defun g () 1) (defun h () (funcall (symbol-function 'g)))"), [])


class Judge(unittest.TestCase):
    def site(self, source):
        return scan(source)

    def test_allow_covers_its_site(self):
        s = self.site("(defun h (s) (intern s \"ACL2\"))")
        allow = [rule.Allow("MAKE", "host/native/t.lisp", "h", "why")]
        problems, covered = rule.judge(s, allow, set())
        self.assertEqual(problems, [])
        self.assertEqual(covered["allowed"], 1)

    def test_stale_allow_is_a_finding(self):
        s = self.site("(defun h (x) (fnn-core 'fn-step x))")
        allow = [rule.Allow("MAKE", "host/native/t.lisp", "h", "why")]
        problems, _ = rule.judge(s, allow, set())
        self.assertEqual(len(problems), 1)
        self.assertIn("matches no site", problems[0])

    def test_allow_never_covers_a_carried_function(self):
        s = self.site("(defparameter *t* '(fn-open))")
        allow = [rule.Allow("NAME", "host/native/t.lisp", "*t*", "why")]
        problems, _ = rule.judge(s, allow, {"fn-open"})
        self.assertEqual(len(problems), 1)
        self.assertIn("def-carried fn-open", problems[0])

    def test_uncovered_site_is_a_finding(self):
        s = self.site("(defun h (x) (funcall 'fn-open x))")
        problems, _ = rule.judge(s, [], set())
        self.assertTrue(any("NAME" in p for p in problems))
        self.assertTrue(any("CALL" in p for p in problems))


class Tree(unittest.TestCase):
    def test_the_tree_is_clean_under_its_lists(self):
        problems, covered = rule.findings()
        self.assertEqual(problems, [])
        self.assertGreater(covered["dispatchers"], len(rule.BASE_DISPATCHERS))


if __name__ == "__main__":
    unittest.main()


class DirectMacroHeads(unittest.TestCase):
    def observed(self, source, direct=("fn-open",)):
        forms = ledger.Reader(PRELUDE + source).top_level()
        result = rule.scan_sources({"host/native/t.lisp": forms}, set(BOOK), direct)
        return [s for s in result.sites if s.context == "m"]

    def test_explicit_direct_entry_permits_only_literal_emitted_call_head(self):
        self.assertTrue(self.observed("(defmacro m (x) `(fn-open ,x))") == [],
                        "declared direct macro call must follow its actual interface")
        self.assertTrue(self.observed("(defmacro m (x) `(fn-open ,x))", direct=()))

    def test_direct_declaration_does_not_permit_quoted_data_or_function_values(self):
        for source in ("(defmacro m (x) `'(fn-open ,x))",
                       "(defmacro m (x) `(list 'fn-open ,x))",
                       "(defmacro m (x) `(funcall #'fn-open ,x))"):
            with self.subTest(source=source):
                self.assertTrue(any(s.rule == "NAME" for s in self.observed(source)))

    def test_neighboring_undeclared_head_still_refuses(self):
        found = self.observed("(defmacro m (x) `(progn (fn-open ,x) (fn-step ,x)))")
        self.assertEqual([(s.rule, s.detail) for s in found], [("NAME", "template head fn-step")])
