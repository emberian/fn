"""(fnn-guarded-by VAR LOCK): the lock contract names its variable (CONVERGE-2
row 31).  tools/lock_discipline_check.py reads the form and refuses a
`guarded-by:' comment; tools/guarded_by_convert.py rewrites comment contracts
into the form, byte for byte outside the contract words."""
from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import guarded_by_convert as conv  # noqa: E402
import lock_discipline_check as ldc  # noqa: E402


def tree_of(text: str):
    with tempfile.TemporaryDirectory() as d:
        root = pathlib.Path(d)
        (root / "host" / "native").mkdir(parents=True)
        (root / "host" / "native" / "a.lisp").write_text(text)
        return ldc.collect_tree(root, ["host/native/a.lisp"])


class CheckerTests(unittest.TestCase):
    def test_the_declaration_gives_the_global_its_lock(self):
        tree = tree_of("(defvar *x* nil)\n(fnn-guarded-by *x* *fnn-extent-lock*)\n"
                       "(defvar *y* nil)\n(fnn-guarded-by *y* (fnn-owner-service-lock))\n")
        self.assertEqual(tree.globals["*x*"][2], "*fnn-extent-lock*")
        self.assertEqual(tree.globals["*y*"][2], "(fnn-owner-service-lock)")
        self.assertEqual(tree.guard_problems, [])

    def test_the_declaration_survives_a_moved_defvar(self):
        # The row 31 shape: the defvar between moves away; the contract
        # still names its own variable, and nothing falls to the neighbour.
        tree = tree_of("(defvar *a* nil)\n(fnn-guarded-by *a* (fnn-owner-service-lock))\n"
                       "(defvar *b* nil)\n")
        self.assertEqual(tree.globals["*a*"][2], "(fnn-owner-service-lock)")
        self.assertIsNone(tree.globals["*b*"][2])

    def test_a_comment_contract_is_a_problem_and_binds_nothing(self):
        tree = tree_of("(defvar *x* nil) ; guarded-by: *fnn-extent-lock*\n")
        self.assertIsNone(tree.globals["*x*"][2])
        self.assertEqual(len(tree.guard_problems), 1)
        self.assertIn("guarded-by:' comment beside *x*", tree.guard_problems[0])

    def test_a_declaration_of_no_global_or_twice_is_a_problem(self):
        tree = tree_of("(fnn-guarded-by *nope* *l*)\n(defvar *x* nil)\n"
                       "(fnn-guarded-by *x* *l*)\n(fnn-guarded-by *x* *m*)\n")
        problems = " | ".join(tree.guard_problems)
        self.assertIn("names *nope*, which no defvar defines", problems)
        self.assertIn("*x* has 2 fnn-guarded-by forms", problems)


class ConvertTests(unittest.TestCase):
    def convert(self, text):
        edits, residual = conv.plan_file(text)
        return conv.apply(text, edits), residual

    def test_same_line_comment(self):
        out, residual = self.convert(
            "(defvar *fds* (make-hash-table))   ; guarded-by: *fnn-extent-lock* (file id -> fd)\n")
        self.assertEqual(out, "(defvar *fds* (make-hash-table))   ; (file id -> fd)\n"
                              "(fnn-guarded-by *fds* *fnn-extent-lock*)\n")
        self.assertEqual(residual, [])

    def test_trailing_clause_and_bare_contract(self):
        out, _ = self.convert("(defvar *s* nil)  ; (entry key), guarded-by: *fnn-extent-lock*\n"
                              "(defvar *w* nil) ; guarded-by: *fnn-extent-lock*\n")
        self.assertEqual(out, "(defvar *s* nil)  ; (entry key)\n(fnn-guarded-by *s* *fnn-extent-lock*)\n"
                              "(defvar *w* nil)\n(fnn-guarded-by *w* *fnn-extent-lock*)\n")

    def test_following_comment_lines_and_the_owner_mutex(self):
        out, _ = self.convert("(defvar *r* nil)\n;; guarded-by: the owner mutex (file ids\n;; not yet quiet)\n"
                              "(defvar *i* nil)\n;; guarded-by: *fnn-extent-lock*.  ACL2's table\n")
        self.assertEqual(out, "(defvar *r* nil)\n(fnn-guarded-by *r* (fnn-owner-service-lock))\n"
                              ";; (file ids\n;; not yet quiet)\n"
                              "(defvar *i* nil)\n(fnn-guarded-by *i* *fnn-extent-lock*)\n;; ACL2's table\n")

    def test_refusals_are_named_residuals(self):
        text = ("(defparameter *lock* (make-mutex))\n;; guarded-by: *lock*\n"
                "(defparameter *table* (make-hash-table))\n"
                "(defvar *z* nil) ; guarded-by: wake-lock\n")
        edits, residual = conv.plan_file(text)
        self.assertEqual(edits, [])
        reasons = sorted(r[2].split(":")[0] for r in residual)
        self.assertEqual(reasons, ["lock", "self"])

    def test_an_unbound_top_level_comment_is_a_residual(self):
        text = "(defparameter *lock*\n  (make-mutex))\n;; guarded-by: *lock*\n(defparameter *t* nil)\n"
        _, residual = conv.plan_file(text)
        self.assertEqual([r[2].split(":")[0] for r in residual], ["unbound"])

    def test_the_tree_has_no_comment_contracts_left(self):
        for path in sorted((ROOT / "host" / "native").glob("*.lisp")):
            edits, residual = conv.plan_file(path.read_text(encoding="utf-8"))
            self.assertEqual((edits, residual), ([], []), path.name)


if __name__ == "__main__":
    unittest.main()
