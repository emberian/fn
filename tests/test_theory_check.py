"""tools/theory_check.py reads the one habit the 2026-09-22 freeze paid for."""
from __future__ import annotations

import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import theory_check  # noqa: E402


class ReaderTests(unittest.TestCase):
    def test_top_level_forms_survive_comments_strings_and_quotes(self):
        text = ('; a comment (with parens)\n(in-package "ACL2") #| block (x) |#\n'
                "(local (in-theory (enable fn-a-vocabulary (:d fn-b) (:e fn-c))))\n"
                '(defthm t1 (equal "a ) string" "a ) string")\n'
                "  :hints ((\"Goal\" :in-theory (enable fn-inside-a-hint))))\n"
                "(in-theory (e/d (fn-d) (fn-e)))\n")
        self.assertEqual(theory_check.top_level_openings(text),
                         [["fn-a-vocabulary", "fn-b"], ["fn-d"]])

    def test_a_hint_inside_a_theorem_is_not_a_top_level_opening(self):
        text = '(defthm t1 t :hints (("Goal" :in-theory (enable fn-codec-vocabulary))))\n'
        self.assertEqual(theory_check.top_level_openings(text), [])

    def test_an_unbalanced_book_is_reported_not_guessed(self):
        with self.assertRaises(ValueError):
            theory_check.forms("(in-theory (enable a)")


class AuditTests(unittest.TestCase):
    def test_a_codec_theory_is_one_defined_in_a_codec_book_or_named_codec(self):
        with tempfile.TemporaryDirectory() as directory:
            books = pathlib.Path(directory)
            (books / "cbor.lisp").write_text("(deftheory fn-cbor-record-vocabulary '(a))\n")
            (books / "wire.lisp").write_text("(deftheory fn-wire-vocabulary '(b))\n")
            (books / "opens-cbor.lisp").write_text(
                "(local (in-theory (enable fn-cbor-record-vocabulary fn-wire-vocabulary)))\n")
            (books / "opens-wire.lisp").write_text(
                "(local (in-theory (enable fn-wire-vocabulary)))\n")
            (books / "opens-named.lisp").write_text(
                "(in-theory (enable fn-somewhere-codec-vocabulary))\n")
            (books / "clean.lisp").write_text(
                '(defthm t1 t :hints (("Goal" :in-theory (enable fn-cbor-record-vocabulary))))\n')
            report = theory_check.audit(books)
        rows = {row["book"]: row for row in report["rows"]}
        self.assertEqual(report["books_with_top_level_openings"], 3)
        self.assertEqual(report["books_opening_a_codec"], 2)
        self.assertEqual(rows["books/opens-cbor"]["codec"], ["fn-cbor-record-vocabulary"])
        self.assertEqual(rows["books/opens-named"]["codec"], ["fn-somewhere-codec-vocabulary"])
        self.assertEqual(rows["books/opens-wire"]["codec"], [])
        self.assertNotIn("books/clean", rows)
        self.assertEqual([row["book"] for row in report["rows"]][:2],
                         ["books/opens-cbor", "books/opens-named"])

    def test_the_summary_and_table_carry_the_counts_and_the_names(self):
        report = {"books_read": 9, "books_with_top_level_openings": 2,
                  "books_opening_a_codec": 1, "codec_theories": ["fn-x-codec-vocabulary"],
                  "rows": [{"book": "books/a", "opened": ["fn-x-codec-vocabulary"],
                            "codec": ["fn-x-codec-vocabulary"]},
                           {"book": "books/b", "opened": ["fn-y"], "codec": []}]}
        self.assertIn("2 of 9 books", theory_check.summary(report))
        self.assertIn("1 above the codec layer open a CODEC", theory_check.summary(report))
        lines = theory_check.table(report)
        self.assertTrue(lines[1].startswith("codec  books/a"))
        self.assertTrue(lines[2].startswith("       books/b"))


class RealTreeTests(unittest.TestCase):
    def test_every_book_reads_and_the_command_line_runs(self):
        report = theory_check.audit()
        self.assertEqual([row for row in report["rows"] if "unreadable" in row], [])
        self.assertGreater(report["books_read"], 200)
        result = subprocess.run([sys.executable, str(ROOT / "tools" / "theory_check.py"),
                                 "--summary"], capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.startswith("theory-check:"), result.stdout)


class BookOrderTests(unittest.TestCase):
    """obstructions-7 items 56 and 65: guard verification ahead of a
    callee's; mv-nth enabled in a book's theory."""

    def setUp(self):
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "tools"))
        import theory_check
        self.tc = theory_check

    def test_a_verification_before_its_callees_is_named(self):
        book = """(in-package "ACL2")
(defun g (x) (declare (xargs :guard t :verify-guards nil)) x)
(defun f (x) (declare (xargs :guard t)) (g x))
(verify-guards g)
"""
        found = self.tc.guard_order(book)
        self.assertEqual(len(found), 1, found)
        self.assertIn("form #3 verifies the guards of f, which calls g", found[0])
        self.assertIn("only at form #4", found[0])
        # In order: nothing.
        good = book.replace("(verify-guards g)\n", "").replace(
            "(defun f", "(verify-guards g)\n(defun f")
        self.assertEqual(self.tc.guard_order(good), [])
        # A later verify-guards of f itself, after g's, is fine; one before is not.
        late = """(defun g (x) (declare (xargs :verify-guards nil)) x)
(defun f (x) (declare (xargs :verify-guards nil)) (g x))
(verify-guards f)
(verify-guards g)
"""
        self.assertEqual(len(self.tc.guard_order(late)), 1)
        # An mbe's :logic callee needs no guard verification.
        logic = """(defun g (x) (declare (xargs :verify-guards nil)) x)
(defun f (x) (declare (xargs :guard t)) (mbe :logic (g x) :exec x))
(verify-guards g)
"""
        self.assertEqual(self.tc.guard_order(logic), [])

    def test_mv_nth_enabled_at_the_top(self):
        self.assertTrue(self.tc.mv_nth_opened("(local (in-theory (enable mv-nth car-cons)))"))
        self.assertTrue(self.tc.mv_nth_opened("(in-theory (e/d (mv-nth) (foo)))"))
        self.assertFalse(self.tc.mv_nth_opened("(in-theory (disable mv-nth))"))
        self.assertFalse(self.tc.mv_nth_opened(
            "(defthm x t :hints ((\"Goal\" :in-theory (enable mv-nth))))"))


class RestoreTests(unittest.TestCase):
    def audit_tree(self, preload=False, local=False, declaration=True,
                   hidden=False, exported=""):
        with tempfile.TemporaryDirectory() as directory:
            books = pathlib.Path(directory)
            (books / "lib").mkdir()
            (books / "lib/shared.lisp").write_text('(in-package "ACL2")\n' + exported)
            (books / "own-leaf.lisp").write_text('(include-book "lib/shared")\n')
            (books / "own-root.lisp").write_text('(include-book "own-leaf")\n')
            # A local include in another book is still an outside consumer.
            (books / "lib/consumer.lisp").write_text('(local (include-book "shared"))\n')
            restore = "(in-theory (union-theories (theory 'before) " \
                      "(set-difference-theories (current-theory :here) " \
                      "(universal-theory 'after))))"
            (books / "exporter.lisp").write_text(
                ('; theory-restore-own-family before: own-*\n' if declaration else '') +
                ('; theory-restore-hidden-shared before: lib/* -- consumers restore shared-exported\n'
                 if hidden else '') +
                ('(include-book "lib/shared")\n' if preload else '') +
                '(deftheory before (current-theory :here))\n'
                '(include-book "own-root")\n'
                '(deftheory after (current-theory :here))\n' +
                ('(local ' + restore + ')' if local else restore) + '\n')
            return theory_check.restore_audit(books)

    def test_shared_dependency_preloaded_passes(self):
        report = self.audit_tree(preload=True)
        self.assertEqual(report["findings"], [])
        self.assertEqual(report["regions"][0]["first_loads"], ["own-leaf", "own-root"])

    def test_first_loaded_shared_dependency_fails_with_evidence(self):
        report = self.audit_tree()
        self.assertEqual(len(report["findings"]), 1)
        self.assertIn("first-loads shared books/lib/shared", report["findings"][0])
        self.assertIn("outside includer books/lib/consumer", report["findings"][0])

    def test_hidden_shared_with_exported_theory_passes(self):
        report = self.audit_tree(hidden=True, exported="(deftheory shared-exported nil)\n")
        self.assertEqual(report["findings"], [])
        self.assertIn("lib/shared", report["regions"][0]["first_loads"])
        self.assertEqual(report["regions"][0]["hidden_shared"]["reason"],
                         "consumers restore shared-exported")

    def test_hidden_shared_without_exported_theory_is_still_a_finding(self):
        for exported in ("", "(deftheory shared-other nil)\n",
                         "(local (deftheory shared-exported nil))\n"):
            with self.subTest(exported=exported):
                report = self.audit_tree(hidden=True, exported=exported)
                self.assertEqual(len(report["findings"]), 1)
                self.assertIn("hidden-shared books/lib/shared has no non-local "
                              "*-exported deftheory", report["findings"][0])

    def test_new_export_requires_family_declaration(self):
        self.assertIn("missing theory-restore-own-family", self.audit_tree(
            preload=True, declaration=False)["findings"][0])

    def test_local_restore_is_reported_but_does_not_export_disables(self):
        report = self.audit_tree(local=True, declaration=False)
        self.assertEqual(report["findings"], [])
        self.assertTrue(report["regions"][0]["local"])

    def test_deflabel_restore_retains_new_rules_and_has_no_shared_loads(self):
        with tempfile.TemporaryDirectory() as directory:
            books = pathlib.Path(directory)
            (books / "own-io.lisp").write_text('(in-package "ACL2")\n')
            (books / "exporter.lisp").write_text(
                '; theory-restore-own-family entry: own-*\n'
                '(deflabel entry)\n(include-book "own-io")\n'
                "(in-theory (union-theories (current-theory 'entry) "
                "(set-difference-theories (current-theory :here) "
                "(universal-theory 'entry))))\n")
            report = theory_check.restore_audit(books)
        self.assertEqual(report["findings"], [])
        self.assertEqual(report["regions"][0]["first_loads"], ["own-io"])


if __name__ == "__main__":
    unittest.main()
