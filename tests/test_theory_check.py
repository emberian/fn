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


if __name__ == "__main__":
    unittest.main()
