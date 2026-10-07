"""tools/lisp_source.py: the one Lisp source reader the checkers share."""
from __future__ import annotations

import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import lisp_source as L  # noqa: E402


class FormsTests(unittest.TestCase):
    def test_character_literals_are_not_strings_or_parens(self):
        text = ("(defun esc (c) (member c '(#\\\" #\\\\)))\n"
                "(defun open-p (c) (eql c #\\())\n"
                "(defun semi-p (c) (eql c #\\;))\n"
                "(defun after () 1)\n")
        self.assertEqual([f.split()[1] for f in L.forms(text)],
                         ["esc", "open-p", "semi-p", "after"])

    def test_store_write_host_keeps_every_definition(self):
        # The `#\"' at host/store-write-host.lisp:160 made the old splitter
        # read the rest of the file as one string (48 of 162 forms).
        text = (ROOT / "host" / "store-write-host.lisp").read_text()
        heads = sum(1 for line in text.splitlines() if line.startswith("("))
        self.assertEqual(len(L.forms(text)), heads)

    def test_block_comments_nest_and_strings_escape(self):
        text = ('#| outer #| inner (a |# still (b |#\n'
                '(defun s () "a \\" ) ( ;")\n'
                '; (not a form\n'
                '(defun t2 () |odd ) symbol|)\n')
        self.assertEqual([f.split()[1] for f in L.forms(text)], ["s", "t2"])

    def test_named_character(self):
        self.assertEqual(L.forms("(f #\\Space) (g #\\a)"), ["(f #\\Space)", "(g #\\a)"])


class CodeOnlyTests(unittest.TestCase):
    def test_blanks_comments_and_strings_keeps_characters(self):
        text = '(f "call (g)" #\\" x) ; (h)\n#| (k) |#(m)'
        self.assertEqual(L.code_only(text), '(f   #\\" x) \n (m)')


class ReadSexpTests(unittest.TestCase):
    def test_quote_marks_read_as_the_lisp_reader_reads_them(self):
        tree = L.read_sexp("(a 'b #'c `(d ,e ,@f) \"s\" #\\( |G h|)")
        self.assertEqual(tree, ["a", ["quote", "b"], ["function", "c"],
                                ["quasiquote", ["d", ["unquote", "e"],
                                                ["unquote-splicing", "f"]]],
                                "#\\(", "|g h|"])

    def test_first_datum_only(self):
        self.assertEqual(L.read_sexp("; c\n(a (b)) (c)"), ["a", ["b"]])
        self.assertEqual(L.read_sexp("  atom (x)"), "atom")
        self.assertIsNone(L.read_sexp("; nothing\n"))

    def test_nested_quote(self):
        self.assertEqual(L.read_sexp("''x"), ["quote", ["quote", "x"]])


if __name__ == "__main__":
    unittest.main()
