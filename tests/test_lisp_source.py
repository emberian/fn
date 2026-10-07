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


class ReadAllTests(unittest.TestCase):
    def test_positions_and_nesting(self):
        text = "(a (b c)) d"
        outer, d = L.read_all(text)
        self.assertEqual((outer.start, outer.end), (0, 9))
        self.assertEqual((d.text, d.start, d.end), ("d", 10, 11))
        inner = outer.items[1]
        self.assertEqual([x.text for x in inner.items], ["b", "c"])
        self.assertEqual(text[inner.start:inner.end], "(b c)")

    def test_marks_ride_on_the_datum_they_precede(self):
        a, b, c, d = L.read_all("'x ,@(y) ''z #'f")[0], *L.read_all("'x ,@(y) ''z #'f")[1:]
        self.assertEqual((a.text, a.marks), ("x", ("'",)))
        self.assertEqual((b.marks, [x.text for x in b.items]), ((",@",), ["y"]))
        self.assertEqual((c.text, c.marks), ("z", ("'", "'")))
        self.assertEqual((d.text, d.marks), ("f", ("#'",)))

    def test_characters_strings_and_escaped_symbols_are_single_leaves(self):
        text = '(f #\\( #\\" #\\Space "a \\" ) ;" |x ( y| ) z'
        form, z = L.read_all(text)
        self.assertEqual([type(x).__name__ for x in form.items],
                         ["Atom", "Atom", "Atom", "Atom", "Str", "Atom"])
        self.assertEqual([x.text for x in form.items if isinstance(x, L.Atom)],
                         ["f", "#\\(", "#\\\"", "#\\Space", "|x ( y|"])
        self.assertEqual(z.text, "z")

    def test_comments_vanish_even_nested(self):
        self.assertEqual([x.text for x in L.read_all("a #| b #| c |# d |# e ; f\ng")],
                         ["a", "e", "g"])

    def test_string_value_resolves_escapes(self):
        (s,) = L.read_all('"a\\"b\\\\c"')
        self.assertEqual(L.string_value(s.text), 'a"b\\c')
        self.assertEqual(L.string_value('"open'), "open")

    def test_lenient_and_strict_unbalanced(self):
        stray, = L.read_all(") x")
        self.assertEqual(stray.text, "x")
        (unclosed,) = L.read_all("(a (b")
        self.assertEqual(unclosed.end, 5)
        with self.assertRaises(L.ReadError) as close:
            L.read_all("(a) )", strict=True)
        self.assertEqual((close.exception.kind, close.exception.offset), ("close", 4))
        with self.assertRaises(L.ReadError) as opened:
            L.read_all("x (a (b", strict=True)
        self.assertEqual((opened.exception.kind, opened.exception.offset), ("open", 2))

    def test_first_only_and_start(self):
        self.assertEqual(len(L.read_all("(a) (b)", first_only=True)), 1)
        (b,) = L.read_all("(a) (b)", start=3, first_only=True)
        self.assertEqual(b.start, 4)

    def test_line_numberer(self):
        line = L.line_numberer("a\nb\n\nc")
        self.assertEqual([line(i) for i in (0, 1, 2, 4, 5)], [1, 1, 2, 3, 4])


if __name__ == "__main__":
    unittest.main()
