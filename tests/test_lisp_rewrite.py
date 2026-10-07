"""tests/test_lisp_rewrite.py: the shared reader / matcher / printer / writer.

Round trips run on real books of the tree (variety noted per name).  No book in
the tree contains a #| |# block comment, so those are covered by synthetic text.
"""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import lisp_rewrite as lr  # noqa: E402

BOOKS = ROOT / "books"
FIX = ROOT / "tests" / "fixtures" / "lisp_rewrite"

ROUND_TRIP_BOOKS = [
    "nntp-auth", "served-catalog", "catalog-logic", "native-operator",  # the four biggest
    "lace", "statement",                      # package prefixes (pkg::sym)
    "def-carried", "defkeystone", "def-holder", "injection-info-params",  # strings with \"
    "account-list", "app-journal", "bp-authored-wire", "bp-eid-shape",   # #\ characters
    "acceptance-alloc", "assumptions-pgs-host-io", "body-chunks", "auth-secret",  # |pipes|
    "hmac-sha256", "deflate-inflate", "catalog-commit",                  # #x literals
    "acceptance-binding", "owner-feed", "config",                        # defpkg / big macros
]


class RoundTrip(unittest.TestCase):
    def test_real_books_parse_then_write_is_byte_identical(self):
        self.assertGreaterEqual(len(ROUND_TRIP_BOOKS), 15)
        for name in ROUND_TRIP_BOOKS:
            path = BOOKS / f"{name}.lisp"
            with self.subTest(book=name):
                p = lr.parse(path)
                self.assertGreater(len(p.forms), 0)
                out = lr.write(p.text, []).encode("utf-8", "surrogateescape")
                self.assertEqual(out, path.read_bytes())
                for f in p.forms:  # spans are exact: each top form is a balanced list
                    self.assertEqual((p.text[f.start], p.text[f.end - 1]), ("(", ")"))

    def test_book_features_really_present(self):
        feats = {"lace": "::", "def-carried": '\\"', "account-list": "#\\", "hmac-sha256": "#x",
                 "acceptance-alloc": "|"}
        for name, needle in feats.items():
            self.assertIn(needle, (BOOKS / f"{name}.lisp").read_text(), name)

    def test_nested_block_comments_and_odd_atoms(self):
        text = ('#| outer #| inner (|# still ) comment |#\n'
                '(a ; trailing ( \n'
                ' "s\\"(" #\\( #\\) #\\Space |p ( q| pkg::sym ACL2::|X y| 1/2 -3.5e2 #xFF #b101\n'
                ' \'x `(y ,z ,@w) #\'car #(1 2))\r\n#|tail|#')
        p = lr.parse(text)
        self.assertEqual(len(p.forms), 1)
        self.assertEqual(lr.write(p.text, []), text)
        kinds = [(i.text, i.kind) for i in p.forms[0].items if isinstance(i, lr.Atom)]
        self.assertIn(("#\\(", "char"), kinds)
        self.assertIn(('"s\\"("', "string"), kinds)
        self.assertIn(("-3.5e2", "number"), kinds)
        self.assertIn(("#xFF", "number"), kinds)
        self.assertIn(("|p ( q|", "symbol"), kinds)
        self.assertIn(("ACL2::|X y|", "symbol"), kinds)
        self.assertEqual(len([c for c in p.comments if c[1].startswith("#|")]), 2)
        self.assertEqual(p.forms[0].comments, ["; trailing ( "])
        self.assertTrue(p.forms[0].has_comment)

    def test_byte_spans_with_non_ascii(self):
        p = lr.parse("(a \"é\")\n(b)")
        self.assertEqual(p.byte_span(p.forms[1]), (p.forms[1].start + 1, p.forms[1].end + 1))

    def test_parse_accepts_path_text_and_name(self):
        path = BOOKS / "lace.lisp"
        self.assertEqual(lr.parse(path).text, lr.parse(str(path)).text)
        self.assertEqual(lr.parse("(a b)").text, "(a b)")


class Writes(unittest.TestCase):
    TEXT = "; head\n(defun f (x) x) ; keep\n\n#| blk |#\n(defun g (y) \"a)b\")\n(h)\n"

    def test_edits_stay_inside_their_spans(self):
        p = lr.parse(self.TEXT)
        f, g, h = p.forms
        out = lr.write(p.text, [(g.start, g.end, "(defun g (y) y)"), (h.start, h.end, "")])
        self.assertEqual(out[:g.start], p.text[:g.start])           # before, byte for byte
        self.assertEqual(out[g.start + len("(defun g (y) y)"):], p.text[g.end:h.start] + p.text[h.end:])
        self.assertEqual(out, "; head\n(defun f (x) x) ; keep\n\n#| blk |#\n(defun g (y) y)\n\n")

    def test_edit_order_does_not_matter_and_inserts_work(self):
        a = lr.write("abcdef", [(4, 5, "X"), (1, 2, "Y"), (3, 3, "Z"), (0, 0, "^")])
        self.assertEqual(a, "^aYcZdXf")
        self.assertEqual(lr.write("abc", []), "abc")

    def test_overlap_and_range_refused(self):
        with self.assertRaises(lr.EditError):
            lr.write("abcdef", [(1, 4, "x"), (3, 5, "y")])
        with self.assertRaises(lr.EditError):
            lr.write("abc", [(2, 9, "")])
        with self.assertRaises(lr.EditError):
            lr.write("abc", [(2, 1, "")])


class Matches(unittest.TestCase):
    def test_head_name_arity_and_captures(self):
        p = lr.parse("(defun f (x) (car x))\n(defun g (x y) (cons x y))\n(defthm f-ok (consp (f x)))")
        ms = lr.match("(defun ?name ?args ?*body)", p)
        self.assertEqual([m.captures["name"].text for m in ms], ["f", "g"])
        self.assertEqual([lr.flat(m.captures["args"]) for m in ms], ["(x)", "(x y)"])
        self.assertEqual([len(m.captures["body"]) for m in ms], [1, 1])
        for m in ms:
            self.assertEqual(p.text[m.start:m.end].split()[0], "(defun")
        self.assertEqual([m.node.items[1].text for m in lr.match(None, p, head="DEFUN", arity=3)], ["f", "g"])
        self.assertEqual([m.node.items[1].text for m in lr.match(None, p, name="g")], ["g"])
        self.assertEqual(len(lr.match(None, p, head="defun", arity=lambda k: k == 3)), 2)

    def test_deep_where_and_nonlinear_variables(self):
        p = lr.parse("(f (if (consp x) (car x) nil) (if (atom y) 1 2) (if (consp z) (car w) nil))")
        deep = lr.match("(if (consp ?v) (car ?v) nil)", p)
        self.assertEqual([lr.flat(m.captures["v"]) for m in deep], ["x"])  # z/w differ
        self.assertEqual(len(lr.match("(if _ _ _)", p)), 3)
        self.assertEqual(len(lr.match("(if _ _ _)", p, deep=False)), 0)
        self.assertEqual(len(lr.match("(if ?t ?a ?b)", p, where=lambda m: lr.flat(m.captures["a"]) == "1")), 1)

    def test_case_insensitive_symbols_exact_strings_and_quote(self):
        p = lr.parse('(DefUn F () "Abc" \'(1 . 2))')
        self.assertEqual(len(lr.match('(defun f () "Abc" \'?q)', p)), 1)
        self.assertEqual(len(lr.match('(defun f () "abc" _)', p)), 0)

    def test_splice_capture_in_the_middle(self):
        p = lr.parse("(a b c d e)")
        m = lr.match("(a ?*mid e)", p)[0]
        self.assertEqual([x.text for x in m.captures["mid"]], ["b", "c", "d"])
        self.assertEqual(lr.match("(a ?*mid z)", p), [])


class Refusals(unittest.TestCase):
    def refused(self, text, needle):
        with self.assertRaises(lr.Unsupported) as c:
            lr.parse(text)
        self.assertIn(needle, c.exception.reason)

    def test_read_eval(self):
        self.refused("(a #.(+ 1 2))", "read-eval")

    def test_feature_expressions(self):
        self.refused("(a #+sbcl b)", "feature-expression")
        self.refused("(a #-sbcl b)", "feature-expression")

    def test_other_dispatch_macros(self):
        self.refused("(a #c(1 2))", "dispatch macro #c")
        self.refused("(a #1=(b))", "dispatch macro #1")
        self.refused("(a #<foo>)", "dispatch macro #<")

    def test_malformed_input(self):
        for bad in ["(a", "a)", '"abc', "#| x", "'", "(a . )(", "#\\"]:
            with self.subTest(bad=bad), self.assertRaises(lr.ReadError):
                lr.parse(bad)

    def test_a_real_host_file_is_refused_by_name(self):
        with self.assertRaises(lr.Unsupported):
            lr.parse(ROOT / "host" / "native" / "io.lisp")

    def test_emit_refuses_to_drop_comments(self):
        p = lr.parse("(a ; note\n b)")
        with self.assertRaises(lr.CommentLoss):
            lr.emit(p.forms[0])
        self.assertEqual(lr.emit(p.forms[0], drop_comments=True), "(a b)")


class Emit(unittest.TestCase):
    def test_short_forms_stay_flat(self):
        p = lr.parse("(let ((a 1)) (f a 'b `(c ,d ,@e) #'g))")
        self.assertEqual(lr.emit(p.forms[0]), "(let ((a 1)) (f a 'b `(c ,d ,@e) #'g))")

    def test_defun_house_layout(self):
        p = lr.parse("(defun f (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))")
        self.assertEqual(lr.emit(p.forms[0]),
                         "(defun f (x)\n  (declare (xargs :guard t))\n  (if (consp x) (car x) nil))")

    def test_defthm_keyword_pairs_and_wrapping(self):
        p = lr.parse("(defthm t1 (equal (f x) y) :hints ((\"Goal\" :in-theory (enable f))) :rule-classes nil)")
        self.assertEqual(lr.emit(p.forms[0]),
                         '(defthm t1\n  (equal (f x) y)\n  :hints (("Goal" :in-theory (enable f)))\n  :rule-classes nil)')

    def test_long_if_and_call_wrap_within_width(self):
        p = lr.parse("(if (and (aaaaaaaaaaaaaaaa x) (bbbbbbbbbbbbbbbbbbbb y) (cccccccccccccccc z)) "
                     "(ddddddddddddddddd (eeeeeeeeeeeeeeee x y z) (ffffffffffffffff x)) (g nil))")
        out = lr.emit(p.forms[0], width=60)
        self.assertEqual(out, "\n".join([
            "(if (and (aaaaaaaaaaaaaaaa x)",
            "         (bbbbbbbbbbbbbbbbbbbb y)",
            "         (cccccccccccccccc z))",
            "    (ddddddddddddddddd (eeeeeeeeeeeeeeee x y z)",
            "                       (ffffffffffffffff x))",
            "  (g nil))"]))
        self.assertTrue(all(len(l) <= 60 for l in out.split("\n")))

    def test_emit_reads_back_equal(self):
        for name in ["lace", "statement", "hmac-sha256"]:
            p = lr.parse(BOOKS / f"{name}.lisp")
            for f in p.forms:
                if isinstance(f, lr.Lst) and f.has_comment:
                    continue
                for layout in ("house", "aligned"):
                    q = lr.parse(lr.emit(f, layout=layout))
                    self.assertEqual(len(q.forms), 1, (name, f.start))
                    self.assertEqual(lr.flat(q.forms[0]), lr.flat(f), (name, f.start, layout))


class DefBufferFixtures(unittest.TestCase):
    """Deputy S's def-buffer clones (lane s-frame-fill groups A/B): after the
    drain each clone is one `(def-buffer NAME)` line, which a def-buffer
    drain must be able to find and replace exactly."""

    def test_def_buffer_lines_found_and_replaced_in_place(self):
        for name, bufs in [("receive-octet-buffer", ["fn-octets-rx"]),
                           ("payload-extent-read", ["fn-octets-rd"])]:
            p = lr.parse(FIX / f"{name}.lisp")
            ms = lr.match("(def-buffer ?name)", p, deep=False)
            self.assertEqual([m.captures["name"].text for m in ms], bufs)
            m = ms[0]
            out = lr.write(p.text, [(m.start, m.end, "(def-buffer " + bufs[0] + " :view t)")])
            self.assertEqual(out[:m.start], p.text[:m.start])
            self.assertEqual(out[m.start + len("(def-buffer " + bufs[0] + " :view t)"):], p.text[m.end:])
            self.assertEqual(len(lr.parse(out).forms), len(p.forms))


if __name__ == "__main__":
    unittest.main()
