"""tools/generator_twin_check.py: each twin kind is found, a backquoted template
and fn-octets itself are not, and the baseline only shrinks (a new twin, a
stale row and a raise without an ACK all fail)."""
import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import generator_twin_check as g  # noqa: E402

OCTET_CLONE = """(in-package "ACL2")
(defstobj fn-foo$c
  (fn-foo$c-arr :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-foo$c-len :type (integer 0 *) :initially 0)
  :congruent-to fn-octets)
"""
FIELD_COPY = """(in-package "ACL2")
(defstobj fn-bar
  (fn-bar-arr :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-bar-len :type (integer 0 *) :initially 0))
"""
BASE = """(in-package "ACL2")
(defstobj fn-octets$c
  (fn-octets$c-arr :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-octets$c-len :type (integer 0 *) :initially 0))
"""
TEMPLATE = """(in-package "ACL2")
(defmacro def-buffer (name)
  `(defstobj ,name
     (arr :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
     (len :type (integer 0 *) :initially 0)
     :congruent-to fn-octets))
"""
FOUNDATION = """(in-package "ACL2")
(defstobj fn-rec$c (fn-rec$c-rows :type (array t (0)) :resizable t))
"""
ABSTRACT = """(in-package "ACL2")
(include-book "rec-foundation")
(defabsstobj fn-rec :foundation fn-rec$c :recognizer (fn-recp :logic fn-rec$ap :exec fn-rec$cp))
"""
GENERATED = """(in-package "ACL2")
(defabsstobj fn-gen :foundation fn-gen-cols :recognizer (fn-genp :logic fn-gen$ap :exec fn-gen-colsp))
"""


class Tree:
    def __init__(self, books, baseline=None):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "books").mkdir()
        for name, text in books.items():
            (self.root / "books" / f"{name}.lisp").write_text(text)
        self.baseline = self.root / "baseline.json"
        if baseline is not None:
            self.baseline.write_text(json.dumps({"comment": "", "rows": baseline}))
        self.acks = self.root / "ACKS.md"
        self.acks.write_text("")

    def rows(self):
        rows, _, bad = g.twins(sorted((self.root / "books").glob("*.lisp")), self.root)
        return rows, bad

    def check(self):
        out = io.StringIO()
        with redirect_stdout(out):
            code = g.main(["--check", "--books-dir", str(self.root / "books"),
                           "--baseline", str(self.baseline)])
        return code, out.getvalue()


def row(count, kinds):
    return {"kinds": kinds, "count": count, "reason": "test"}


class Case(unittest.TestCase):
    def tree(self, *args):
        t = Tree(*args)
        self.addCleanup(t.tmp.cleanup)
        return t


class Kinds(Case):
    def test_congruent_clone(self):
        rows, bad = self.tree({"foo": OCTET_CLONE}).rows()
        self.assertEqual(bad, [])
        self.assertEqual(rows, {"books/foo.lisp": {"kinds": ["octet-clone"], "count": 1}})

    def test_field_for_field_copy(self):
        rows, _ = self.tree({"bar": FIELD_COPY}).rows()
        self.assertEqual(rows, {"books/bar.lisp": {"kinds": ["octet-clone"], "count": 1}})

    def test_base_and_template_exempt(self):
        rows, _ = self.tree({"octets-stobj": BASE, "def-buffer": TEMPLATE}).rows()
        self.assertEqual(rows, {})

    def test_record_stobj_counts_against_the_foundation_book(self):
        rows, _ = self.tree({"rec-foundation": FOUNDATION, "rec": ABSTRACT}).rows()
        self.assertEqual(rows, {"books/rec-foundation.lisp": {"kinds": ["record-stobj"], "count": 1}})

    def test_generated_foundation_is_not_seen(self):
        rows, _ = self.tree({"gen": GENERATED}).rows()
        self.assertEqual(rows, {})


class Ratchet(Case):
    def test_baselined_twin_passes(self):
        code, out = self.tree({"foo": OCTET_CLONE}, {"books/foo.lisp": row(1, ["octet-clone"])}).check()
        self.assertEqual(code, 0, out)

    def test_new_twin_fails(self):
        code, out = self.tree({"foo": OCTET_CLONE, "bar": FIELD_COPY},
                         {"books/foo.lisp": row(1, ["octet-clone"])}).check()
        self.assertEqual(code, 1)
        self.assertIn("NEW twin in books/bar.lisp", out)

    def test_stale_row_fails(self):
        # foo was drained but its row was not lowered: that is room for a new twin.
        code, out = self.tree({"foo": BASE.replace("fn-octets$c", "fn-octets")},
                         {"books/foo.lisp": row(1, ["octet-clone"])}).check()
        self.assertEqual(code, 1)
        self.assertIn("STALE row books/foo.lisp", out)

    def test_write_baseline_shrinks_and_keeps_reason(self):
        t = self.tree({"foo": OCTET_CLONE}, {"books/foo.lisp": row(2, ["octet-clone"]),
                                        "books/gone.lisp": row(1, ["octet-clone"])})
        rows, _ = t.rows()
        self.assertEqual(g.write_baseline(rows, t.baseline, acks=t.acks), [])
        self.assertEqual(g.load_baseline(t.baseline),
                         {"books/foo.lisp": {"kinds": ["octet-clone"], "count": 1, "reason": "test"}})

    def test_write_baseline_refuses_a_raise(self):
        t = self.tree({"foo": OCTET_CLONE, "bar": FIELD_COPY}, {"books/foo.lisp": row(1, ["octet-clone"])})
        rows, _ = t.rows()
        before = t.baseline.read_text()
        self.assertNotEqual(g.write_baseline(rows, t.baseline, acks=t.acks), [])
        self.assertEqual(t.baseline.read_text(), before)


class RealTree(Case):
    def test_every_book_reads(self):
        _, _, bad = g.twins(g.all_books())
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()
