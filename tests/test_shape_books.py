"""tools/shape_books.py: fan-in over the farm's include graph."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import shape_books                                            # noqa: E402

# book -> the books it includes.  base is under everything; leaf under nothing.
CLOSURE = {
    "books/base": [],
    "books/mid-a": ["books/base"],
    "books/mid-b": ["books/base"],
    "books/top": ["books/mid-a", "books/mid-b"],
    "tests/acl2/top-tests": ["books/top"],
    "books/leaf": [],
}
ROOTS = ["books/top", "tests/acl2/top-tests", "books/leaf"]


class FanInTests(unittest.TestCase):
    def test_counts_are_transitive_includers_and_roots(self):
        counts = shape_books.fan_in(CLOSURE, ROOTS)
        self.assertEqual(counts["books/base"], (5, 2))   # itself, mid-a, mid-b, top, top-tests
        self.assertEqual(counts["books/mid-a"], (3, 2))
        self.assertEqual(counts["books/top"], (2, 2))
        self.assertEqual(counts["books/leaf"], (1, 1))

    def test_ranking_is_by_dependents_then_roots_then_name(self):
        rows = shape_books.ranked(shape_books.fan_in(CLOSURE, ROOTS))
        self.assertEqual([b for b, _, _ in rows][:3], ["books/base", "books/mid-a", "books/mid-b"])

    def test_the_doc_region_replaces_only_between_its_markers(self):
        text = "before\n" + shape_books.BEGIN + "\nold\n" + shape_books.END + "\nafter\n"
        region = shape_books.doc_region(shape_books.fan_in(CLOSURE, ROOTS), len(ROOTS))
        out = shape_books.replace_region(text, region)
        self.assertTrue(out.startswith("before\n" + shape_books.BEGIN))
        self.assertTrue(out.endswith(shape_books.END + "\nafter\n"))
        self.assertIn("| `books/base.lisp` | 5 | 2 |", out)
        self.assertNotIn("old", out)

    def test_no_git_is_unknown_not_an_error(self):
        self.assertEqual(shape_books.last_changed("books/base", Path("/nonexistent")), "unknown")


class ResolveAndDispatchTests(unittest.TestCase):
    """Item 26: bare names resolve; --affected-by alone is the chain view."""

    def setUp(self):
        import tempfile
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        for rel in ("books/wire.lisp", "books/twin.lisp", "tests/acl2/twin.lisp",
                    "tests/acl2/wire-tests.lisp"):
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text("; book\n")

    def tearDown(self):
        self.tmp.cleanup()

    def test_every_spelling_farm_takes_and_a_bare_name(self):
        for word in ("books/wire", "books/wire.lisp", str(self.root / "books/wire.lisp"),
                     "wire", "wire.lisp"):
            self.assertEqual(shape_books.resolve_book(word, self.root), "books/wire", word)
        self.assertEqual(shape_books.resolve_book("wire-tests", self.root),
                         "tests/acl2/wire-tests")

    def test_ambiguous_and_missing_are_refused_by_name_not_traceback(self):
        with self.assertRaises(SystemExit) as caught:
            shape_books.resolve_book("twin", self.root)
        self.assertIn("ambiguous", str(caught.exception))
        self.assertIn("tests/acl2/twin.lisp", str(caught.exception))
        with self.assertRaises(SystemExit) as caught:
            shape_books.resolve_book("nope", self.root)
        self.assertIn("no such book", str(caught.exception))
        self.assertIn("books/nope.lisp", str(caught.exception))

    def test_affected_by_alone_prints_the_chain_view(self):
        from unittest import mock
        import io
        import contextlib
        calls = []
        with mock.patch.object(shape_books, "chain_report",
                               lambda affected, through: calls.append((affected, through)) or ["CHAIN"]), \
                mock.patch.object(shape_books, "tree_counts",
                                  side_effect=AssertionError("the top table ran")):
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(shape_books.main(["--affected-by", "books/wire.lisp"]), 0)
        self.assertEqual(calls, [(["books/wire.lisp"], None)])
        self.assertEqual(out.getvalue().strip(), "CHAIN")

    def test_book_takes_a_bare_name(self):
        from unittest import mock
        import io
        import contextlib
        with mock.patch.object(shape_books, "tree_counts",
                               return_value=({"books/top": (1, 1)}, 3)), \
                mock.patch.object(shape_books, "resolve_book",
                                  lambda w: {"top": "books/top"}[w]), \
                mock.patch.object(shape_books, "last_changed", lambda b: "x"):
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(shape_books.main(["--book", "top"]), 0)
        self.assertIn("books/top.lisp", out.getvalue())


if __name__ == "__main__":
    unittest.main()
