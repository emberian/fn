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


if __name__ == "__main__":
    unittest.main()
