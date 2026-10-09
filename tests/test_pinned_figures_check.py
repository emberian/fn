"""tools/pinned_figures_check.py: a test book never pins a figure a book derives (D27)."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))

import pinned_figures_check  # noqa: E402


def tree(books: str, tests: dict) -> Path:
    root = Path(tempfile.mkdtemp())
    (root / "books").mkdir()
    (root / "tests/acl2").mkdir(parents=True)
    (root / "books/heap-store-figure.lisp").write_text(books)
    for name, text in tests.items():
        (root / "tests/acl2" / name).write_text(text)
    return root


class PinnedFiguresCheck(unittest.TestCase):
    BOOKS = ("(defconst *fn-heap-reclaim-record-octets* (+ 48 (* 2 4096) (* 2 1024)))\n"
             "(defconst *fn-heap-storeless-thread-octets* (* 6 1048576))\n")

    def test_a_constant_is_evaluated_from_the_books(self):
        root = tree(self.BOOKS, {})
        self.assertEqual(pinned_figures_check.figures(root),
                         {48 + 8192 + 2048: "*fn-heap-reclaim-record-octets*",
                          6291456: "*fn-heap-storeless-thread-octets*"})

    def test_a_literal_equal_to_a_producing_constant_is_named(self):
        root = tree(self.BOOKS, {"a-tests.lisp": "(assert! (equal x (* 10288 6)))\n"
                                                 "(assert! (equal y 10289))\n"
                                                 "; 10288 in a comment, \"10288\" in a string\n"})
        self.assertEqual(pinned_figures_check.pins(root),
                         ["tests/acl2/a-tests.lisp:1: 10288 is *fn-heap-reclaim-record-octets*"])

    def test_a_pinned_heap_decision_is_named_unless_it_is_a_fixture_or_exempt(self):
        pinned = "(assert! (equal (decide x) '(:heap 724 \"small\" 4096 1024 34)))\n"
        refused = "(assert! (equal r '(:refused :machine-cannot-hold-threads 2200 2048)))\n"
        line = "(assert! (equal l \"heap=724 MB profile=small\"))\n"
        root = tree(self.BOOKS, {"a-tests.lisp": pinned + refused + line,
                                 "b-tests.lisp": "; pinned-fixture\n" + pinned,
                                 "heap-figure-tests.lisp": pinned})
        self.assertEqual(
            pinned_figures_check.pins(root),
            [f"tests/acl2/a-tests.lisp:{n}: a heap figure is pinned in a decision"
             for n in (1, 2, 3)])

    def test_a_derived_decision_is_not_named(self):
        root = tree(self.BOOKS, {"a-tests.lisp": "(assert! (equal (decide x)\n"
                                                 "  (list :heap *run-mb* \"small\" 4096 1024 34)))\n"})
        self.assertEqual(pinned_figures_check.pins(root), [])

    def test_the_tree_holds_no_pin(self):
        self.assertEqual(pinned_figures_check.pins(pinned_figures_check.ROOT), [])


if __name__ == "__main__":
    unittest.main()
