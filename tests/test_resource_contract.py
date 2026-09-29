"""tools/resource_contract.py: the resource contract's citations against the tree."""

import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import resource_contract as rc  # noqa: E402


class LiteralTests(unittest.TestCase):
    def test_an_integer_and_a_product_are_read_and_nothing_else(self):
        self.assertEqual(rc.lisp_int("65536"), 65536)
        self.assertEqual(rc.lisp_int("(* 64 1048576)"), 64 * 1048576)
        self.assertEqual(rc.lisp_int(" (* 2 16 3) "), 96)
        with self.assertRaises(ValueError):
            rc.lisp_int("(+ 1 2)")
        with self.assertRaises(ValueError):
            rc.lisp_int("*fn-some-constant*")


class TheoremTests(unittest.TestCase):
    def test_a_theorem_is_found_only_as_a_defining_form_at_column_zero(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "books" / "x.lisp").write_text(
                "(defthm fn-x-holds (implies t t))\n"
                "(defthmd fn-x-holds-too t)\n"
                "(defkeystone fn-x-key t)\n"
                "; (defthm fn-x-commented t)\n"
                "  (defthm fn-x-indented t)\n"
                "(defun fn-x-holds-prefix () t)\n", encoding="utf-8")
            self.assertTrue(rc.theorem_defined(root, "books/x", "fn-x-holds"))
            self.assertTrue(rc.theorem_defined(root, "books/x", "fn-x-holds-too"))
            self.assertTrue(rc.theorem_defined(root, "books/x", "fn-x-key"))
            self.assertFalse(rc.theorem_defined(root, "books/x", "fn-x-commented"))
            self.assertFalse(rc.theorem_defined(root, "books/x", "fn-x-indented"))
            self.assertFalse(rc.theorem_defined(root, "books/x", "fn-x-holds-pre"))
            self.assertFalse(rc.theorem_defined(root, "books/x", "fn-x-hold"))
            self.assertIsNone(rc.theorem_defined(root, "books/absent", "fn-x-holds"))

    def test_the_doc_region_replaces_only_between_its_markers(self):
        text = "before\n" + rc.BEGIN + "\nold\n" + rc.END + "\nafter\n"
        block = rc.BEGIN + "\nnew\n" + rc.END
        self.assertEqual(rc.splice(text, block), "before\n" + block + "\nafter\n")
        self.assertEqual(rc.current_block(text), rc.BEGIN + "\nold\n" + rc.END)


class RealTreeTests(unittest.TestCase):
    """The committed doc against this tree: what `make check` asks, without
    the manifest audit (green_check is its own tested tool)."""

    def test_every_row_has_a_prose_row_and_the_ids_are_distinct(self):
        text = rc.DOC.read_text(encoding="utf-8")
        named = rc.row_ids_in_prose(text)
        ids = [row.id for row in rc.ROWS]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(set(ids), named)

    def test_the_committed_block_is_what_the_tree_says(self):
        text = rc.DOC.read_text(encoding="utf-8")
        self.assertEqual(rc.current_block(text), rc.render_block())

    def test_every_citation_of_a_landed_row_resolves(self):
        for s in rc.standings():
            self.assertEqual(s.missing_theorems, [], s.row.id)
            self.assertEqual(s.missing_proofs, [], s.row.id)
            self.assertEqual(s.missing_records, [], s.row.id)
            if s.pending:
                self.assertTrue(s.row.landing, f"{s.row.id} pends without a lane")

    def test_a_pending_citation_names_its_lane(self):
        for row in rc.ROWS:
            for book, name in row.theorems:
                if rc.theorem_defined(ROOT, book, name) is not True:
                    self.assertTrue(row.landing, f"{row.id}: {book} {name}")

    def test_the_constants_are_read_from_their_books(self):
        values = dict((label, value) for label, value, _, _ in rc.constant_values())
        self.assertIn("*fn-heap-article-slot-budget*", values)
        self.assertGreater(values["*fn-heap-article-slot-budget*"], 0)
        self.assertGreaterEqual(values["*fn-otm-stall-default-ms*"],
                                values["*fn-otm-deadline-default-ms*"])
        codes = dict(rc.outcome_codes())
        self.assertEqual(codes[":accepted"], 0)
        self.assertEqual(len(set(codes.values())), len(codes))
        self.assertGreater(rc.counts()["assumption_rows"], 0)


if __name__ == "__main__":
    unittest.main()
