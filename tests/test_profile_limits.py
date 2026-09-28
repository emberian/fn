"""tools/profile_limits.py: one profile table, its generated spans and its copy guard."""
from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import profile_limits  # noqa: E402

TABLE = {"stack-kib": {"value": 1024}, "fixed-threads": {"value": 12},
         "mux-loops": {"value": 2}, "control-clients": {"value": 16},
         "max-connections": {"value": 32}}


class TableTests(unittest.TestCase):
    def test_the_book_is_read_without_evaluating(self):
        rows = profile_limits.rows()
        self.assertIn("tls-limit", rows)
        self.assertIsInstance(rows["stack-kib"]["value"], int)
        self.assertTrue(all(r["unit"] and r["meaning"] for r in rows.values()))

    def test_expressions(self):
        self.assertEqual(profile_limits.evaluate("fixed-threads + mux-loops + control-clients",
                                                 TABLE), "30")
        self.assertEqual(profile_limits.evaluate("max-connections - 1", TABLE), "31")
        self.assertEqual(profile_limits.evaluate("stack-kib,", TABLE), "1,024")
        self.assertEqual(profile_limits._terms_ok("stack-kib + nope", TABLE), "nope")
        self.assertIsNone(profile_limits._terms_ok("stack-kib - 1", TABLE))


class RegionTests(unittest.TestCase):
    def tree(self, text):
        root = Path(tempfile.mkdtemp())
        for relative in profile_limits.REGION_FILES:
            (root / relative).parent.mkdir(parents=True, exist_ok=True)
            (root / relative).write_text("x <!--limit:stack-kib-->1024<!--/limit--> y\n")
        (root / profile_limits.REGION_FILES[0]).write_text(text)
        return root

    def test_current_span_passes(self):
        root = self.tree("a <!--limit:fixed-threads + mux-loops-->14<!--/limit--> b\n")
        self.assertEqual(profile_limits.regions(root, TABLE, write=False), [])

    def test_stale_span_is_refused_and_rewritten(self):
        root = self.tree("a <!--limit:fixed-threads-->11<!--/limit--> b\n")
        found = profile_limits.regions(root, TABLE, write=False)
        self.assertTrue(any("says 11 and the table says 12" in p for p in found), found)
        self.assertEqual(profile_limits.regions(root, TABLE, write=True), [])
        self.assertIn("-->12<!--", (root / profile_limits.REGION_FILES[0]).read_text())

    def test_unknown_row_is_refused(self):
        root = self.tree("a <!--limit:no-such-row-->1<!--/limit--> b\n")
        found = profile_limits.regions(root, TABLE, write=False)
        self.assertTrue(any("names no row no-such-row" in p for p in found), found)

    def test_a_file_without_a_span_is_refused(self):
        root = self.tree("no span here\n")
        found = profile_limits.regions(root, TABLE, write=False)
        self.assertTrue(any("carries no" in p for p in found), found)


class CopyTests(unittest.TestCase):
    def test_a_literal_copy_is_refused(self):
        root = Path(tempfile.mkdtemp())
        (root / "host" / "native").mkdir(parents=True)
        (root / "host" / "native" / "mux.lisp").write_text("(defconstant +fnn-mux-loops+ 2)\n")
        found = profile_limits.copies(root)
        self.assertEqual(len(found), 1, found)

    def test_the_tree_has_no_known_copy(self):
        self.assertEqual(profile_limits.copies(ROOT), [])


if __name__ == "__main__":
    unittest.main()
