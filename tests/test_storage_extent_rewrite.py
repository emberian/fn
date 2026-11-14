"""Discriminate physical references from journal rows and payload packing."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from storage_extent_rewrite import rewrite, STRIDE, PACK

class StorageExtentRewriteTests(unittest.TestCase):
    def test_owner_and_row_arithmetic(self):
        src = "; (* 3 extent) stays a comment\n(defun physical (extent row role) (+ (* 3 extent) (* 3 row) role))\n(defun io (extent row role) (+ (* 3 extent) (* 3 row) role))\n"
        got, count = rewrite(src, "physical", "(* 3 extent)", f"(* {STRIDE} extent)")
        self.assertEqual(count, 1)
        self.assertIn(f"(+ (* {STRIDE} extent) (* 3 row) role)", got)
        self.assertIn("(defun io (extent row role) (+ (* 3 extent) (* 3 row) role))", got)
        self.assertTrue(got.startswith("; (* 3 extent) stays a comment"))
        self.assertEqual(rewrite(got, "physical", "(* 3 extent)", f"(* {STRIDE} extent)"), (got, 0))

    def test_stride_and_packing_are_different(self):
        src = "(defun block (blk row-cext row role) (+ (* *fn2-commit-write-resources* row-cext) (mod blk *fn2-commit-write-resources*) (* 3 row) role))"
        got, n = rewrite(src, None, "(* *fn2-commit-write-resources* row-cext)", f"(* {STRIDE} row-cext)")
        got, m = rewrite(got, None, "(mod blk *fn2-commit-write-resources*)", f"(mod blk {PACK})")
        self.assertEqual((n, m), (1, 1))
        self.assertIn(f"(+ (* {STRIDE} row-cext) (mod blk {PACK}) (* 3 row) role)", got)

    def test_expression_capture_preserves_handle(self):
        src = "(defun readback (loc) (* 3 (nth 0 loc)))"
        got, n = rewrite(src, None, "(* 3 (nth 0 ?x))", f"(* {STRIDE} (nth 0 {{x}}))")
        self.assertEqual(n, 1)
        self.assertIn(f"(* {STRIDE} (nth 0 loc))", got)

if __name__ == "__main__":
    unittest.main()
