"""tests/test_own_make_field.py: tools/own_make_field.py (lane owner-globals-28).

The fixture is a byte diff against a HAND-converted file: four construction
shapes, a block comment, a name list that is not a construction and a call
already converted.  The refusal tests name every residual reason.
"""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import own_make_field as omf  # noqa: E402

FIX = ROOT / "tests" / "fixtures" / "own_make_field"
A15 = "a b c d e f g h i j k l m n"  # fourteen


class Fixture(unittest.TestCase):
    def test_hand_converted_fixture_is_byte_identical(self):
        before = (FIX / "before.lisp").read_bytes().decode()
        after = (FIX / "after.lisp").read_bytes().decode()
        new, rep = omf.transform_text(before, "before.lisp")
        self.assertEqual(new, after)
        self.assertEqual(sorted(s["rule"] for s in rep["sites"]),
                         ["fresh-nil", "node-secret-owner", "refused-call", "refused-symbol"])
        self.assertEqual([s["arity"] for s in rep["skipped"]], [2])

    def test_idempotent(self):
        after = (FIX / "after.lisp").read_text()
        new, rep = omf.transform_text(after)
        self.assertEqual(new, after)
        self.assertEqual(rep["sites"], [])


class Refusals(unittest.TestCase):
    def one(self, args):
        new, rep = omf.transform_text(f"(f (fn-own-make {args}))")
        return new, rep["sites"][0]

    def test_mixed_source_owners(self):
        new, s = self.one(f"{A15[:-2]} (fn-own-node-secret o) (fn-own-refused p)")
        self.assertEqual(s["refused"], "mixed-source-owners")
        self.assertNotIn("proc", new)

    def test_unknown_fifteenth(self):
        _, s = self.one(f"{A15[:-2]} secret rf")
        self.assertTrue(s["refused"].startswith("fifteenth-argument-not-a-carry"))

    def test_name_collision(self):
        _, s = self.one(f"{A15[:-2]} node-secret refused")
        self.assertEqual(s["rule"], "refused-symbol")
        new, rep = omf.transform_text(f"(let ((proc 1)) (fn-own-make {A15[:-2]} node-secret refused))")
        self.assertTrue(rep["sites"][0]["refused"].startswith("name-collision"))
        self.assertEqual(new, f"(let ((proc 1)) (fn-own-make {A15[:-2]} node-secret refused))")

    def test_numbered_variables(self):
        new, s = self.one("s v c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13")
        self.assertEqual(s["rule"], "numbered-variables")
        self.assertTrue(new.endswith("c13 c14))"))

    def test_source_owner_containing_a_construction_is_refused_inner_converted(self):
        inner = f"(fn-own-make {A15[:-2]} nil nil)"
        new, rep = omf.transform_text(f"(fn-own-make {A15[:-2]} (fn-own-node-secret {inner}) (fn-own-refused {inner}))")
        self.assertEqual(sorted(("refused" in s) for s in rep["sites"]), [False, False, True])
        self.assertEqual(new.count("(fn-oproc-initial)"), 2)
        self.assertNotIn("(fn-own-proc", new)


if __name__ == "__main__":
    unittest.main()
