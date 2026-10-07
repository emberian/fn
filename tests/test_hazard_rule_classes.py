import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import hazard_rule_classes as h  # noqa: E402
from lisp_rewrite import write  # noqa: E402

FIX = Path(__file__).resolve().parent / "fixtures" / "hazard_rule_classes"


class Convert(unittest.TestCase):
    def setUp(self):
        self.orig = h.ROOT
        h.ROOT = FIX

    def tearDown(self):
        h.ROOT = self.orig

    def test_plan_and_output(self):
        edits, resid = h.plan(FIX / "census.tsv")
        self.assertEqual(sorted((n, w) for _, n, w in resid),
                         [("e-already", "already-nil"), ("f-generated", "generated")])
        text = (FIX / "in.lisp").read_text()
        out = write(text, [e for _, e in edits["in.lisp"]])
        self.assertIn("(defthm a-plain (implies (foop x) (consp x))\n :rule-classes nil)", out)
        self.assertIn("(car x)) :rule-classes nil))", out)
        self.assertIn(":rule-classes (:forward-chaining)))", out)
        self.assertIn("(consp x)) :rule-classes nil)\n(defthm e-already", out)
        self.assertIn("; a comment that stays", out)
        # only the rule classes changed
        self.assertEqual(out.replace("\n :rule-classes nil", "").replace("nil", "X"),
                         text.replace(":rewrite :forward-chaining", ":forward-chaining")
                         .replace("((:rewrite))", "nil").replace(":rule-classes :rewrite", ":rule-classes nil")
                         .replace("nil", "X"))

    def test_disable_mode(self):
        edits, resid = h.disable_plan(FIX / "census.tsv")
        self.assertEqual(sorted((n, w) for _, n, w in resid),
                         [("d-only-list", "defthmd: already disabled"), ("f-generated", "generated")])
        text = (FIX / "in.lisp").read_text()
        out = write(text, [e for _, e in edits["in.lisp"]])
        self.assertTrue(out.startswith(text))
        self.assertTrue(out.endswith("(in-theory (disable a-plain\n                    b-rewrite\n"
                                     "                    (:rewrite c-mixed)\n                    e-already))\n"))


if __name__ == "__main__":
    unittest.main()
