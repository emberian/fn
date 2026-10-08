import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import hazard_rule_followthrough as t  # noqa: E402
from lisp_rewrite import write  # noqa: E402

DISABLE = ("; Hazard rules (tools/hazard_rule_classes.py --disable): :rewrite rules on\n"
           "; a structural primitive of bare variables, kept for this book's proofs\n"
           "; and disabled for every book that includes it (enable or :use them).\n")

A = """(in-package "ACL2")
(defthm a-dead (implies (foop x) (consp x)))
(defthm a-own (implies (foop x) (car x)))
(defthm a-user (implies (foop x) (consp (cdr x)))
  :hints (("Goal" :use a-own)))
(defthm a-use-only (implies (barp x) (consp x)))
(defthm a-targeted (implies (barp x y) (consp y)))
(defthm a-refused (implies (and (natp i) (barp x)) (equal (nth i x) 1)))
(in-theory (disable a-user (:rewrite a-dead)))

""" + DISABLE + """(in-theory (disable a-dead
                    a-own
                    a-use-only
                    a-targeted
                    a-refused))
"""
B = """(in-package "ACL2")
(include-book "a")
(defthm b-1 (foop z) :hints (("Goal" :use (:instance a-use-only (x z)))))
(defthm b-2 (foop z) :hints (("Goal" :in-theory (e/d (a-targeted a-refused) (a-dead)))))
"""


class Followthrough(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        r = Path(self.d.name)
        for sub in ("books", "planning", "host", "tests/acl2"):
            (r / sub).mkdir(parents=True)
        (r / "books/a.lisp").write_text(A)
        (r / "books/b.lisp").write_text(B)
        rows = {f"{n}|consp": 1 for n in ("a-dead", "a-own", "a-use-only", "a-targeted", "a-refused")}
        (r / t.BASELINE).write_text(json.dumps({"rows": rows}))
        self.root = r

    def tearDown(self):
        self.d.cleanup()

    def classes(self):
        res, _ = t.analyse(self.root)
        return {n: c for n, (b, c, w) in res.items()}

    def test_classes(self):
        self.assertEqual(self.classes(), {
            "a-dead": "DEAD-DELETE", "a-own": "DEAD-LOCAL", "a-use-only": "USE-ONLY",
            "a-targeted": "TARGETED", "a-refused": "TARGETED"})

    def test_apply(self):
        res, _ = t.analyse(self.root)
        edits, resid, texts = t.apply_plan(self.root, res)
        a = write(texts["books/a.lisp"], edits["books/a.lisp"])
        b = write(texts["books/b.lisp"], edits["books/b.lisp"])
        self.assertNotIn("(defthm a-dead", a)
        self.assertIn("(local (defthm a-own (implies (foop x) (car x))))", a)
        self.assertIn("(defthm a-use-only (implies (barp x) (consp x))\n :rule-classes nil)", a)
        self.assertIn("(defthm a-targeted (implies (barp x y) (consp y))\n"
                      " :rule-classes ((:forward-chaining :trigger-terms ((barp x y)))))", a)
        # the conclusions and hypotheses are untouched
        for stmt in ("(implies (foop x) (car x))", "(implies (barp x) (consp x))",
                     "(implies (barp x y) (consp y))"):
            self.assertIn(stmt, a)
        # the disable block loses every name it no longer needs; a-refused stays
        block = a.split(DISABLE)[1]
        self.assertEqual(" ".join(block.split()), "(in-theory (disable a-refused))")
        # mentions elsewhere: the disable of a deleted rule goes, the enable of a targeted one goes
        self.assertNotIn("a-dead", b)
        self.assertIn("(e/d (a-refused)", b)

    def test_refuses_with_a_named_reason(self):
        res, _ = t.analyse(self.root)
        edits, resid, _ = t.apply_plan(self.root, res)
        self.assertEqual([(n, c, w.split(" (")[0]) for b, n, c, w in resid],
                         [("a-refused", "TARGETED", "hypothesis is a primitive call")])

    def test_trigger_shapes(self):
        from lisp_rewrite import parse
        from hazard_rule_classes import Refuse
        ok = parse("(defthm x (implies (foop a b) (consp b)))").forms[0]
        self.assertEqual(t.trigger_of(ok).items[0].text, "foop")
        for src, why in (("(defthm x (implies (and (foop a) (natp i)) (consp a)))", "primitive call"),
                         ("(defthm x (implies (foop a a) (consp a)))", "distinct"),
                         ("(defthm x (implies (foop a) (consp b)))", "outside the trigger"),
                         ("(defthm x (consp a))", "not (implies")):
            with self.assertRaises(Refuse) as cm:
                t.trigger_of(parse(src).forms[0])
            self.assertIn(why, str(cm.exception))


if __name__ == "__main__":
    unittest.main()
