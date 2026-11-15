"""Root1 actual child-domain controls; no ACL2 execution."""
import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_source import forms, read_sexp


def definition(path, name):
    return next(t for s in forms((ROOT / path).read_text())
                if isinstance((t := read_sexp(s)), list) and len(t) > 1 and t[1] == name)


def typed_domain(tree):
    return tree[-1][3][0] == "list*" and tree[-1][3][1:3] == [
        ["list", ["fn2-columns-sym", ["car", "children"]], ["car", "children"]],
        ["list", ["fn2-columns-sym", ["car", "children"]], ["car", "children"]]]


class TypedDomain(unittest.TestCase):
    def test_every_actual_child_gets_type_and_shape(self):
        t = definition("books/checkpoint-child-contracts.lisp", "fn2-checkpoint-root1-child-hyps")
        self.assertTrue(typed_domain(t))
        old = [*t[:-1], ["if", ["atom", "children"], "nil", ["cons", t[-1][3][2], t[-1][3][-1]]]]
        self.assertFalse(typed_domain(old))
        arms = definition("books/machine-arms.lisp", "fn2-arms-child-shape-hyps")
        self.assertEqual(arms[-1][3][0], "list*")
        source = (ROOT / "books/checkpoint-child-contracts.lisp").read_text()
        self.assertIn('(list (fn2-columns-sym (car children) "P")', source)
        self.assertIn('(list (fn2-columns-sym (car children) "-WFP")', source)

    def test_actual_malformed_carrier_fixture_matches_schema(self):
        schema = definition("books/checkpoint-metadata-state.lisp", "fn2-checkpoint-metadata")
        self.assertEqual(len(schema[2]), 25)
        self.assertEqual(len(schema), 3)
        fixture = (ROOT / "tests/checkpoint-root1-typed-domain-unit.lisp").read_text()
        self.assertIn("(repeat 24 '(0))", fixture)
        self.assertIn("(not (fn2-checkpoint-metadatap", fixture)
        self.assertIn("fn2-arms-child-shape-hyps", fixture)


if __name__ == "__main__":
    unittest.main()
