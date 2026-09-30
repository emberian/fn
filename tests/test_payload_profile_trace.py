"""Closed observer must reject unknown operations and expose translated negation."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import payload_profile_trace as trace
from ledger import Sym

class ProfileTraceTests(unittest.TestCase):
    def expr(self, text):
        return trace.Instrument({}).expr(trace.read_forms(text)[0])

    def test_subtraction_accounts_for_negation_and_addition(self):
        result = self.expr("(- x y)")
        self.assertEqual(result.count("(list :negate "), 1)
        self.assertEqual(result.count("(list :add "), 1)
        self.assertIn("(unary-- ", result)
        self.assertIn("(binary-+ ", result)

    def test_unknown_primitive_and_unreviewed_arity_refuse(self):
        for source in ("(opaque x)", "(- x y z)"):
            with self.assertRaises(ValueError):
                self.expr(source)

    def test_nary_source_arithmetic_normalizes_each_binary_site(self):
        result = self.expr("(+ x (* y z w) a)")
        self.assertEqual(result.count("(list :add "), 2)
        self.assertEqual(result.count("(list :multiply "), 2)

    def test_subtraction_argument_effects_precede_outer_arithmetic(self):
        result = self.expr("(- (* a b) (+ c d))")
        self.assertLess(result.index("(list :multiply "), result.index("(list :negate "))
        self.assertEqual(result.count("(list :add "), 2)
        self.assertEqual(result.count("(list :negate "), 1)

    def test_checked_artifact_matches_trusted_sources_and_has_all_projections(self):
        generated = trace.generate()
        self.assertEqual((ROOT / "books/payload-profile-source-trace.lisp").read_text(), generated)
        self.assertEqual(generated.count("-value-projection"), len(trace.SELECTED) - 1)
        self.assertIn("(defthm fn-pzt-pzw-quantum-by-definition", generated)
        self.assertEqual(generated.count("-source-counts"), len(trace.SELECTED))
        for path in trace.SOURCES:
            self.assertIn(path + " SHA256 ", generated)

if __name__ == "__main__":
    unittest.main()
