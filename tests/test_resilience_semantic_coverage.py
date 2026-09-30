import unittest

from tools.resilience.adapters import simulator, response_holds
from tools.resilience.journal import Journal
from tools.resilience.semantic_coverage import report
from tests.test_resilience_response_holds import fixture


class SemanticCoverageTests(unittest.TestCase):
    def test_native_dimensions_cannot_be_inferred_from_model_holds(self):
        scenario, output = fixture()
        journal, verdict = response_holds.observe(scenario, output, 0, .1)
        result = report(scenario, journal)
        self.assertEqual(result["observations"], 8)
        self.assertEqual({r["signature"]["hold_count_class"] for r in result["situations"]},
                         {"zero", "one", "multiple"})
        for row in result["situations"]:
            for dimension in ("headroom_band", "reader_generation_relation", "evidence_version_relation"):
                self.assertEqual(row["signature"][dimension], "unobserved")

    def test_uncertainty_and_repeated_recovery_are_distinct_situations(self):
        s = simulator.example()
        j = Journal(s.id)
        for name, pending, fenced in [("uncertain-B", "B", "T"),
                                      ("resolve-B", "none", "NIL"), ("repeat-B", "none", "NIL")]:
            j.client("model-step", operation=name, p=pending, f=fenced)
        r = report(s, j)
        self.assertEqual(r["distinct"], 3)
        self.assertEqual({v["signature"]["recovery_attempt"] for v in r["situations"]},
                         {"zero", "one", "repeated"})

    def test_diagnostics_cannot_invent_client_semantic_coverage(self):
        s = simulator.example()
        j = Journal(s.id)
        j.internal("model-step", operation="resolve-B", p="none", f="NIL")
        self.assertEqual(report(s, j)["observations"], 0)

    def test_incomplete_or_unbound_observations_are_refused(self):
        s = simulator.example()
        for name, fields in [("resolve-B", {}), ("missing", {"p": "none", "f": "NIL"})]:
            j = Journal(s.id)
            j.client("model-step", operation=name, **fields)
            with self.assertRaises(ValueError):
                report(s, j)
