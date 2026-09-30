"""Typed logical trace checker teeth; real source trace archived separately."""
import copy
import unittest
from tools.resilience.adapters.typed_window import EXPECTED, observe, judge


class TypedWindowTests(unittest.TestCase):
    def trace(self):
        return "\n".join(
            f"ACL2 !>FN_W7_WINDOW step={i} answer={a}\nphase={p} bytes={b} workers={w} close={c}"
            for i, (a, p, b, w, c) in enumerate(EXPECTED))

    def test_complete_literal_relationships(self):
        journal = observe(self.trace())
        result = judge(journal)
        self.assertEqual(result.kind, "consistent")
        self.assertEqual(len(journal.records), 8)
        self.assertIn("typed-window-native-return-and-join", result.pending_rules)

    def test_release_at_cancel_and_return_break_retained_charge_rules(self):
        for step, rule in ((1, "cancel-keeps-charges"), (4, "return-keeps-charges")):
            with self.subTest(step=step):
                journal = observe(self.trace())
                journal.records[step]["charged_bytes"] = 64
                result = judge(journal)
                self.assertEqual((result.kind, result.cause), ("violation", rule))

    def test_wrong_request_and_duplicate_settlement_cannot_pass(self):
        for step, rule in ((3, "wrong-request-cannot-return"), (7, "duplicate-settlement-stale")):
            journal = observe(self.trace())
            journal.records[step]["answer"] = ":RELEASED"
            self.assertEqual(judge(journal).cause, rule)

    def test_truncation_duplicate_and_missing_fields_fail(self):
        journal = observe(self.trace())
        journal.records.pop()
        self.assertEqual(judge(journal).kind, "harness-failure")
        journal = observe(self.trace())
        journal.records[3] = copy.deepcopy(journal.records[2])
        self.assertEqual(judge(journal).kind, "harness-failure")
        journal = observe(self.trace())
        journal.records[4].pop("workers")
        self.assertEqual(judge(journal).kind, "harness-failure")

    def test_source_echo_is_not_an_executed_observation(self):
        self.assertEqual(observe('(cw "FN_W7_WINDOW step=~x0 answer=~x1")').records, [])

    def test_actual_model_phases_do_not_fill_native_dimensions(self):
        from tools.resilience.semantic_coverage import typed_window_report
        result = typed_window_report(observe(self.trace()))
        self.assertEqual((result["distinct"], result["observations"]), (4, 8))
        for row in result["situations"]:
            for field in ("publication_phase", "outcome_certainty", "reader_generation_relation",
                          "hold_count_class", "headroom_band", "evidence_version_relation"):
                self.assertEqual(row["signature"][field], "unobserved")
