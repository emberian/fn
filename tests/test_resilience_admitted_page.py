"""Admission adapter/oracle semantics; synthetic rows are not native evidence."""
import copy
import unittest
from tools.resilience import admitted_page as page
from tools.resilience.checker import check as check_history
from tools.resilience.scenario import check, ScenarioError
from tools.resilience.shrink import dependencies


def fixture():
    scenario = check(page.example())
    views = [
        (":REGISTERED", ":NONE", 100, 0, 0, True, ":CLOSABLE"),
        (":ADMITTED", ":ISSUED", 1000, 1, 1, False, ":READ-FILE-HELD"),
        (":CANCEL-ATTEMPT", ":CANCELLED", 1000, 1, 1, False, ":READ-FILE-HELD"),
        (":OWNED-READ-HELD", ":CANCELLED", 1000, 1, 1, False, ":READ-FILE-HELD"),
        (":STALE", ":CANCELLED", 1000, 1, 1, False, ":READ-FILE-HELD"),
        (":CANCELLED", ":SETTLED", 100, 0, 1, True, ":CLOSABLE"),
        (":ADMITTED", ":ISSUED", 1000, 1, 2, False, ":READ-FILE-HELD"),
        (":STALE", ":SETTLED", 1000, 1, 2, False, ":READ-FILE-HELD"),
        (":PUBLISH", ":SETTLED", 900, 0, 2, True, ":READ-FILE-HELD"),
        (":READ-FILE-HELD", ":SETTLED", 900, 0, 2, True, ":READ-FILE-HELD"),
        (":EVICTED", ":SETTLED", 100, 0, 2, True, ":CLOSABLE"),
        (":CLOSED", ":SETTLED", 0, 0, 2, True, ":STALE"),
    ]
    text = "\n".join(f"FN_W7_ADMITTED trial=0 step={i} answer={a} phase={p} bytes={b} "
                     f"workers={w} next={n} spent={n} baseline=3000 clear={'T' if c else 'NIL'} preview={q}"
                     for i, (a, p, b, w, n, c, q) in enumerate(views))
    return scenario, page.observe(scenario, text)


class AdmittedPageTests(unittest.TestCase):
    def test_completion_accepts_actual_cli_indent_but_not_echo_or_other_trial(self):
        from tools.resilience.adapters.admitted_page_source import completed
        self.assertTrue(completed("        ACL2 !>FN_W7_ADMITTED_COMPLETE trial=0\n", 0))
        self.assertFalse(completed('(cw "FN_W7_ADMITTED_COMPLETE trial=0~%")', 0))
        self.assertFalse(completed("ACL2 !>FN_W7_ADMITTED_COMPLETE trial=1", 0))

    def test_actual_owner_admission_drives_only_admitted_token_and_preserves_scope(self):
        scenario, journal = fixture()
        text = page.driver(scenario)
        self.assertIn("fn-owner-page-read-admit", text)
        self.assertIn("fn-pio-own-admitted-token token", text)
        self.assertNotIn("fn-pio-issue", text)
        self.assertNotIn("fn-prl-admit", text)  # owner computes demand internally
        verdict = check_history(scenario, journal)
        self.assertEqual(verdict.kind, "consistent")
        self.assertIn("page-native-return-and-join", verdict.pending_rules)
        self.assertNotIn("retired-file-closed", verdict.witnesses_observed)

    def test_cancel_refund_is_exact_retained_cause(self):
        scenario, journal = fixture()
        journal.records[2]["charged_bytes"] = 100
        verdict = page.judge(scenario, journal)
        self.assertEqual(verdict.kind, "violation")
        self.assertEqual(verdict.cause, "admitted-page-cancel-refunded-before-completion")

    def test_old_completion_cannot_refund_new_request(self):
        scenario, journal = fixture()
        journal.records[7]["workers"] = 0
        self.assertEqual(page.judge(scenario, journal).cause,
                         "admitted-page-stale-completion-mutated-live-charge")

    def test_cache_credit_blocks_close_after_logical_ownership_clear(self):
        scenario, journal = fixture()
        journal.records[9]["answer"] = ":CLOSED"
        self.assertEqual(page.judge(scenario, journal).cause, "admitted-page-closed-charged-cache")

    def test_missing_observation_cannot_be_shorter_valid_history(self):
        scenario, journal = fixture()
        journal.records.pop(4)
        self.assertEqual(page.judge(scenario, journal).kind, "harness-failure")

    def test_request_consumer_must_follow_admission(self):
        scenario = page.example()
        scenario.operations[0] = scenario.operations[2]
        with self.assertRaises(ScenarioError):
            check(scenario)

    def test_cannot_overwrite_retained_request_or_claim_native_join(self):
        scenario = page.example()
        scenario.operations[6].args["request"] = "A"
        with self.assertRaises(ScenarioError):
            check(scenario)
        scenario = page.example()
        scenario.witnesses = ["retired-file-closed"]
        with self.assertRaises(ScenarioError):
            check(scenario)

    def test_reducer_preserves_all_source_state_dependencies(self):
        scenario = check(page.example())
        edges = dependencies(scenario)
        for prior, current in zip(scenario.operations, scenario.operations[1:]):
            self.assertIn(prior.id, edges[current.id])

    def test_native_fault_or_time_claim_is_rejected(self):
        scenario = page.example()
        scenario.healing_bound = {"kind": "experimental", "value": 1, "source": "not observed"}
        with self.assertRaises(ScenarioError):
            check(scenario)

    def test_fixture_profile_cannot_alias_global_expected_recipe(self):
        scenario = page.example()
        scenario.initial["budget"][0] = 0
        self.assertEqual(page.RECIPE["budget"][0], 100000)
        with self.assertRaises(ScenarioError):
            check(scenario)

    def test_case_alias_cannot_rebind_retained_request(self):
        scenario = page.example()
        scenario.operations[6].args["request"] = "a"
        with self.assertRaises(ScenarioError):
            check(scenario)

    def test_cannot_refund_spent_identity_or_installed_baseline(self):
        scenario, journal = fixture()
        journal.records[5]["spent"] = 0
        self.assertEqual(page.judge(scenario, journal).cause,
                         "admitted-page-installed-baseline-or-spent-credit")
