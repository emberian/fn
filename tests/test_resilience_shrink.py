"""The reducer must reproduce violations, not make an execution disappear."""
from dataclasses import replace
from types import SimpleNamespace
import unittest

from tools.resilience.adapters import simulator
from tools.resilience.scenario import Operation, Scenario, ScenarioError
from tools.resilience.shrink import delete, dependencies, minimize


def fixture():
    return Scenario("shrink", "Retained identity dependency", "local-commit-log",
                    {"recipe": "empty-store", "prior": []},
                    [{"name": "client", "kind": "client"}],
                    [Operation("A", "client", "post", {"groups": ["g"]}),
                     Operation("retry", "client", "retry", {"of": "A"}),
                     Operation("noise", "client", "post", {"groups": ["g"]}),
                     Operation("heal", "client", "recover")],
                    [], ["heal"], ["post-accepted"])


class ShrinkTests(unittest.TestCase):
    def test_transitive_identity_dependencies_survive_deletion(self):
        scenario = fixture()
        scenario.operations.insert(2, Operation("read", "client", "read",
                                                {"article": "A", "requires": ["retry"]}))
        self.assertEqual([o.id for o in delete(scenario, "A").operations], ["noise", "heal"])
        self.assertEqual([o.id for o in delete(scenario, "noise").operations],
                         ["A", "retry", "read", "heal"])

    def test_missing_and_future_prerequisites_refused(self):
        for prerequisite in ("missing", "heal"):
            s = fixture()
            s.operations[0] = replace(s.operations[0], args={"groups": ["g"],
                                                            "requires": [prerequisite]})
            with self.assertRaises(ScenarioError):
                dependencies(s)

    def test_model_transition_producers_are_not_erased(self):
        s = simulator.example()
        self.assertEqual(dependencies(s)["resolve-B"], {"stale-recovery-B"})
        with self.assertRaises(ScenarioError):
            delete(s, "prepare-A")

    def test_only_same_violation_cause_is_a_reproduction(self):
        seen = []
        def execute(s):
            ids = {o.id for o in s.operations}
            seen.append(ids)
            kind = "violation" if "A" in ids else "harness-failure"
            return SimpleNamespace(kind=kind, cause="fracture")
        result = minimize(fixture(), execute)
        self.assertFalse(result.exhausted)
        self.assertEqual([o.id for o in result.scenario.operations], ["A", "heal"])
        self.assertTrue(any(a["kind"] == "harness-failure" and not a["retained"]
                            for a in result.attempts))
        self.assertEqual(result.executions, len(seen))

    def test_inconclusive_no_witness_and_different_violation_do_not_shrink(self):
        for kind, cause in [("inconclusive", "budget"), ("no-witness", ""),
                            ("violation", "different")]:
            calls = []
            def execute(s):
                calls.append(s)
                return SimpleNamespace(kind="violation" if len(calls) == 1 else kind,
                                       cause="original" if len(calls) == 1 else cause)
            result = minimize(fixture(), execute)
            self.assertEqual(len(result.scenario.operations), 4)
            self.assertFalse(any(a["retained"] for a in result.attempts))

    def test_budget_exhaustion_keeps_last_actual_reproduction(self):
        result = minimize(fixture(), lambda _: SimpleNamespace(kind="violation", cause="same"), 1)
        self.assertTrue(result.exhausted)
        self.assertEqual(result.executions, 1)
        self.assertEqual(len(result.scenario.operations), 4)

    def test_non_violation_baseline_is_refused(self):
        with self.assertRaises(ValueError):
            minimize(fixture(), lambda _: SimpleNamespace(kind="consistent", cause=""))
