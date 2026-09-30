import unittest
from tools.resilience.typed_window_model import Step, validate, driver, expectations, dependencies, observe, judge

class TypedWindowModelTests(unittest.TestCase):
    def test_release_reacquire_and_old_request(self):
        steps = [Step("r", "return"), Step("s", "release"), Step("a", "admit", "next"),
                 Step("q", "acquire", "next"), Step("old", "return"), Step("new", "return", "next")]
        views = expectations(steps)
        self.assertEqual([v["answer"] for v in views], [":RETURNED", ":RELEASED", ":ADMITTED", ":ASSIGNED", ":STALE-JOB", ":RETURNED"])
        self.assertIn("a", dependencies(steps)["q"])
    def test_symbolic_labels_never_enter_executable_text(self):
        label = '\" (value-triple :injected)'
        text = driver([Step(label, "admit", label), Step("use", "acquire", label)], 2)
        self.assertNotIn(label, text)
        with self.assertRaises(ValueError): validate([Step("use", "return", "missing")])
    def test_partial_trial_fails_closed(self):
        verdict = judge([Step("c", "cancel")], observe("", 0), 0)
        self.assertEqual(verdict.kind, "harness-failure")
    def test_actual_literal_parser_and_named_violation(self):
        steps = [Step("c", "cancel")]
        text = "FN_W7_TYPED trial=0 step=0 answer=:CANCELLED phase=:CANCELLED-RUNNING bytes=320 workers=1 close=:READ-FILE-HELD"
        self.assertEqual(judge(steps, observe(text, 0), 0).kind, "consistent")
        self.assertEqual(judge(steps, observe(text.replace("bytes=320", "bytes=64"), 0), 0).kind, "violation")
        self.assertEqual(len(observe(text, 1).records), 0)

    def test_retained_actual_acl2_trials(self):
        import json
        from pathlib import Path
        evidence = Path(__file__).resolve().parents[1] / "planning/evidence/resilience-typed-window-2026-09-30"
        text = (evidence / "model-trials.log").read_text()
        for i, case in enumerate(json.loads((evidence / "model-trials.json").read_text())):
            self.assertEqual(judge([Step(**s) for s in case], observe(text, i), i).kind, "consistent")

    def test_shared_scenario_and_reducer_keep_state_producers(self):
        from tools.resilience.scenario import Scenario, Operation, check, ScenarioError
        from tools.resilience.typed_window_model import from_scenario
        from tools.resilience.shrink import dependencies, delete
        scenario = Scenario("typed", "Typed lifecycle", "typed-window-model",
                            {"recipe": "typed-window-assigned-vector"},
                            [{"name": "client", "kind": "client"}],
                            [Operation("return", "client", "window-return"),
                             Operation("release", "client", "window-release"),
                             Operation("admit", "client", "window-admit", {"request": "next"}),
                             Operation("acquire", "client", "window-acquire", {"request": "next"})],
                            [], ["release"], ["typed-window-settled"])
        check(scenario)
        self.assertEqual(from_scenario(scenario)[-1].request, "next")
        self.assertEqual(dependencies(scenario)["acquire"], {"admit"})
        self.assertEqual(len(delete(scenario, "admit").operations), 2)
        scenario.operations[0] = Operation("bad", "client", "window-return", {"request": "future"})
        with self.assertRaises(ScenarioError): check(scenario)

    def test_shared_settlement_witness_uses_actual_execution(self):
        import json
        from pathlib import Path
        from tools.resilience.scenario import Scenario, Operation
        from tools.resilience.typed_window_model import judge_scenario
        evidence = Path(__file__).resolve().parents[1] / "planning/evidence/resilience-typed-window-2026-09-30"
        cases = json.loads((evidence / "model-trials.json").read_text())
        text = (evidence / "model-trials.log").read_text()
        for trial, expected in [(0, "consistent"), (2, "no-witness")]:
            operations = [Operation(s["id"], "client", "window-" + s["action"],
                                    {"request": s["request"], "selector": s["selector"]}) for s in cases[trial]]
            scenario = Scenario("actual", "Actual typed trial", "typed-window-model",
                                {"recipe": "typed-window-assigned-vector"},
                                [{"name": "client", "kind": "client"}], operations,
                                [], [operations[-1].id], ["typed-window-settled"])
            self.assertEqual(judge_scenario(scenario, observe(text, trial), trial).kind, expected)

    def test_retained_bundle_campaign_actual_verdicts(self):
        import json
        from pathlib import Path
        from tools.resilience.scenario import Scenario
        from tools.resilience.typed_window_model import judge_scenario
        evidence = Path(__file__).resolve().parents[1] / "planning/evidence/resilience-typed-window-2026-09-30/stateful"
        text = (evidence / "stateful-trials.log").read_text()
        for i, data in enumerate(json.loads((evidence / "stateful-trials.json").read_text())):
            verdict = judge_scenario(Scenario.from_json(data), observe(text, i), i)
            self.assertEqual(verdict.kind, "consistent")
            self.assertIn("typed-window-settled", verdict.witnesses_observed)
