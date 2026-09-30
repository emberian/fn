"""Backend fail-closed unit plus retained actual execution validation."""
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
from tools.resilience.adapters.typed_window_source import SourceBackend, ROOT
from tools.resilience.typed_window_model import observe, judge_scenario
from tools.resilience.scenario import Scenario

EVIDENCE = ROOT / "planning/evidence/resilience-typed-window-2026-09-30/backend"


class TypedSourceBackendTests(unittest.TestCase):
    def test_retained_actual_same_world_executions(self):
        for trial in (0, 1):
            directory = EVIDENCE / f"trial-{trial:04d}"
            scenario = Scenario.load(directory / "scenario.json")
            journal = observe((directory / "log").read_text(), trial)
            verdict = judge_scenario(scenario, journal, trial)
            self.assertEqual(verdict.kind, "consistent")
            self.assertIn("typed-window-settled", verdict.witnesses_observed)

    def test_source_echo_cannot_complete_a_trial(self):
        directory = EVIDENCE / "trial-0000"
        text = (directory / "log").read_text()
        # Retain the echoed CW form, remove the actual literal completion.
        text = text.replace("ACL2 !>FN_W7_TYPED_COMPLETE trial=0\n", "")
        scenario = Scenario.load(directory / "scenario.json")
        with tempfile.TemporaryDirectory(dir=ROOT / "build") as tmp:
            backend = SourceBackend(tmp, "unit-only-backend")
            backend.live = True  # Unit orchestration stub, no process started.
            with patch.object(backend, "command", return_value=SimpleNamespace(returncode=0, stdout="", stderr="")), \
                 patch.object(backend, "fetch", side_effect=lambda name, destination: Path(destination).write_text(text)):
                verdict = backend.execute(scenario)
            self.assertEqual(verdict.kind, "harness-failure")
            self.assertEqual(verdict.cause, "typed-source-trial-did-not-complete")

    def test_session_and_host_coordinates_are_bounded(self):
        for session, host in [("bad;name", "hbox"), ("valid", "other-host")]:
            with self.assertRaises(ValueError):
                SourceBackend(ROOT / "build/unit-unused", session, host)

    def test_retained_actual_alternate_idle_worker_binding(self):
        directory = EVIDENCE.parent / "worker-binding/trial-0000"
        scenario = Scenario.load(directory / "scenario.json")
        verdict = judge_scenario(scenario, observe((directory / "log").read_text(), 0), 0)
        self.assertEqual(verdict.kind, "consistent")
        self.assertIn("typed-window-settled", verdict.witnesses_observed)

    def test_declared_healing_bound_cannot_pass_without_measurement(self):
        directory = EVIDENCE / "trial-0000"
        scenario = Scenario.load(directory / "scenario.json")
        scenario.healing_bound = {"kind": "seconds", "value": 1, "source": "unit declared bound"}
        verdict = judge_scenario(scenario, observe((directory / "log").read_text(), 0), 0)
        self.assertEqual(verdict.kind, "harness-failure")
        self.assertEqual(verdict.cause, "typed-source-healing-unmeasured")

    def test_other_profile_witnesses_cannot_be_claimed(self):
        from tools.resilience.scenario import check, ScenarioError
        directory = EVIDENCE / "trial-0000"
        scenario = Scenario.load(directory / "scenario.json")
        scenario.witnesses = ["post-accepted"]
        with self.assertRaises(ScenarioError): check(scenario)

    def test_earlier_release_does_not_close_a_later_live_request(self):
        from tools.resilience.scenario import Operation
        evidence = EVIDENCE.parent
        data = json.loads((evidence / "model-trials.json").read_text())[0][:4]
        scenario = Scenario("prefix", "Terminal live request", "typed-window-model",
                            {"recipe": "typed-window-assigned-vector"}, [{"name": "core", "kind": "client"}],
                            [Operation(s["id"], "core", "window-" + s["action"],
                                       {"request": s["request"], "selector": s["selector"]}) for s in data],
                            [], [data[-1]["id"]], ["typed-window-settled"])
        journal = observe((evidence / "model-trials.log").read_text(), 0)
        journal.records = journal.records[:4]  # Oracle unit over retained actual transition prefix.
        self.assertEqual(judge_scenario(scenario, journal, 0).kind, "no-witness")
