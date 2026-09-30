"""Tester mutations for the model backend, using a hand-written fixture."""
import copy
import tempfile
import unittest
from pathlib import Path

from tools.resilience import checker, mutations
from tools.resilience.adapters import simulator
from tools.resilience.journal import Journal, TruncatedHistory
from tools.resilience.scenario import ScenarioError, check as validate


def fixture():
    s = simulator.example()
    # Observable views specified independently, not computed by the checker.
    views = [("0", "A", "NIL", "0"), ("1", "none", "NIL", "1"),
             ("1", "B", "NIL", "1"), ("1", "B", "NIL", "1"),
             ("1", "B", "T", "1"), ("1", "B", "T", "1"),
             ("1", "none", "NIL", "1"), ("1", "none", "NIL", "1"),
             ("1", "B", "NIL", "1"), ("2", "none", "NIL", "3")]
    lines = ["FN_SIM_PLAN s=acceptance-world k=0 n=10"]
    for i, (o, view) in enumerate(zip(s.operations, views)):
        detail = " ".join(f"{k}={v}" for k, v in zip(simulator.VIEW, view))
        a = o.args
        x = ":" + a["result"].upper() if "result" in a else "-"
        lines += [f"FN_SIM_ORACLE s=acceptance-world k=0 i={i} {detail}",
                  f"FN_SIM_TRACE s=acceptance-world k=0 i={i} t={simulator.KINDS[o.op]} "
                  f"m={a['identity']} g={a['generation']} x={x} {detail}"]
    lines.append("FN_SIM_RESULT s=acceptance-model r=passed")
    return s, "\n".join(lines)


class SimulatorAdapterTests(unittest.TestCase):
    def setUp(self):
        self.s, self.output = fixture()
        self.j, self.v = simulator.observe(self.s, self.output, 0, 0.1)

    def test_fixture_productive_and_settled(self):
        self.assertTrue(self.v.green)
        self.assertEqual(self.v.witnesses_missing, [])
        self.assertEqual(len(self.j.of_kind("client")), 10)
        self.assertEqual(len([r for r in self.j.of_kind("environment")
                             if r.get("event") == "fault-fired"]), 3)

    def test_suppressed_workload_disabled_fault_killed_stage(self):
        for mutation in (mutations.suppress_workload, mutations.disable_fault_hook,
                         mutations.kill_stage):
            s, j = mutation(self.s, self.j)
            self.assertFalse(checker.check(s, j).green)

    def test_universal_refusal_and_omitted_operation(self):
        j = copy.deepcopy(self.j)
        for r in j.of_kind("client"):
            r.update(a="0", p="none", f="NIL", q="0")
        self.assertEqual(checker.check(self.s, j).kind, "violation")
        j.records = [r for r in self.j.records if r.get("operation") != "durable-B"]
        self.assertFalse(checker.check(self.s, j).green)

    def test_child_death_truncation_wrong_dispatch_and_corrupt_oracle(self):
        cases = [(self.output, 73), (self.output.rsplit("\n", 1)[0], 0),
                 (self.output.replace("g=8", "g=7"), 0),
                 (self.output.replace("i=9 a=2", "i=9 a=0"), 0)]
        for text, code in cases:
            _, v = simulator.observe(self.s, text, code, 0.1)
            self.assertFalse(v.green)

    def test_changed_success_expectation_does_not_activate_fault(self):
        s = copy.deepcopy(self.s)
        s.operations[4].args["result"] = "durable"
        output = self.output.replace("x=:INDETERMINATE", "x=:DURABLE")
        _, verdict = simulator.observe(s, output, 0, 0.1)
        self.assertEqual(verdict.kind, "harness-failure")
        self.assertIn("fault-never-occurred", verdict.cause)

    def test_terminal_ownership_required(self):
        j = copy.deepcopy(self.j)
        j.records = [r for r in j.records if r.get("event") != "model-terminal"]
        self.assertFalse(checker.check(self.s, j).green)

    def test_model_counterexample_is_not_a_harness_failure(self):
        _, verdict = simulator.observe(self.s, self.output.replace("r=passed", "r=failed"),
                                       0, 0.1)
        self.assertEqual(verdict.kind, "violation")
        self.assertEqual(verdict.cause, "model-oracle-rejected")

    def test_budget_exhaustion_remains_inconclusive(self):
        for budget in (checker.Budget(max_histories=0), checker.Budget(max_records=1)):
            self.assertEqual(checker.check(self.s, self.j, budget).kind, "inconclusive")

    def test_truncated_journal_and_edited_verdict_fail(self):
        with tempfile.TemporaryDirectory() as root:
            path = self.j.write(Path(root) / "journal.jsonl")
            mutations.truncate_history(path)
            with self.assertRaises(TruncatedHistory):
                Journal.read(path)
        self.v.kind = "violation"
        self.v.sign()
        corrupted = mutations.corrupt_checker_result(self.v)
        self.assertFalse(corrupted.verify())

    def test_reader_input_cannot_be_lisp_source(self):
        s = copy.deepcopy(self.s)
        s.operations[0].args["identity"] = 'A") (quit) ('
        with self.assertRaises(ScenarioError):
            simulator.driver(s)
        s = copy.deepcopy(self.s)
        s.operations[0].args["generation"] = True
        with self.assertRaises(ScenarioError):
            validate(s)


if __name__ == "__main__":
    unittest.main()
