"""Independent observed fixture and mutations of the response-model tester."""
import copy
import unittest

from tools.resilience import checker, mutations
from tools.resilience.adapters import response_holds
from tools.resilience.scenario import ScenarioError


def fixture():
    scenario = response_holds.example()
    views = [(0, 1, 1, 0, 0, ":ACQUIRED"), (0, 2, 3, 0, 0, ":ACQUIRED"),
             (1, 2, 3, 1, 0, "0"), (1, 1, 2, 1, 0, ":RELEASED"),
             (1, 1, 2, 1, 0, "0"), (1, 1, 2, 1, 0, ":ABSENT"),
             (1, 0, 0, 1, 0, ":RELEASED"), (1, 0, 0, 0, 1, "1")]
    lines = ["FN_SIM_PLAN s=response-holds-model k=0 n=8"]
    for i, (op, view) in enumerate(zip(scenario.operations, views)):
        fields = " ".join(f"{k}={v}" for k, v in zip(response_holds.VIEW, view))
        lines.append(f"FN_SIM_TRACE s=response-holds-model k=0 i={i} "
                     f"t={response_holds.KINDS[op.op]} o={op.args.get('owner', 0)} {fields}")
    lines.append("FN_SIM_RESULT s=response-holds-model r=passed")
    return scenario, "\n".join(lines)


class ResponseHoldsModelTests(unittest.TestCase):
    def test_two_holds_one_blocks_then_productive_settlement(self):
        s, output = fixture()
        j, v = response_holds.observe(s, output, 0, 0.1)
        self.assertTrue(v.green, v.to_json())
        self.assertEqual(len(j.of_kind("client")), 8)
        self.assertEqual(len(j.of_kind("internal")), 8)
        self.assertEqual(v.witnesses_missing, [])
        self.assertIn("response-holds-model-composition", v.pending_rules)

    def test_missing_duplicate_child_death_and_wrong_dispatch_never_pass(self):
        s, output = fixture()
        trace = next(line for line in output.splitlines() if "i=4 " in line)
        for changed, status in [(output.replace(trace, ""), 0), (output + "\n" + trace, 0),
                                (output, 1), (output.replace("i=4 t=:REAP", "i=4 t=:RELEASE"), 0),
                                (output.replace("i=4 t=:REAP o=0", "i=4 t=:REAP o=1"), 0)]:
            self.assertEqual(response_holds.observe(s, changed, status, 0.1)[1].kind, "harness-failure")

    def test_release_one_cannot_release_retirement_or_other_owner(self):
        s, output = fixture()
        for altered in [output.replace("i=4 t=:REAP o=0 g=1 h=1 q=2 p=1 r=0 a=0",
                                       "i=4 t=:REAP o=0 g=1 h=1 q=2 p=0 r=1 a=1"),
                        output.replace("i=3 t=:RELEASE o=0 g=1 h=1 q=2",
                                       "i=3 t=:RELEASE o=0 g=1 h=0 q=0"),
                        output.replace(":ACQUIRED", ":DUPLICATE")]:
            self.assertEqual(response_holds.observe(s, altered, 0, 0.1)[1].kind, "violation")

    def test_actual_duplicate_release_activation_is_required(self):
        s, output = fixture()
        self.assertEqual(response_holds.observe(s, output.replace(":ABSENT", ":RELEASED"), 0, 0.1)[1].kind,
                         "harness-failure")

    def test_suppression_disabled_fault_and_unsettled_terminal_never_pass(self):
        s, output = fixture()
        j, _ = response_holds.observe(s, output, 0, 0.1)
        for mutation in (mutations.suppress_workload, mutations.disable_fault_hook, mutations.kill_stage):
            altered_s, altered_j = mutation(s, j)
            self.assertFalse(checker.check(altered_s, altered_j).green)
        altered = copy.deepcopy(j)
        altered.records = [r for r in altered.records if r.get("event") != "response-model-terminal"]
        self.assertEqual(checker.check(s, altered).kind, "harness-failure")
        altered = copy.deepcopy(j)
        altered.records = [r for r in altered.records if r.get("event") != "response-model-oracle"]
        self.assertEqual(checker.check(s, altered).kind, "harness-failure")
        altered = copy.deepcopy(j)
        altered.of_kind("internal")[4]["p"] = "0"
        self.assertEqual(checker.check(s, altered).kind, "violation")
        self.assertEqual(checker.check(s, j, checker.Budget(max_records=2)).kind, "inconclusive")

    def test_driver_rejects_reader_text_and_other_contract_or_initial(self):
        for changed in ("owner", "contract", "initial"):
            s = response_holds.example()
            if changed == "owner":
                s.operations[0].args["owner"] = '#.(evil)'
            elif changed == "contract":
                s.contract = "acceptance-model"
            else:
                s.initial["prior"] = [dict(id="unexpected")]
            with self.assertRaises((ValueError, ScenarioError)):
                response_holds.driver(s)


if __name__ == "__main__":
    unittest.main()
