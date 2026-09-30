"""Mutations of the simulator evidence gate, never evidence about fn."""
import copy
import unittest

from tools.run_simulator import parse_records, scenario_passed, TRACE_PREFIX


def complete_world():
    plans, traces, oracles = [], [], []
    lengths = [2] * 6 + [4] * 4
    for k, (a, b) in enumerate((a, b) for a in lengths for b in lengths):
        plans.append(dict(s="acceptance-world", k=str(k), n=str(a + b)))
        for i in range(a + b):
            row = dict(s="acceptance-world", k=str(k), i=str(i),
                       a="0", p="none", f="NIL", q="0")
            traces.append(dict(row, t=":PREPARE", m="A", g="7", x="-"))
            oracles.append(dict(row))
    return plans, traces, oracles


class SimulatorGateTests(unittest.TestCase):
    def setUp(self):
        self.plans, self.traces, self.oracles = complete_world()
        self.result = [dict(s="acceptance-world", r="passed", n="100")]

    def passed(self, **changes):
        args = dict(scenario="acceptance-world", exit_code=0, parse_error=None,
                    traces=self.traces, results=self.result,
                    plans=self.plans, oracles=self.oracles)
        args.update(changes)
        return scenario_passed(**args)

    def test_complete_record_shapes(self):
        self.assertTrue(self.passed())

    def test_child_death_and_missing_results(self):
        self.assertFalse(self.passed(exit_code=73))
        self.assertFalse(self.passed(results=[]))
        self.assertFalse(self.passed(results=self.result * 2))

    def test_truncation_and_duplicate_step(self):
        self.assertFalse(self.passed(traces=self.traces[:-1]))
        mutated = self.traces[:]
        mutated[200] = mutated[199]
        self.assertFalse(self.passed(traces=mutated))

    def test_shortened_world_cannot_claim_completion(self):
        self.assertFalse(self.passed(plans=self.plans[:1], traces=self.traces[:4],
                                     oracles=self.oracles[:4],
                                     results=[dict(s="acceptance-world", r="passed", n="1")]))

    def test_independent_oracle_missing_or_disagrees(self):
        self.assertFalse(self.passed(oracles=[]))
        mutated = copy.deepcopy(self.oracles)
        mutated[30]["p"] = "A"
        self.assertFalse(self.passed(oracles=mutated))

    def test_duplicate_field_refused(self):
        with self.assertRaises(ValueError):
            parse_records(TRACE_PREFIX + "s=world s=other", TRACE_PREFIX)

    def test_durable_repeated_steps_are_not_completion(self):
        result = [dict(s="acceptance-durable", r="passed")]
        self.assertFalse(scenario_passed("acceptance-durable", 0, None,
                          [dict(s="acceptance-durable", t="initial")] * 3, result))


if __name__ == "__main__":
    unittest.main()
