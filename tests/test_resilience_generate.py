import unittest

from tools.resilience.adapters.simulator import driver
from tools.resilience.generate import acceptance, fault_choice


class GenerationTests(unittest.TestCase):
    def test_workload_seed_does_not_depend_on_fault_stream(self):
        def workload(s):
            return [(o.id, o.args) for o in s.operations if not o.id.startswith("stale-")]
        self.assertEqual(workload(acceptance(8, 1)), workload(acceptance(8, 99)))

    def test_fault_decision_does_not_depend_on_unrelated_action(self):
        self.assertEqual(fault_choice(77, "stale-2"), fault_choice(77, "stale-2"))
        a, b = acceptance(8, 77, 3), acceptance(8, 77, 4)
        self.assertEqual([f for f in a.faults if f.operation == "stale-2"],
                         [f for f in b.faults if f.operation == "stale-2"])

    def test_replay_and_healing_are_explicit_and_driver_consumable(self):
        for seed in range(16):
            s = acceptance(seed, seed + 10)
            self.assertEqual(s.to_json(), acceptance(seed, seed + 10).to_json())
            self.assertEqual([o.id for o in s.operations[-2:]], s.healing)
            self.assertIn(f"n={len(s.operations)}", driver(s))

    def test_generator_budget_is_a_harness_bound(self):
        for episodes in (0, 33, True):
            with self.assertRaises(ValueError):
                acceptance(1, 2, episodes)
