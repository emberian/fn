from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import acl2_cost


class Acl2Cost(unittest.TestCase):
    def setUp(self):
        self.log = (ROOT / 'tests/fixtures/acl2_cost/conn-kind-summary-excerpts.log').read_text()

    def test_wrapped_actual_event_name(self):
        first = acl2_cost.events(self.log)[0]
        self.assertIn('FN2-ARMS-OK-1-FN2-CONN-FN2-MACHINES-FN2-POOL-FN2-CONTROL-OF-TUPLE', first.form)
        self.assertNotIn('Rules:', first.form)

    def test_proof_work_and_time_are_distinct(self):
        most_steps = acl2_cost.costliest_event(self.log)
        slowest = acl2_cost.slowest_event(self.log)
        self.assertEqual(most_steps.steps, 145713)
        self.assertEqual(most_steps.seconds, 0.64)
        self.assertIn('INITIALIZE-ROWS-TYPE', most_steps.form)
        self.assertEqual(slowest.seconds, 1.38)
        self.assertIn('DEFUN FN2-MACHINE-ADMIT', slowest.form)
        self.assertEqual(acl2_cost.book_steps(self.log), 1206838)

    def test_missing_step_count_does_not_hide_timed_event(self):
        log = 'Summary\nForm: (DEFUN COMPILE-ONLY ...)\nRules: NIL\nTime: 2.0 seconds\n'
        self.assertIsNone(acl2_cost.costliest_event(log))
        self.assertEqual(acl2_cost.slowest_event(log).seconds, 2.0)


if __name__ == '__main__':
    unittest.main()
