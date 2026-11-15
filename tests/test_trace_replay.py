"""Whole-result diagnostic projection controls, with handwritten scalar rows."""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location("fn2_trace_replay", Path(__file__).parents[1] / "tools" / "trace_replay.py")
assert _SPEC and _SPEC.loader
trace = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = trace
_SPEC.loader.exec_module(trace)

# The vectors do not call the implementation to construct expected effects.
N = 4294967295
START = [5, 7, 0, 0, 0, 0, 0, 0, N, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
EXTRA = [6, 10, 1, 0, 0, 0, 0, 0, N, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
END = [1, 7, 0, 0, 0, 0, 0, 1, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
CALENDAR = [["principal", 0], ["principal", 1], ["service", 0]]
QUEUES = [[0, 7, 8], [1, 9]]


class TraceReplayTests(unittest.TestCase):
    def project(self, records, lost=0):
        return trace.replay(records, lost, CALENDAR, 0, QUEUES)

    def test_whole_order_extra_then_ordinary_then_current_tail(self):
        self.assertEqual(self.project([START, EXTRA, END]),
                         trace.Projection(1, ((0, 8, 11, 7), (1, 9, 10))))
        self.assertEqual(QUEUES, [[0, 7, 8], [1, 9]])

    def test_standalone_and_already_queued_are_complete_effects(self):
        self.assertEqual(self.project([EXTRA, EXTRA]),
                         trace.Projection(0, ((0, 7, 8), (1, 9, 10))))

    def test_missing_effect_changes_whole_result(self):
        self.assertEqual(self.project([START, END]),
                         trace.Projection(1, ((0, 8, 11, 7), (1, 9))))
        self.assertNotEqual(self.project([START, END]), self.project([START, EXTRA, END]))

    def test_loss_and_gaps_never_validate(self):
        for records, lost in [([START, EXTRA, END], 1), ([START], 0), ([END], 0),
                              ([EXTRA, END], 0), ([START, START, END], 0)]:
            with self.subTest(records=records, lost=lost), self.assertRaises(trace.TraceError):
                self.project(records, lost)

    def test_mismatched_identity_or_action_extent_refuses(self):
        for index, replacement in [(1, 8), (2, 1), (3, 1), (10, 1)]:
            end = END.copy()
            end[index] = replacement
            with self.subTest(index=index), self.assertRaises(trace.TraceError):
                self.project([START, EXTRA, end])

    def test_forged_metadata_work_and_bad_principal_refuse(self):
        for index, replacement in [(2, 2), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (10, 1), (11, 1)]:
            extra = EXTRA.copy()
            extra[index] = replacement
            with self.subTest(index=index), self.assertRaises(trace.TraceError):
                self.project([START, extra, END])

    def test_ambiguous_or_untyped_initial_queues_refuse(self):
        for queues in [[[0, 7], [1, 7]], [[0, 7, 7]], [[True, 7]], [[0, N]]]:
            with self.subTest(queues=queues), self.assertRaises(trace.TraceError):
                trace.replay([], 0, CALENDAR, 0, queues)

    def test_hypothesis_removal_tail_before_ordinary_is_detected(self):
        self.assertNotEqual(self.project([START, EXTRA, END]),
                            trace.Projection(1, ((0, 8, 7, 11), (1, 9, 10))))


if __name__ == "__main__":
    unittest.main()
