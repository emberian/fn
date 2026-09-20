"""Host-side tests for the contact scheduler driver.

These test the ordering and the bounds the host owns.  They do not test who is
selected, when a tick is admissible, or whether a bundle expired: those are
`books/scheduler.lisp`, exercised by `tests/acl2/scheduler-tests.lisp`.  The
fake host below records the call sequence so that the ordering the model
composes --- select, durable decision, durable attempt, commit --- is checked
as an ordering, without a second implementation of the decision.
"""

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from tools import scheduler


PLAN = {
    "peer": "dtn://peer/fn",
    "config": {"queue-bound": 4, "aging-limit": 2, "retry-bound": 16},
    "works": [{"work-id": "work-small", "class": "article", "size": 10},
              {"work-id": "work-big", "class": "article", "size": 1000}],
    "windows": [{"start": 0, "end": 1000, "ticks": [10, 20]},
                {"start": 5000, "end": 6000, "ticks": [5100]}],
    "expiries": [{"at-tick": 2, "work-id": "work-big",
                  "creation-time": 1599999000000, "lifetime": 100000,
                  "monotonic": 5100, "wall": 1600000000000,
                  "wall-error": 5000, "has-wall": True}],
}


class FakeHost(scheduler.SchedulerHost):
    """Records what the driver asked and answers from a fixed script."""

    def __init__(self, selections, admissible=None):
        self.calls = []
        self.selections = list(selections)
        self.admissible_script = admissible
        self.installed = None

    def install(self, plan, next_tx):
        self.installed = (plan, next_tx)
        self.calls.append(("install", next_tx))
        for work in plan.works:
            self.calls.append(("admit", work.work_id))

    def observe(self, event):
        self.calls.append(("observe", event.split()[0].strip("()")))

    def admissible(self):
        if self.admissible_script is None:
            return True
        return self.admissible_script.pop(0)

    def selection(self):
        return self.selections.pop(0) if self.selections else None

    def decision_octets(self, work_id, attempt_id):
        self.calls.append(("decision", work_id, attempt_id))
        return bytes([70, 78, 83, 67, 1, 1, 0, 0, 0, 4]) + b"\x01\x02\x03\x04"

    def commit(self, work_id, attempt_id):
        self.calls.append(("commit", work_id, attempt_id))

    def pass_tick(self):
        self.calls.append(("pass",))


class PlanReading(unittest.TestCase):
    def test_reads_a_plan(self):
        plan = scheduler.plan_from(PLAN)
        self.assertEqual(plan.peer, "dtn://peer/fn")
        self.assertEqual(plan.queue_bound, 4)
        self.assertEqual(len(plan.windows), 2)
        self.assertEqual(plan.windows[0].ticks, (10, 20))
        self.assertEqual(len(plan.expiries), 1)
        self.assertEqual(plan.works[1].size, 1000)

    def test_refuses_an_unknown_class(self):
        document = json.loads(json.dumps(PLAN))
        document["works"][0]["class"] = "postcard"
        self.assertRaises(scheduler.PlanError, scheduler.plan_from, document)

    def test_refuses_a_zero_bound(self):
        document = json.loads(json.dumps(PLAN))
        document["config"]["aging-limit"] = 0
        self.assertRaises(scheduler.PlanError, scheduler.plan_from, document)

    def test_refuses_a_backwards_window(self):
        document = json.loads(json.dumps(PLAN))
        document["windows"][0]["end"] = 0
        document["windows"][0]["start"] = 10
        self.assertRaises(scheduler.PlanError, scheduler.plan_from, document)

    def test_refuses_too_many_ticks(self):
        document = json.loads(json.dumps(PLAN))
        document["windows"][0]["ticks"] = list(range(scheduler.MAX_TICKS + 1))
        self.assertRaises(scheduler.PlanError, scheduler.plan_from, document)

    def test_refuses_a_half_age_anchor(self):
        document = json.loads(json.dumps(PLAN))
        document["expiries"][0]["age"] = 5
        self.assertRaises(scheduler.PlanError, scheduler.plan_from, document)

    def test_refuses_a_negative_size(self):
        document = json.loads(json.dumps(PLAN))
        document["works"][0]["size"] = -1
        self.assertRaises(scheduler.PlanError, scheduler.plan_from, document)

    def test_refuses_an_oversized_file(self):
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / "plan.json"
            path.write_bytes(b"{" + b" " * (scheduler.MAX_PLAN_BYTES + 1))
            self.assertRaises(scheduler.PlanError, scheduler.load_plan, path)


class WorkIdReading(unittest.TestCase):
    def test_reads_a_string_literal(self):
        self.assertEqual(scheduler.work_id_of(b'"work-small"'), "work-small")

    def test_refuses_a_bare_symbol(self):
        self.assertRaises(scheduler.PlanError, scheduler.work_id_of, b":NONE")

    def test_refuses_an_unbounded_identifier(self):
        long = b'"' + b"x" * (scheduler.MAX_TEXT + 1) + b'"'
        self.assertRaises(scheduler.PlanError, scheduler.work_id_of, long)


class DecisionLogging(unittest.TestCase):
    def test_trailer_is_over_exactly_the_acl2_octets(self):
        with tempfile.TemporaryDirectory() as root:
            log = scheduler.DecisionLog(Path(root))
            log.open()
            protected = bytes([70, 78, 83, 67, 1, 1, 0, 0, 0, 2, 9, 9])
            path = log.record(protected)
            stored = path.read_bytes()
            self.assertEqual(stored[:len(protected)], protected)
            self.assertEqual(stored[len(protected):],
                             hashlib.sha256(protected).digest())

    def test_refuses_a_refused_record(self):
        with tempfile.TemporaryDirectory() as root:
            log = scheduler.DecisionLog(Path(root))
            log.open()
            self.assertRaises(scheduler.PlanError, log.record, b"")

    def test_records_are_sequenced(self):
        with tempfile.TemporaryDirectory() as root:
            log = scheduler.DecisionLog(Path(root))
            log.open()
            log.record(b"one")
            log.record(b"two")
            self.assertEqual([p.name for p in log.entries()],
                             ["0000000000000000.sc", "0000000000000001.sc"])


class Driving(unittest.TestCase):
    def _run(self, selections, attempt, admissible=None):
        with tempfile.TemporaryDirectory() as root:
            host = FakeHost(selections, admissible)
            log = scheduler.DecisionLog(Path(root))
            plan = scheduler.plan_from(PLAN)
            outcomes = scheduler.run_plan(plan, host, log, attempt)
            return host, len(log.entries()), outcomes

    def test_decision_is_durable_before_the_attempt(self):
        seen = []

        def attempt(work_id, attempt_id, tick):
            seen.append(("attempt", work_id, tick))
            return True

        host, records, outcomes = self._run(["work-small", None, "work-big"], attempt)
        order = [c[0] for c in host.calls]
        first_decision = order.index("decision")
        first_commit = order.index("commit")
        self.assertLess(first_decision, first_commit)
        self.assertEqual(seen[0], ("attempt", "work-small", 0))
        self.assertEqual([o["outcome"] for o in outcomes],
                         ["submitted", "pass", "submitted"])
        self.assertEqual(records, 2)

    def test_a_refused_attempt_is_a_pass_and_charges_no_retry(self):
        def attempt(work_id, attempt_id, tick):
            return False

        host, _records, outcomes = self._run(["work-small", "work-small",
                                             "work-small"], attempt)
        self.assertEqual([o["outcome"] for o in outcomes],
                         ["refused", "refused", "refused"])
        self.assertNotIn("commit", [c[0] for c in host.calls])
        self.assertEqual([c[0] for c in host.calls].count("pass"), 3)

    def test_an_inadmissible_tick_selects_nothing(self):
        def attempt(work_id, attempt_id, tick):
            raise AssertionError("an inadmissible tick must not attempt")

        host, records, outcomes = self._run([], attempt,
                                            admissible=[False, False, False])
        self.assertEqual([o["outcome"] for o in outcomes],
                         ["inadmissible"] * 3)
        self.assertEqual(records, 0)

    def test_windows_open_and_close_around_their_ticks(self):
        def attempt(work_id, attempt_id, tick):
            return True

        host, _records, _outcomes = self._run([None, None, None], attempt)
        observed = [c[1] for c in host.calls if c[0] == "observe"]
        self.assertEqual(observed.count("fn-sched-open-event"), 2)
        self.assertEqual(observed.count("fn-sched-close-event"), 2)

    def test_the_expiry_is_observed_at_its_tick(self):
        def attempt(work_id, attempt_id, tick):
            return True

        host, _records, _outcomes = self._run([None, None, None], attempt)
        observed = [c[1] for c in host.calls if c[0] == "observe"]
        self.assertEqual(observed.count("fn-sched-expiry-event"), 1)
        self.assertLess(observed.index("fn-sched-expiry-event"),
                        len(observed) - 1)

    def test_every_work_in_the_plan_is_admitted_once(self):
        def attempt(work_id, attempt_id, tick):
            return True

        host, _records, _outcomes = self._run([None, None, None], attempt)
        admitted = [c[1] for c in host.calls if c[0] == "admit"]
        self.assertEqual(admitted, ["work-small", "work-big"])


class EventForms(unittest.TestCase):
    def test_expiry_event_carries_the_anchor_and_the_observation(self):
        plan = scheduler.plan_from(PLAN)
        form = scheduler.expiry_event(plan.expiries[0])
        self.assertIn("fn-sched-expiry-event", form)
        self.assertIn("fn-clock-observation 5100 1600000000000 5000 t", form)
        self.assertIn(" nil ", form)

    def test_an_age_anchor_becomes_a_pair(self):
        document = json.loads(json.dumps(PLAN))
        document["expiries"][0]["age"] = 7
        document["expiries"][0]["age-monotonic"] = 3
        plan = scheduler.plan_from(document)
        self.assertIn("(cons 7 3)", scheduler.expiry_event(plan.expiries[0]))


if __name__ == "__main__":
    unittest.main()
