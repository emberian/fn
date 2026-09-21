#!/usr/bin/env python3
"""Inject each bad outcome into a real scenario and require a nonzero exit.

This is the completion condition of F1 in
`planning/review-2026-09-20-astra-followup.md`: before this file, the two-node
gate's `scenario_feed_peer_cut` could observe the article never arriving, two
accepted transfers across one lost reply, or the wrong final group count, and
the gate exited 0 -- every one of those appended a sentence to `gaps`, and
`gaps` was not read by the exit calculation at all.  The review's
`planning/evidence/astra-followup-2026-09-20/probe.py` demonstrated it by
driving the actual scenario method with simulated boundary responses; this
file is that probe turned into a committed regression, with the assertions
inverted: each injected outcome must now FAIL its assertion and the gate's
exit must be nonzero.

What it does and does not establish.  It drives the real
`TwoNodeGate.scenario_feed_peer_cut`, `scenario_feed_restart` and
`DeployGate`'s finding recorder with simulated boundary outcomes.  No socket,
no node, no ACL2 and no store: what it establishes is the gate's classification
and its exit code, which is exactly what F1 is about.  Whether two real fn
nodes recover from a lost reply is what running the gate on the box answers.

The three-way distinction the review asks for is asserted here directly:

  * an exercised assertion that comes out false is `violated` and exits 1;
  * a scenario whose observation was insufficient is `inconclusive` and exits
    3, which must not be read as a pass;
  * an unavailable feature is `not-built`/`not-exercised`, is reported under
    its own name, and exits 0.
"""
import json
from pathlib import Path
import sys
from types import SimpleNamespace as NS
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import deploy_gate                                             # noqa: E402
import twonode_gate                                            # noqa: E402
from deploy_gate import (FindingError, GATE_INCONCLUSIVE,      # noqa: E402
                         GATE_OK, GATE_VIOLATED, HELD, INCONCLUSIVE,
                         NOT_BUILT, NOT_EXERCISED, Step, VIOLATED)
from twonode_gate import GROUPS, TwoNodeGate                    # noqa: E402


def verdicts(gate, key):
    """Every verdict recorded under one assertion key, in order."""
    return [one.verdict for one in gate.found if one.key == key]


def one_verdict(gate, key):
    found = verdicts(gate, key)
    if len(found) != 1:
        raise AssertionError("{}: expected one finding, got {}".format(key, found))
    return found[0]


class Harness:
    """A TwoNodeGate with its boundary replaced by injected outcomes.

    Every method below that the scenario calls is a boundary: a command on the
    host, a tap read, a node start.  The scenario itself -- the order of the
    phases, which answers it asserts over, and how it classifies them -- is the
    real code, unmodified.
    """

    def __init__(self, *, arrived=True, accepted_lines=1, end_count=1,
                 start_count=0, cut_taken=True, posted=True, tap=True,
                 post_enabled=True, restart_ok=True, offers=1, alive=True):
        gate = TwoNodeGate.__new__(TwoNodeGate)
        gate.steps, gate.found, gate.facts = [], [], {}
        gate.deploy = "/simulated/deploy"
        gate.rev = "0000000"
        gate.keep = True
        gate.a = twonode_gate.NodeSpec(gate, "a")
        gate.b = twonode_gate.NodeSpec(gate, "b")
        gate.nodes = (gate.a, gate.b)
        gate.a.port, gate.b.port = 1111, 3333
        gate.a.pid, gate.b.pid = "4242", "4343"
        gate.a.post_enabled = gate.b.post_enabled = post_enabled
        gate.b.tap_port = 2222 if tap else 0
        gate.a.tap_port = 2222 if tap else 0
        self.gate = gate
        self.arrived = arrived
        self.accepted_lines = accepted_lines
        self.end_count = end_count
        self.start_count = start_count
        self.cut_taken = cut_taken
        self.posted = posted
        self.restart_ok = restart_ok
        self.offers = offers
        self.alive = alive
        self.presence_calls = 0
        # One offer line per message-id the two scenarios use: each scenario
        # greps the tap for lines naming ITS article, so a single fixture
        # serves both without either seeing the other's.
        self.wire = ("".join("C> IHAVE {}\n".format(one)
                             for one in ("<fed-cut@example.invalid>",
                                         "<fed-restart@example.invalid>")) * offers
                     + "S< 239 accepted\n" * accepted_lines)

        gate.feed = self.feed
        gate.tap_mark = lambda node: 0
        gate.stop_node = lambda *a, **k: None
        gate.start_node = lambda *a, **k: self.restart_ok
        gate.sh = self.sh
        gate.read_tap = self.read_tap
        gate.log_tail = lambda node, why: self.step("log tail", "")
        gate.require_live = lambda node, where: gate.check(
            "node-live", self.alive, "node {} was not running at {}".format(
                node.upper, where), instance=node.name)

    # -- the boundary -----------------------------------------------------
    def step(self, name, output, rc=0, expect=None):
        found = Step(name, "SIMULATED boundary outcome", rc, output, 0.0,
                     expect=expect)
        self.gate.steps.append(found)
        return found

    def sh(self, name, command, **kwargs):
        if "arm the tap" in name:
            return self.step(name, "")
        if "arming file was consumed" in name:
            return self.step(name, "CUT-TAKEN" if self.cut_taken else "STILL-ARMED")
        if "FNFD journal" in name:
            return self.step(name, "-rw-r--r-- 1 x x 120 feed-b.fnfd")
        if "kill -9" in name:
            return self.step(name, "")
        return self.step(name, "", expect=kwargs.get("expect"))

    def read_tap(self, node, name, since=0, expect=0):
        return self.step(name, self.wire)

    def feed(self, phase, extra, name=None, timeout=300, expect=0):
        if phase == "post":
            value = {"ok": self.posted, "result": "240" if self.posted else "441"}
        elif phase == "wait":
            value = {"ok": self.arrived,
                     "status": "article" if self.arrived else "timeout",
                     "attempts": 1, "identical": self.arrived}
        else:
            count = self.start_count if self.presence_calls == 0 else self.end_count
            self.presence_calls += 1
            value = {"groups": {GROUPS[0]: "211 {} 1 {} {}".format(
                count, max(count, 1), GROUPS[0])}}
        return self.step(name or phase, json.dumps(value),
                         1 if phase == "wait" and not self.arrived else 0, expect)

    # -- driving ----------------------------------------------------------
    def cut(self):
        self.gate.scenario_feed_peer_cut()
        return self.gate

    def restart(self):
        self.gate.scenario_feed_restart()
        return self.gate


class TheLostReplyScenarioFails(unittest.TestCase):
    """F1's three injected outcomes, each of which used to exit 0."""

    def test_nondelivery_after_the_cut_fails_the_gate(self):
        gate = Harness(arrived=False, accepted_lines=0, end_count=0).cut()
        self.assertEqual(one_verdict(gate, "cut-arrival"), VIOLATED)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)
        self.assertTrue(any("is lost between two nodes that are both up" in one.detail
                            for one in gate.found if one.verdict == VIOLATED))

    def test_two_accepted_transfers_across_one_lost_reply_fails_the_gate(self):
        gate = Harness(arrived=True, accepted_lines=2, end_count=1).cut()
        self.assertEqual(one_verdict(gate, "cut-at-most-one"), VIOLATED)
        self.assertEqual(one_verdict(gate, "cut-arrival"), HELD)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)

    def test_the_wrong_final_group_count_fails_the_gate(self):
        gate = Harness(arrived=True, accepted_lines=1, end_count=2).cut()
        self.assertEqual(one_verdict(gate, "cut-copies"), VIOLATED)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)

    def test_a_clean_lost_reply_recovery_passes(self):
        gate = Harness(arrived=True, accepted_lines=1, end_count=1).cut()
        for key in ("cut-post", "cut-taken", "cut-arrival", "cut-at-most-one",
                    "cut-copies"):
            self.assertEqual(one_verdict(gate, key), HELD, key)
        self.assertEqual(gate.exit_code(), GATE_OK)

    def test_a_cut_that_never_fired_is_inconclusive_not_a_pass(self):
        """The scenario ran, delivered, and measured an ordinary transfer."""
        gate = Harness(arrived=True, accepted_lines=1, end_count=1,
                       cut_taken=False).cut()
        self.assertEqual(one_verdict(gate, "cut-taken"), INCONCLUSIVE)
        self.assertEqual(gate.exit_code(), GATE_INCONCLUSIVE)

    def test_no_tap_leaves_every_cut_assertion_inconclusive(self):
        gate = Harness(tap=False).cut()
        for key in ("cut-taken", "cut-arrival", "cut-at-most-one", "cut-copies"):
            self.assertEqual(one_verdict(gate, key), INCONCLUSIVE, key)
        self.assertEqual(gate.exit_code(), GATE_INCONCLUSIVE)

    def test_an_unavailable_feature_is_reported_and_does_not_fail(self):
        """The review's explicit carve-out: unavailable may be unexercised."""
        gate = Harness(post_enabled=False).cut()
        for key in ("cut-post", "cut-taken", "cut-arrival", "cut-at-most-one",
                    "cut-copies"):
            self.assertEqual(one_verdict(gate, key), NOT_BUILT, key)
        self.assertEqual(gate.exit_code(), GATE_OK)
        self.assertTrue(all(one.blocker for one in gate.found
                            if one.verdict == NOT_BUILT))

    def test_a_refused_post_leaves_the_rest_inconclusive(self):
        gate = Harness(posted=False).cut()
        self.assertEqual(one_verdict(gate, "cut-post"), VIOLATED)
        self.assertEqual(one_verdict(gate, "cut-arrival"), INCONCLUSIVE)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)


class TheRestartScenarioFails(unittest.TestCase):
    """The review names the restart scenario as sharing F1's pattern."""

    def test_no_arrival_after_the_kill_fails_the_gate(self):
        gate = Harness(arrived=False, accepted_lines=0).restart()
        self.assertEqual(one_verdict(gate, "k5-arrival"), VIOLATED)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)

    def test_two_accepted_transfers_across_the_kill_fails_the_gate(self):
        gate = Harness(arrived=True, accepted_lines=2).restart()
        self.assertEqual(one_verdict(gate, "k5-exactly-one"), VIOLATED)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)

    def test_no_recorded_offer_is_inconclusive(self):
        gate = Harness(arrived=True, accepted_lines=1, offers=0).restart()
        self.assertEqual(one_verdict(gate, "k5-exactly-one"), HELD)
        self.assertEqual(one_verdict(gate, "k5-offer-recorded"), INCONCLUSIVE)
        self.assertEqual(gate.exit_code(), GATE_INCONCLUSIVE)

    def test_a_node_that_does_not_restart_fails_the_gate(self):
        gate = Harness(restart_ok=False).restart()
        self.assertEqual(one_verdict(gate, "k5-restart"), VIOLATED)
        self.assertEqual(one_verdict(gate, "k5-arrival"), INCONCLUSIVE)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)

    def test_a_clean_restart_by_offer_passes(self):
        gate = Harness(arrived=True, accepted_lines=1, offers=1).restart()
        for key in ("k5-post", "k5-journal", "k5-restart", "k5-arrival",
                    "k5-exactly-one", "k5-offer-recorded"):
            self.assertEqual(one_verdict(gate, key), HELD, key)
        self.assertEqual(gate.exit_code(), GATE_OK)


class TheRecorderRefusesWhatItCannotCheck(unittest.TestCase):
    """The emitter is the only way a finding is made, and it validates."""

    def gate(self):
        gate = TwoNodeGate.__new__(TwoNodeGate)
        gate.steps, gate.found, gate.facts = [], [], {}
        return gate

    def test_a_claim_must_be_declared(self):
        gate = self.gate()
        with self.assertRaises(FindingError):
            gate.record("no-such-assertion", VIOLATED, "invented")

    def test_an_undeclared_instance_is_refused(self):
        gate = self.gate()
        with self.assertRaises(FindingError):
            gate.check("cut-arrival", True, "", instance="c")

    def test_an_undecided_finding_must_name_its_blocker(self):
        gate = self.gate()
        with self.assertRaises(FindingError):
            gate.record("cut-arrival", INCONCLUSIVE, "no reason given")

    def test_an_unknown_verdict_is_refused(self):
        gate = self.gate()
        with self.assertRaises(FindingError):
            gate.record("cut-arrival", "green", "not a verdict")

    def test_an_unreached_assertion_is_emitted_not_dropped(self):
        gate = Harness().cut()
        gate.finalize_findings()
        self.assertEqual(one_verdict(gate, "a-survives-b-kill"), NOT_EXERCISED)
        for one in gate.found:
            if one.verdict == NOT_EXERCISED:
                self.assertTrue(one.blocker)

    def test_the_digest_refuses_a_hand_typed_verdict(self):
        gate = Harness(arrived=False).cut()
        doc = gate.findings_document("0000000", "tools/twonode_gate.py")
        self.assertEqual(doc["verdict"], VIOLATED)
        import hashlib
        for row in doc["rows"]:
            if row["verdict"] == VIOLATED:
                row["verdict"] = HELD
                break
        again = hashlib.sha256(json.dumps(
            doc["rows"], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        self.assertNotEqual(doc["rows_digest"], again)

    def test_a_limitation_never_changes_the_exit(self):
        gate = Harness().cut()
        gate.limitation("standing", "a postpublish fault is indeterminate (D13).")
        self.assertEqual(gate.exit_code(), GATE_OK)
        self.assertIn("a postpublish fault is indeterminate (D13).", gate.gaps)

    def test_a_violation_outranks_an_inconclusive(self):
        gate = Harness(arrived=True, end_count=2, cut_taken=False).cut()
        self.assertEqual(one_verdict(gate, "cut-taken"), INCONCLUSIVE)
        self.assertEqual(one_verdict(gate, "cut-copies"), VIOLATED)
        self.assertEqual(gate.verdict(), VIOLATED)
        self.assertEqual(gate.exit_code(), GATE_VIOLATED)

    def test_the_gate_error_code_still_wins(self):
        gate = Harness().cut()
        self.assertEqual(gate.exit_code("stopped early"), 2)


class TheStdoutContractCarriesTheVerdict(unittest.TestCase):
    """`tools/verdict.py` reads the last lines; they must carry the new words."""

    def test_the_summary_line_names_violations_and_inconclusives(self):
        import io
        import contextlib
        gate = Harness(arrived=True, end_count=2, cut_taken=False).cut()
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            deploy_gate.report(gate)
        text = out.getvalue()
        self.assertRegex(text, r"^steps=\d+ failed=\d+ not-exercised=\d+ "
                               r"violated=[1-9]\d* inconclusive=[1-9]\d*\n")
        self.assertIn("FAILED assertion cut-copies", text)
        self.assertIn("INCONCLUSIVE cut-taken", text)
        self.assertIn("verdict=violated", text)


if __name__ == "__main__":
    unittest.main()
