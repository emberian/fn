#!/usr/bin/env python3
"""The gate finding recorder: a bad outcome is a nonzero exit, never a gap.

F1 of `planning/review-2026-09-20-astra-followup.md`: a gate once watched
its promised behaviour fail, wrote the sentence into `gaps`, and exited 0.
`tools/deploy_gate.py`'s recorder (which tools/inn_lab.py inherits) is the
only way a finding is made; these cases hold its three-way distinction:

  * an exercised assertion that comes out false is `violated` and exits 1;
  * an insufficient observation is `inconclusive` and exits 3, never a pass;
  * an unreached or unavailable one is `not-exercised`/`not-built`, reported
    under its own name, and exits 0.

No socket, no node, no image: the classification and the exit code only.
(The two-node scenarios this file also drove retired with
tools/twonode_gate.py, python-diet T5; their subject is now
tests/test_native_peering.py.)
"""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import deploy_gate                                             # noqa: E402
from deploy_gate import (DeployGate, FindingError, GATE_INCONCLUSIVE,  # noqa: E402
                         GATE_OK, GATE_VIOLATED, HELD, INCONCLUSIVE, NOT_EXERCISED,
                         VIOLATED)


def gate():
    one = DeployGate.__new__(DeployGate)
    one.steps, one.found, one.facts = [], [], {}
    return one


class TheRecorderRefusesWhatItCannotCheck(unittest.TestCase):
    def test_a_claim_of_success_must_be_declared(self):
        with self.assertRaises(FindingError):
            gate().record("no-such-assertion", HELD, "invented")

    def test_a_failure_may_be_reported_without_a_declaration(self):
        """The inventory must not be a reason to swallow a failure."""
        one = gate()
        one.record("no-such-assertion", VIOLATED, "the subject failed")
        self.assertEqual(one.verdict(), VIOLATED)
        self.assertEqual(one.exit_code(), GATE_VIOLATED)

    def test_an_undeclared_instance_is_refused(self):
        with self.assertRaises(FindingError):
            gate().check("post-capability", True, "", instance="c")

    def test_an_undecided_finding_must_name_its_blocker(self):
        with self.assertRaises(FindingError):
            gate().record("post-capability", INCONCLUSIVE, "no reason given")

    def test_an_unknown_verdict_is_refused(self):
        with self.assertRaises(FindingError):
            gate().record("post-capability", "green", "not a verdict")

    def test_an_unreached_assertion_is_emitted_not_dropped(self):
        one = gate()
        one.check("post-capability", True, "")
        one.finalize_findings()
        found = [f for f in one.found if f.key == "outcomes-distinct"]
        self.assertEqual([f.verdict for f in found], [NOT_EXERCISED])
        self.assertTrue(found[0].blocker)
        self.assertEqual(one.exit_code(), GATE_OK)

    def test_an_inconclusive_run_is_not_a_pass(self):
        one = gate()
        one.inconclusive("post-capability", "no reply", "the owner never answered")
        self.assertEqual(one.exit_code(), GATE_INCONCLUSIVE)

    def test_a_violation_outranks_an_inconclusive(self):
        one = gate()
        one.inconclusive("post-capability", "no reply", "the owner never answered")
        one.check("outcomes-distinct", False, "refused exited 0")
        self.assertEqual(one.verdict(), VIOLATED)
        self.assertEqual(one.exit_code(), GATE_VIOLATED)

    def test_a_limitation_never_changes_the_exit(self):
        one = gate()
        one.check("post-capability", True, "")
        one.limitation("standing", "a postpublish fault is indeterminate (D13).")
        self.assertEqual(one.exit_code(), GATE_OK)
        self.assertIn("a postpublish fault is indeterminate (D13).", one.gaps)

    def test_the_gate_error_code_still_wins(self):
        self.assertEqual(gate().exit_code("stopped early"), 2)

    def test_the_digest_refuses_a_hand_typed_verdict(self):
        one = gate()
        one.check("outcomes-distinct", False, "refused exited 0")
        doc = one.findings_document("0000000", "tools/deploy_gate.py")
        self.assertEqual(doc["verdict"], VIOLATED)
        for row in doc["rows"]:
            if row["verdict"] == VIOLATED:
                row["verdict"] = HELD
        again = hashlib.sha256(json.dumps(
            doc["rows"], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        self.assertNotEqual(doc["rows_digest"], again)


class TheStdoutContractCarriesTheVerdict(unittest.TestCase):
    """`tools/verdict.py` reads the last lines; they must carry the words."""

    def test_the_summary_line_names_violations_and_inconclusives(self):
        one = gate()
        one.check("outcomes-distinct", False, "refused exited 0")
        one.inconclusive("post-capability", "no reply", "the owner never answered")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            deploy_gate.report(one)
        text = out.getvalue()
        self.assertRegex(text, r"^steps=\d+ failed=\d+ not-exercised=\d+ "
                               r"violated=1 inconclusive=1\n")
        self.assertIn("FAILED assertion outcomes-distinct", text)
        self.assertIn("INCONCLUSIVE post-capability", text)
        self.assertIn("verdict=violated", text)


if __name__ == "__main__":
    unittest.main()
