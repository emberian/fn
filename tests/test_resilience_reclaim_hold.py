"""Capture-first independent response observer; no native execution implied."""
import copy
import unittest

from tests.native_harness import EXIT
from tools.resilience import checker, mutations
from tools.resilience.adapters import reclaim_hold
from tools.resilience.journal import Journal


def fixture():
    s = reclaim_hold.example()
    j = Journal(s.id)
    j.stage("workload", "begun")
    j.client("response-hold", operation="hold", cid=7, group="211 5 1 5 fn.test")
    j.client("read", operation="read-prior", result="match", during_competing_work=True)
    j.client("reclaim", operation="reclaim-1", installed=False, returncode=0)
    j.environment("fault-fired", operation="reclaim-1", boundary="reclaim-candidate-selected",
                  action="interleave", stage="performed", cid=7)
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    j.client("response-drain", operation="release", cid=7, status="224 Overview information", numbers=[1, 2, 3, 4, 5])
    j.client("reclaim", operation="reclaim-heal", installed=True, returncode=0)
    j.client("read", operation="read-retained", result="match", expired_status="430 article reclaimed")
    for row in [dict(phase="captured"), dict(phase="held", cid=7),
                dict(phase="settled", cid=8, status="released"),
                dict(phase="deferred", reason="readers"),
                dict(phase="settled", cid=7, status="released"),
                dict(phase="captured"), dict(phase="installed", records=5, reclaimed=2, dropped=1)]:
        j.environment("response-reclaim", **row)
    j.environment("response-terminal", cid=7)
    j.stage("healing", "ended", elapsed=1.0)
    return s, j


class ReclaimHoldObserverTests(unittest.TestCase):
    def test_native_markers_parse_without_reconstructing_generation(self):
        rows = reclaim_hold.events(
            b"RECLAIM held at=captured\nOVER quantum-held cid=7\n"
            b"RECLAIM deferred reason=readers\nOVER response-settled cid=7 status=released\n"
            b"RECLAIM installed records=5 reclaimed=2 dropped=1 ms=12\n")
        self.assertEqual([r["phase"] for r in rows], ["captured", "held", "deferred", "settled", "installed"])
        self.assertEqual(rows[1]["cid"], 7)

    def test_independent_response_after_capture_then_productive_settlement(self):
        s, j = fixture()
        v = checker.check(s, j)
        self.assertTrue(v.green, v.to_json())
        self.assertIn("reclaim-response-native-composition", v.pending_rules)
        self.assertIn("response-hold-settled", v.witnesses_observed)

    def test_old_hold_premature_install_wrong_settlement_and_duplicate_release_refute(self):
        for mutation in ("hold-first", "install-held", "wrong-cid", "duplicate-release"):
            s, j = fixture()
            rows = [r for r in j.of_kind("environment") if r.get("event") == "response-reclaim"]
            if mutation == "hold-first":
                rows[0].update(phase="held", cid=7)
                rows[1].update(phase="captured")
            elif mutation == "install-held":
                rows[3].update(phase="installed", reclaimed=2)
            elif mutation == "wrong-cid":
                rows[4]["cid"] = 99
            else:
                rows[5].update(phase="settled", cid=7, status="released")
            self.assertEqual(checker.check(s, j).kind, "violation", mutation)

    def test_missing_productivity_incomplete_drain_and_uncertain_request_never_pass(self):
        for mutation in ("no-bytes", "short-drain", "uncertain", "empty-reclaim", "no-terminal"):
            s, j = fixture()
            if mutation == "no-bytes":
                next(r for r in j.of_kind("client") if r.get("operation") == "read-prior")["result"] = "other"
            elif mutation == "short-drain":
                next(r for r in j.of_kind("client") if r.get("operation") == "release")["numbers"] = [1]
            elif mutation == "uncertain":
                next(r for r in j.of_kind("client") if r.get("operation") == "reclaim-1")["returncode"] = EXIT.UNCERTAIN
            elif mutation == "empty-reclaim":
                next(r for r in j.of_kind("environment") if r.get("phase") == "installed")["reclaimed"] = 0
            else:
                j.records = [r for r in j.records if r.get("event") != "response-terminal"]
            self.assertFalse(checker.check(s, j).green, mutation)

    def test_disabled_fault_suppressed_workload_killed_stage_and_budget(self):
        for mutation in (mutations.disable_fault_hook, mutations.suppress_workload, mutations.kill_stage):
            s, j = fixture()
            s, j = mutation(s, j)
            self.assertFalse(checker.check(s, j).green)
        s, j = fixture()
        self.assertEqual(checker.check(s, j, checker.Budget(max_records=2)).kind, "inconclusive")

    def test_duplicate_operation_and_forged_activation_are_harness_failure(self):
        s, j = fixture()
        j.records.append(copy.deepcopy(j.of_kind("client")[0]))
        self.assertEqual(checker.check(s, j).kind, "harness-failure")
        s, j = fixture()
        next(r for r in j.of_kind("environment") if r.get("event") == "fault-fired")["cid"] = 8
        self.assertEqual(checker.check(s, j).kind, "harness-failure")


if __name__ == "__main__":
    unittest.main()
