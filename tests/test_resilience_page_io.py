"""Issued-I/O observer and tester mutations; these are not native evidence."""
import copy
import unittest

from tools.resilience import checker, mutations
from tools.resilience.adapters import page_io
from tools.resilience.journal import Journal

OLD = [0, 7, 1, 64, 200, 987654321]
NEW = [1, 8, 2, 64, 180, 123456789]


def fixture():
    s = page_io.example()
    j = Journal(s.id)
    j.stage("workload", "begun")
    j.client("io-request", operation="read-prior", status="403 article temporarily unavailable")
    j.client("io-cancel", operation="cancel", token=OLD)
    j.client("io-retire", operation="retire", returncode=0, installed=True)
    j.environment("fault-fired", operation="read-prior", boundary="page-read-outstanding",
                  action="interleave", stage="issued", token=OLD)
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    j.client("io-release", operation="deliver", token=OLD)
    j.client("read", operation="read-retained", article="n0", result="match")
    for row in [dict(phase="held", token=OLD, file=1), dict(phase="cancelled", token=OLD),
                dict(phase="close-held", file=1), dict(phase="settled", token=OLD, answer=":CANCELLED"),
                dict(phase="closed", file=1), dict(phase="settled", token=NEW, answer=":PUBLISH")]:
        j.environment("page-io", **row)
    j.environment("io-terminal", token=OLD)
    j.stage("healing", "ended", elapsed=1.0)
    return s, j


class PageIOObserverTests(unittest.TestCase):
    def test_bounded_token_parser_accepts_wrapping_without_reader(self):
        log = (b"PAGE-IO held token=(0 7 1 64\n 200 987654321) file=1\n"
               b"PAGE-IO cancelled token=(0 7 1 64 200 987654321)\n"
               b"PAGE-IO close-held file=1\n"
               b"PAGE-IO settled token=(0 7 1 64 200 987654321) answer=:CANCELLED\n"
               b"PAGE-IO closed file=1\nPAGE-IO duplicate answer=:STALE\n")
        rows = page_io.events(log)
        self.assertEqual([r["phase"] for r in rows],
                         ["held", "cancelled", "close-held", "settled", "closed", "duplicate"])
        self.assertEqual(rows[0]["token"], OLD)
        self.assertEqual(page_io.events(b"PAGE-IO held token=(#.(evil) 7 1 64 200 9) file=1"), [])

    def test_productive_cancelled_token_and_distinct_retained_read(self):
        s, j = fixture()
        v = checker.check(s, j)
        self.assertTrue(v.green, v.to_json())
        self.assertIn("page-io-native-composition", v.pending_rules)
        self.assertIn("worker thread death unclaimed", v.diagnostics[0])

    def test_disabled_fault_suppressed_workload_and_killed_stage(self):
        for mutation in (mutations.disable_fault_hook, mutations.suppress_workload, mutations.kill_stage):
            s, j = fixture()
            s, j = mutation(s, j)
            self.assertFalse(checker.check(s, j).green)

    def test_cancelled_publication_wrong_identity_and_premature_close_refute(self):
        for mutation in ("publish-old", "swap-token", "early-close", "duplicate-settlement"):
            s, j = fixture()
            rows = [r for r in j.of_kind("environment") if r.get("event") == "page-io"]
            if mutation == "publish-old":
                rows[3]["answer"] = ":PUBLISH"
            elif mutation == "swap-token":
                rows[3]["token"] = NEW
            elif mutation == "early-close":
                rows[2].update(phase="closed")
            else:
                rows[4].update(phase="settled", token=OLD, answer=":CANCELLED")
            self.assertEqual(checker.check(s, j).kind, "violation", mutation)

    def test_no_productivity_terminal_missing_and_duplicate_operation_never_green(self):
        for mutation in ("no-publish", "wrong-bytes", "no-terminal", "duplicate-operation"):
            s, j = fixture()
            if mutation == "no-publish":
                j.records = [r for r in j.records if r.get("token") != NEW]
            elif mutation == "wrong-bytes":
                next(r for r in j.of_kind("client") if r.get("event") == "read")["result"] = "other"
            elif mutation == "no-terminal":
                j.records = [r for r in j.records if r.get("event") != "io-terminal"]
            else:
                j.records.append(copy.deepcopy(j.of_kind("client")[0]))
            self.assertFalse(checker.check(s, j).green, mutation)

    def test_activation_is_correlated_and_budgets_do_not_pass(self):
        s, j = fixture()
        next(r for r in j.of_kind("environment") if r.get("event") == "fault-fired")["token"] = NEW
        self.assertEqual(checker.check(s, j).kind, "harness-failure")
        s, j = fixture()
        self.assertEqual(checker.check(s, j, checker.Budget(max_records=2)).kind, "inconclusive")


if __name__ == "__main__":
    unittest.main()
