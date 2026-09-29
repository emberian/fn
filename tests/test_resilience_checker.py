"""The resilience framework's first increment (design-resilience-framework
-2026-09-29.md §2, §6, §7, §9): the IR round-trips and validates by name;
the whole-history checker narrows a lost reply by a read, a retry and a
listing; the two-group fracture is REFUSED (the tooth) while the
per-membership independent oracle accepts it; budget exhaustion is
`inconclusive`; refusing everything is `no-witness`; the seven
tester-of-testers mutations are each distinguished from the green control.
No image, no store: the journals are the tester's fabricated inputs."""
from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from tools.resilience import checker, contract, mutations
from tools.resilience.journal import Journal, TruncatedHistory
from tools.resilience.scenario import (Scenario, Operation, Fault, ScenarioError, validate,
                                       boundary_registry, executable_on_native)
from tools.resilience.adapters import native_cuts as adapter
from tests.campaign import native_cuts

REGISTRY = boundary_registry()


def two_group(boundary="log-written", witnesses=("post-accepted",)):
    """post-A to groups a and b, killed at BOUNDARY, then both groups listed."""
    return Scenario(
        id="fracture", title="atomic two-group post under a lost reply",
        contract="local-commit-log",
        initial={"recipe": "empty-store", "groups": ["a", "b"], "prior": []},
        actors=[{"name": "client", "kind": "client"}],
        operations=[Operation("post-A", "client", "post", {"groups": ["a", "b"], "payload": "A"}),
                    Operation("list-a", "client", "list-group", {"group": "a"}),
                    Operation("list-b", "client", "list-group", {"group": "b"})],
        faults=[Fault("post-A", boundary, "kill", "contract-admissible")],
        healing=["list-a", "list-b"], witnesses=list(witnesses))


def lost(scenario, boundary="log-written"):
    j = Journal(scenario.id)
    j.client("reply", operation="post-A", outcome="lost")
    j.environment("fault-fired", operation="post-A", boundary=boundary, action="kill",
                  evidence="returncode=-9")
    return j


class ScenarioIRTests(unittest.TestCase):
    def test_cut_scenarios_round_trip_and_validate(self):
        for s in adapter.scenarios():
            self.assertEqual(validate(s, REGISTRY), [])
            again = Scenario.from_json(s.to_json())
            self.assertEqual(again, s)
            self.assertTrue(executable_on_native(s, REGISTRY))

    def test_validation_names_each_problem(self):
        s = two_group(boundary="no-such-boundary", witnesses=())
        s.operations.append(Operation("retry-x", "client", "retry", {"of": "nothing"}))
        s.faults.append(Fault("post-A", "log-written", "kill", ""))
        problems = validate(s, REGISTRY)
        for expected in ("unregistered boundary no-such-boundary", "retry of nothing",
                         "at least one positive witness", "has no class"):
            self.assertTrue(any(expected in p for p in problems), (expected, problems))
        with self.assertRaises(ScenarioError):
            adapter.check_scenario(s, REGISTRY)

    def test_pending_schedule_points_are_registered_but_not_executable(self):
        s = two_group(boundary="page-read-outstanding")
        self.assertEqual(validate(s, REGISTRY), [])
        self.assertFalse(executable_on_native(s, REGISTRY))

    def test_registry_carries_the_verified_candidate_columns(self):
        for cut in native_cuts.POST_LOG_CUTS:
            self.assertEqual(REGISTRY[cut.name]["rule"],
                             native_cuts.POST_LOG_ONE_CANDIDATE[cut.name], cut.name)


class HistoryCheckerTests(unittest.TestCase):
    def test_lost_reply_leaves_two_histories_a_read_narrows_a_contrary_retry_violates(self):
        s = two_group(witnesses=("read-completed",))
        s.operations += [Operation("read-A", "client", "read", {"article": "post-A"}),
                         Operation("retry-A", "client", "retry", {"of": "post-A"})]
        j = lost(s)
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.surviving, 2, v)
        self.assertEqual(v.kind, "no-witness")      # nothing positive yet, never green
        j.client("read", operation="read-A", article="post-A", result="match")
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual((v.kind, v.surviving), ("consistent", 1))
        self.assertTrue(v.verify())
        j.client("reply", operation="retry-A", outcome="accepted")   # but it was served!
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation")
        self.assertEqual(v.explanation["record"]["operation"], "retry-A")
        self.assertEqual(v.explanation["last_non_empty"], [{"post-A": "committed"}])
        self.assertIn("duplicate-is-no-op", v.explanation["rules"])

    def test_fracture_two_groups_is_refused_by_the_whole_history(self):
        """THE TOOTH: one membership survived, the other did not.  Each
        listing passes on its own ("old or new"); no legal atomic acceptance
        explains both, so B is empty."""
        s = two_group()
        j = lost(s)
        j.client("list-group", operation="list-a", group="a", members=["post-A"])
        j.client("list-group", operation="list-b", group="b", members=[])
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation", v)
        self.assertEqual(v.explanation["record"]["group"], "b")
        self.assertEqual(v.explanation["last_non_empty"], [{"post-A": "committed"}])
        self.assertIn("atomic-memberships", v.pending_rules)     # the rule is cited as pending
        self.assertTrue(checker.independent_per_membership(s, j))   # what the old oracle accepts

    def test_both_memberships_or_neither_are_each_one_history(self):
        for members, fate in (( ["post-A"], "committed"), ([], "absent")):
            s = two_group(witnesses=("read-completed",))
            j = lost(s)
            j.client("list-group", operation="list-a", group="a", members=members)
            j.client("list-group", operation="list-b", group="b", members=members)
            v = checker.check(s, j, registry=REGISTRY)
            self.assertEqual(v.surviving, 1, (members, v))
            self.assertNotEqual(v.kind, "violation")

    def test_boundary_rule_refuses_the_fate_the_cut_table_excludes(self):
        s = two_group(boundary="finish-durable")            # column: present
        s.operations.append(Operation("read-A", "client", "read", {"article": "post-A"}))
        j = lost(s, boundary="finish-durable")
        j.client("read", operation="read-A", article="post-A", result="absent")
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation")
        self.assertEqual(v.explanation["rules"], ["absent-until-committed"])   # the read emptied B
        self.assertIn("boundary-fate", v.explanation["rules_used"])            # after the column narrowed it
        self.assertEqual(v.explanation["last_non_empty"], [{"post-A": "committed"}])

    def test_persisted_count_from_the_image_narrows(self):
        s = two_group()
        j = lost(s)
        j.environment("persisted-records", count=1, source="log scan-store")
        j.client("list-group", operation="list-a", group="a", members=[])
        j.client("list-group", operation="list-b", group="b", members=[])
        self.assertEqual(checker.check(s, j, registry=REGISTRY).kind, "violation")

    def test_other_bytes_is_a_violation(self):
        s = two_group()
        s.operations.append(Operation("read-A", "client", "read", {"article": "post-A"}))
        j = lost(s)
        j.client("read", operation="read-A", article="post-A", result="other")
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation")
        self.assertEqual(v.explanation["rules"], ["committed-serves-exact"])

    def test_budget_exhaustion_is_inconclusive_never_consistent(self):
        s = two_group()
        s.operations = [Operation("post-%d" % i, "client", "post", {"groups": ["a"]})
                        for i in range(13)] + s.operations[1:]
        s.faults = []
        j = Journal(s.id)
        for i in range(13):
            j.client("reply", operation="post-%d" % i, outcome="lost")
        v = checker.check(s, j, checker.Budget(max_histories=4096), REGISTRY)
        self.assertEqual((v.kind, v.cause), ("inconclusive", "budget:histories"))
        self.assertFalse(v.green)
        self.assertIsNone(v.surviving)

    def test_refusing_everything_is_no_witness(self):
        s = two_group()
        s.faults = []
        j = Journal(s.id)
        j.client("reply", operation="post-A", outcome="refused")
        j.client("list-group", operation="list-a", group="a", members=[])
        j.client("list-group", operation="list-b", group="b", members=[])
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual((v.kind, v.cause, v.surviving), ("no-witness", "missing:post-accepted", 1))
        self.assertFalse(v.green)

    def test_internal_durable_claim_never_narrows_but_is_listed(self):
        s = two_group(witnesses=("read-completed",))
        s.operations.append(Operation("read-A", "client", "read", {"article": "post-A"}))
        j = lost(s)
        j.internal("claim", operation="post-A", claim="durable")   # a log line, not an ack
        j.client("read", operation="read-A", article="post-A", result="absent")
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "no-witness")    # consistent history, no positive witness
        self.assertEqual(v.surviving, 1)
        self.assertEqual(len(v.diagnostics), 1)

    def test_pending_rules_are_reported_only_when_used(self):
        s = two_group(witnesses=("read-completed",))
        s.operations = [s.operations[0], Operation("read-A", "client", "read", {"article": "post-A"})]
        j = lost(s)
        j.client("read", operation="read-A", article="post-A", result="match")
        self.assertEqual(checker.check(s, j, registry=REGISTRY).pending_rules, [])


class TestTheTestersTests(unittest.TestCase):
    def setUp(self):
        self.scenario = adapter.scenario_for(native_cuts.POST_LOG_CUTS[3])   # log-written
        self.journal = mutations.fabricated_green_run(self.scenario, fate="absent")

    def test_the_control_is_green(self):
        v = checker.check(self.scenario, self.journal, registry=REGISTRY)
        self.assertTrue(v.green, v)
        self.assertEqual(sorted(v.witnesses_observed),
                         ["post-accepted", "read-completed", "retry-reconciled"])
        self.assertEqual(v.pending_rules, [])
        self.assertTrue(v.verify())
        for fate in ("committed", "absent"):
            j = mutations.fabricated_green_run(self.scenario, fate=fate)
            self.assertTrue(checker.check(self.scenario, j, registry=REGISTRY).green, fate)

    def test_each_journal_mutation_is_distinguished(self):
        kinds = set()
        for name, mutate in mutations.MUTATIONS.items():
            s, j = mutate(self.scenario, self.journal)
            v = checker.check(s, j, registry=REGISTRY)
            kind, cause = mutations.EXPECTED[name]
            self.assertEqual(v.kind, kind, (name, v))
            self.assertTrue((v.cause or "").startswith(cause), (name, v.cause))
            self.assertFalse(v.green, name)
            kinds.add((v.kind, (v.cause or "").split(":")[0] + ":" + (v.cause or "").split(":")[1]
                       if ":" in (v.cause or "") else v.kind))
        self.assertEqual(len(kinds), len(mutations.MUTATIONS))   # pairwise distinct

    def test_truncated_history_is_refused_by_the_reader(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = self.journal.write(Path(tmp) / "journal.jsonl")
            self.assertEqual(Journal.read(path).digest(), self.journal.digest())
            mutations.truncate_history(path)
            with self.assertRaises(TruncatedHistory):
                Journal.read(path)

    def test_corrupted_verdict_fails_its_own_check(self):
        s, j = mutations.omit_witness(self.scenario, self.journal)
        v = checker.check(s, j, registry=REGISTRY)
        self.assertFalse(v.green)
        forged = mutations.corrupt_checker_result(v)
        self.assertTrue(forged.green)          # what a reader would believe
        self.assertFalse(forged.verify())      # and why it must not
        self.assertTrue(v.verify())
        self.assertEqual(checker.Verdict.from_json(v.to_json()), v)


class ContractRuleTests(unittest.TestCase):
    def test_every_rule_names_its_source(self):
        for r in contract.RULES.values():
            self.assertIn(r.status, ("registered", "verified-table", "pending"))
            if r.status == "registered":
                self.assertTrue(r.theorem and r.book, r.name)
            if r.status == "pending":
                self.assertIsNone(r.theorem, r.name)

    def test_registered_theorems_exist_in_their_books(self):
        root = Path(__file__).resolve().parent.parent
        for r in contract.RULES.values():
            if r.status == "registered":
                text = (root / r.book).read_text(encoding="utf-8")
                self.assertIn("(defthm {}".format(r.theorem), text, r.name)


if __name__ == "__main__":
    unittest.main()
