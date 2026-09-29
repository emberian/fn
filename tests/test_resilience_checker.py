"""The resilience framework's first increment (design-resilience-framework
-2026-09-29.md §2, §6, §7, §9): the IR round-trips and validates by name;
the whole-history checker narrows a lost reply by a read, a retry and a
listing; the two-group fracture is REFUSED (the tooth) while the
per-membership independent oracle accepts it; budget exhaustion is
`inconclusive`; refusing everything is `no-witness`; the nine
tester-of-testers mutations are each distinguished from the green control.
The second increment (W7c, §5, §7): a killed recovery that changed the
history, a checkpoint the cut's column excludes and a served-route fate the
served column excludes are each a violation citing its rule; a healing
phase past its bound is `healing-overran` (an experimental budget's overrun
a diagnostic); the six schedule points generate scenarios, the pending ones
named with their owners.  No image, no store: the journals are the tester's
fabricated inputs."""
from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from tools.resilience import checker, contract, mutations, schedule_points
from tools.resilience.journal import Journal, TruncatedHistory
from tools.resilience.scenario import (Scenario, Operation, Fault, ScenarioError, validate,
                                       boundary_registry, executable_on_native,
                                       pending_reasons, reclaim_cut_names, PENDING_BOUNDARIES)
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
        for name, row in PENDING_BOUNDARIES.items():
            self.assertFalse(REGISTRY[name]["executable"], name)
            self.assertEqual(REGISTRY[name]["owner"], row["owner"])
        for s in schedule_points.scenarios():
            if any(f.boundary in PENDING_BOUNDARIES for f in s.faults):
                self.assertEqual(validate(s, REGISTRY), [], s.id)
                self.assertFalse(executable_on_native(s, REGISTRY), s.id)
                self.assertTrue(pending_reasons(s, REGISTRY), s.id)
        # A post does not reach a reader's boundary: the category error is named.
        s = two_group(boundary="page-read-outstanding")
        self.assertTrue(any("does not reach this boundary" in p for p in validate(s, REGISTRY)))

    def test_a_fault_at_a_boundary_its_operation_never_reaches_is_refused(self):
        s = adapter.scenario_for(native_cuts.POST_LOG_CUTS[3])
        s.faults.append(Fault("recover", "log-written", "kill", "contract-admissible"))
        problems = validate(s, REGISTRY)
        self.assertTrue(any("recover@log-written" in p and "does not reach" in p
                            for p in problems), problems)
        s = adapter.scenario_for(native_cuts.POST_LOG_CUTS[3])
        s.healing_bound = {"kind": "minutes", "value": 0, "source": ""}
        problems = validate(s, REGISTRY)
        for expected in ("bound of no kind", "positive value", "names its source"):
            self.assertTrue(any(expected in p for p in problems), (expected, problems))

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
                         ["post-accepted", "read-completed", "recovery-completed",
                          "retry-reconciled"])
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
            kinds.add((v.kind, v.cause))
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


def W(scenario):
    j = Journal(scenario.id)
    j.stage("workload", "begun")
    return j


def heal(j, elapsed=0.5):
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    return lambda: j.stage("healing", "ended", elapsed=elapsed)


class RecoveryAndCheckpointCheckerTests(unittest.TestCase):
    def test_a_killed_recovery_that_changed_the_history_is_a_violation(self):
        s = adapter.recovery_scenario_for(adapter.recovery_cuts()[0])   # recover-replayed
        j = W(s)
        j.client("reply", operation="post-prior", outcome="accepted", route="store-post")
        j.client("reply", operation="post-candidate", outcome="lost", route="store-post")
        j.environment("fault-fired", operation="post-candidate", boundary="log-written",
                      action="kill", route="store-post", evidence="returncode=-9")
        j.environment("persisted-records", count=2, phase="at-cut", source="log scan-store")
        j.client("recover", operation="recover-killed", outcome="lost", phase="fault")
        j.environment("fault-fired", operation="recover-killed", boundary="recover-replayed",
                      action="kill", route="store-post", evidence="returncode=-9")
        j.environment("persisted-records", count=1, phase="after-killed-recovery",
                      source="log scan-store")
        end = heal(j)
        end()
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation", v.to_json())
        self.assertEqual(v.explanation["record"]["phase"], "after-killed-recovery")
        self.assertIn("recovery-keeps-history", v.explanation["rules"])

    def test_a_kept_history_and_a_completed_second_recovery_are_consistent(self):
        s = adapter.recovery_scenario_for(adapter.recovery_cuts()[0])
        j = W(s)
        j.client("reply", operation="post-prior", outcome="accepted", route="store-post")
        j.client("reply", operation="post-candidate", outcome="lost", route="store-post")
        j.environment("fault-fired", operation="post-candidate", boundary="log-written",
                      action="kill", route="store-post", evidence="returncode=-9")
        j.environment("persisted-records", count=2, phase="at-cut", source="log scan-store")
        j.client("recover", operation="recover-killed", outcome="lost", phase="fault")
        j.environment("fault-fired", operation="recover-killed", boundary="recover-replayed",
                      action="kill", route="store-post", evidence="returncode=-9")
        j.environment("persisted-records", count=2, phase="after-killed-recovery",
                      source="log scan-store")
        end = heal(j)
        j.client("recover", operation="recover", outcome="completed", phase="healing")
        j.environment("persisted-records", count=2, phase="after-recovery",
                      source="log scan-store")
        j.client("read", operation="read-prior", article="post-prior", result="match")
        j.client("read", operation="read-candidate", article="post-candidate", result="match")
        j.client("reply", operation="retry-candidate", outcome="duplicate", route="store-post")
        j.environment("persisted-records", count=2, phase="final", source="log scan-store")
        end()
        v = checker.check(s, j, registry=REGISTRY)
        self.assertTrue(v.green, v.to_json())
        self.assertEqual(v.surviving, 1)
        self.assertIn("recovery-completed", v.witnesses_observed)
        # The healing recovery failing is the history not kept, by rule.
        j.records[[r["seq"] for r in j.records if r.get("operation") == "recover"][0]]["outcome"] = "failed"
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation")
        self.assertEqual(v.explanation["rules"], ["recovery-keeps-history"])

    def checkpoint_journal(self, s, which, final_open="open=checkpoint:5 suffix=0"):
        j = W(s)
        for p in adapter.CHECKPOINT_POSTS[:3]:
            j.client("reply", operation=p, outcome="accepted", route="store-post")
        j.client("checkpoint", operation="checkpoint-1", outcome="completed")
        for p in adapter.CHECKPOINT_POSTS[3:]:
            j.client("reply", operation=p, outcome="accepted", route="store-post")
        j.client("checkpoint", operation="checkpoint-killed", outcome="lost")
        j.environment("fault-fired", operation="checkpoint-killed", boundary=s.faults[0].boundary,
                      action="kill", route="store-post", evidence="returncode=-9")
        j.client("status", operation="status-after",
                 open="open=checkpoint:{} suffix={}".format(3 if which == "old" else 5,
                                                           2 if which == "old" else 0))
        j.environment("checkpoint-installed", boundary=s.faults[0].boundary, which=which,
                      source="store status")
        end = heal(j)
        j.client("recover", operation="recover", outcome="completed", phase="healing")
        for p in adapter.CHECKPOINT_POSTS:
            j.client("read", operation="read-" + p, article=p, result="match")
        j.client("reply", operation="retry-5", outcome="duplicate", route="store-post")
        j.client("checkpoint", operation="checkpoint-2", outcome="completed")
        j.client("status", operation="status-final", open=final_open)
        end()
        return j

    def test_the_checkpoint_the_cut_excludes_is_a_violation_and_the_allowed_one_is_not(self):
        staged = native_cuts.STATE_CHECKPOINT_CUTS[2]        # staged-durable: old
        durable = native_cuts.STATE_CHECKPOINT_CUTS[4]       # durable: new
        replaced = native_cuts.STATE_CHECKPOINT_CUTS[3]      # replaced: either
        for cut, which, expect in ((staged, "new", "violation"), (staged, "old", "consistent"),
                                   (durable, "old", "violation"), (durable, "new", "consistent"),
                                   (replaced, "old", "consistent"),
                                   (replaced, "new", "consistent")):
            s = adapter.checkpoint_scenario_for(cut)
            v = checker.check(s, self.checkpoint_journal(s, which), registry=REGISTRY)
            self.assertEqual(v.kind, expect, (cut.name, which, v.to_json()))
            if expect == "violation":
                self.assertEqual(v.explanation["rules"], ["checkpoint-old-or-new"])
            else:
                self.assertTrue(v.green, (cut.name, which))
                self.assertIn("checkpoint-installed", v.witnesses_observed)

    def test_the_served_column_judges_a_served_route_fault(self):
        # finish-consumed: absent on the served route, present for a batch of one.
        cut = native_cuts.POST_LOG_CUTS[1]
        self.assertEqual((REGISTRY[cut.name]["rules"]["served-post"],
                          REGISTRY[cut.name]["rules"]["store-post"]), ("absent", "present"))
        s = adapter.served_scenario_for(cut)
        for route, expect in (("served-post", "violation"), ("store-post", "consistent")):
            j = W(s)
            j.client("reply", operation="post-prior", outcome="accepted", route="served-post")
            j.client("reply", operation="post-candidate", outcome="lost", route="served-post")
            j.environment("fault-fired", operation="post-candidate", boundary=cut.name,
                          action="kill", route=route, evidence="owner rc=-9")
            j.environment("persisted-records", count=2, phase="at-cut", source="log scan-store")
            end = heal(j)
            end()
            v = checker.check(s, j, registry=REGISTRY)
            self.assertEqual(v.kind if v.kind == "violation" else "consistent", expect,
                             (route, v.to_json()))
            if expect == "violation":
                # The served column left only the absent fate; the image's
                # scan of two records then emptied B.
                self.assertIn("boundary-fate", v.explanation["rules_used"])
                self.assertEqual(v.explanation["record"]["event"], "persisted-records")

    def test_healing_past_its_bound_is_a_verdict_and_an_experimental_overrun_a_diagnostic(self):
        s = adapter.scenario_for(native_cuts.POST_LOG_CUTS[3])
        j = mutations.fabricated_green_run(s, fate="absent")     # elapsed 0.5
        s.healing_bound = {"kind": "seconds", "value": 0.1, "source": "test"}
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual((v.kind, v.green), ("healing-overran", False))
        self.assertTrue(v.cause.startswith("healing:0.5s>0.1s"), v.cause)
        self.assertEqual(v.healing["elapsed"], 0.5)
        s.healing_bound = {"kind": "experimental", "value": 0.1, "source": "test"}
        v = checker.check(s, j, registry=REGISTRY)
        self.assertTrue(v.green, v.to_json())
        self.assertTrue(any("experimental healing budget exceeded" in d for d in v.diagnostics))
        s.healing_bound = {"kind": "seconds", "value": 60, "source": "test"}
        self.assertTrue(checker.check(s, j, registry=REGISTRY).green)

    def test_offline_membership_variant_lists_both_groups(self):
        s = adapter.scenario_for(native_cuts.POST_LOG_CUTS[3], memberships=True)
        self.assertEqual(validate(s, REGISTRY), [])
        self.assertEqual([o.args["group"] for o in s.operations if o.op == "list-group"],
                         [adapter.GROUP, adapter.GROUP2])
        self.assertIn("memberships-listed", s.witnesses)
        for fate in ("committed", "absent"):
            v = checker.check(s, mutations.fabricated_green_run(s, fate=fate), registry=REGISTRY)
            self.assertTrue(v.green, (fate, v.to_json()))


class SchedulePointTests(unittest.TestCase):
    def test_the_six_rows_generate_scenarios_and_name_the_pending_ones(self):
        self.assertEqual([r.point for r in schedule_points.ROWS],
                         ["publication-durable-reply-pending", "page-read-outstanding",
                          "reclaim-candidate-selected", "new-checkpoint-prepared",
                          "recovery-repair-write", "receipt-observed"])
        rows = schedule_points.status(REGISTRY)
        self.assertTrue(all(r["valid"] for r in rows), [r for r in rows if not r["valid"]])
        self.assertEqual({r["scenario"] for r in rows if r["status"] == "executable"},
                         {"native-served-log-fenced",
                          "native-checkpoint-state-checkpoint-staged-durable",
                          "native-checkpoint-state-checkpoint-replaced",
                          "native-checkpoint-state-checkpoint-durable",
                          "native-recovery-log-truncated", "native-recovery-log-recovered",
                          "native-recovery-recovery-stage-unlinked"})
        pending = {r["scenario"]: r for r in rows if r["status"] == "pending"}
        self.assertEqual(set(pending), {"schedule-page-read-outstanding",
                                        "schedule-reclaim-candidate-selected",
                                        "schedule-receipt-observed-duplicate",
                                        "schedule-receipt-observed-reorder",
                                        "schedule-receipt-observed-lose-completion"})
        self.assertEqual(pending["schedule-page-read-outstanding"]["owner"], "online-reclaim-8")
        self.assertEqual(pending["schedule-reclaim-candidate-selected"]["owner"],
                         "online-reclaim-8")
        self.assertEqual(pending["schedule-receipt-observed-duplicate"]["owner"], "bp-remainder-3")
        for r in pending.values():
            self.assertTrue(r["reasons"] and r["expected"] == "consistent", r)
        self.assertTrue(all(r["expected"] == "consistent" for r in rows))

    def test_the_reclaim_pass_cuts_are_registered_from_the_host_in_kill_form(self):
        names = reclaim_cut_names()
        if not names:
            self.skipTest("no +fnn-reclaim-cuts+ in this tree")
        self.assertEqual(names[:1] + names[-1:], ["captured", "released"])
        self.assertEqual(REGISTRY["reclaim-captured"]["rule"], "old")
        self.assertEqual(REGISTRY["reclaim-installed"]["rule"], "new")
        self.assertEqual(REGISTRY["reclaim-candidate-selected"]["kill_form"], "reclaim-captured")
        self.assertIn(REGISTRY["reclaim-candidate-selected"]["kill_form"], REGISTRY)

    def test_every_family_scenario_validates_and_is_executable(self):
        counts = {}
        for name in adapter.FAMILIES:
            ss = adapter.family_scenarios(name)
            counts[name] = len(ss)
            for s in ss:
                self.assertEqual(validate(s, REGISTRY), [], s.id)
                self.assertTrue(executable_on_native(s, REGISTRY), s.id)
                self.assertEqual(Scenario.from_json(s.to_json()), s)
        self.assertEqual(counts, {"post": 5, "recovery": 7, "served": 5,
                                  "served-recovery": 3, "checkpoint": 5})


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
