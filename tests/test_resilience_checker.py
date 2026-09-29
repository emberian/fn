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

import collections
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
        """A design §5 point is executable exactly when its held form is in
        this tree AND its runner exists (receipt-observed: bp_node.py);
        the others stay pending, named with their owners."""
        for name, row in PENDING_BOUNDARIES.items():
            entry = REGISTRY[name]
            self.assertEqual(entry["executable"],
                             entry["held_in_tree"] and entry["runner_in_tree"], name)
            self.assertEqual(entry["owner"], row["owner"])
            if entry["executable"]:
                self.assertEqual(entry["actions"], list(row["actions"]), name)
            else:
                self.assertEqual(entry["actions"], [], name)
        self.assertTrue(REGISTRY["receipt-observed"]["executable"])
        self.assertFalse(REGISTRY["page-read-outstanding"]["executable"])
        for s in schedule_points.scenarios():
            if any(f.boundary in PENDING_BOUNDARIES for f in s.faults):
                self.assertEqual(validate(s, REGISTRY), [], s.id)
                pending = {f.boundary for f in s.faults if not REGISTRY[f.boundary]["executable"]}
                self.assertEqual(executable_on_native(s, REGISTRY), not pending, s.id)
                self.assertEqual(bool(pending_reasons(s, REGISTRY)), bool(pending), s.id)
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
                          "native-recovery-recovery-stage-unlinked",
                          "schedule-receipt-observed-duplicate",
                          "schedule-receipt-observed-reorder",
                          "schedule-receipt-observed-lose-completion"})
        pending = {r["scenario"]: r for r in rows if r["status"] == "pending"}
        self.assertEqual(set(pending), {"schedule-page-read-outstanding",
                                        "schedule-reclaim-candidate-selected"})
        self.assertEqual(pending["schedule-page-read-outstanding"]["owner"], "online-reclaim-8")
        self.assertEqual(pending["schedule-reclaim-candidate-selected"]["owner"],
                         "online-reclaim-8")
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
                                  "served-recovery": 3, "checkpoint": 5, "cross-route": 1})


def receipt_journal(variant, *, first="accepted", dup="accepted", articles=1, present=True,
                    pinned="no", held_forward="no-route", replay="completed"):
    """The bp-node runner's journal for VARIANT, as the box would write it
    (tools/resilience/adapters/bp_node.py), with the knobs a tooth turns."""
    s = next(x for x in schedule_points.scenarios()
             if x.id == "schedule-receipt-observed-" + variant)
    f = s.faults[0]
    j = Journal(s.id)
    j.stage("workload", "begun")
    j.environment("fault-fired", operation="receipt-1", boundary=f.boundary, action=f.action,
                  route=f.route, evidence="BP APP RECEIPT-OBSERVED HOLD release=/x")
    if variant == "reorder":
        j.client("policy-change", operation="policy", what="receipt-policy",
                 change="route-removed", route_present=False, returncode=0)
    j.client("reply", operation="receipt-1", outcome=first, route="bp-transit",
             returncode=0 if first == "accepted" else 8)
    if variant == "duplicate":
        j.client("reply", operation="receipt-dup", outcome=dup, route="bp-transit",
                 returncode=0, duplicate_of="receipt-1")
    j.internal("claim", claim="durable", operation="receipt-1", disposition="accepted",
               source="receiver")
    done = heal(j)
    if variant == "reorder":
        j.client("restart", operation="dispatch-held", outcome="completed", returncode=0,
                 forward=held_forward, route_present=False)
        j.client("policy-change", operation="restore", what="receipt-policy",
                 change="route-restored", route_present=True, returncode=0)
        j.client("restart", operation="dispatch", outcome="completed", returncode=0,
                 forward="sent", route_present=True)
    elif variant == "duplicate":
        j.client("restart", operation="dispatch", outcome="completed", returncode=0,
                 forward="none", route_present=True)
    else:
        j.client("restart", operation="replay", outcome=replay, returncode=0, forward="sent",
                 route_present=True)
    j.client("status", operation="deliver", receipt="accepted" if pinned == "no" else "absent",
             pinned=pinned, returncode=0)
    j.client("probe", operation="probe", identity="bundle-1", articles=articles,
             present=present, bytes="relayed" if present else "absent")
    done()
    return s, j


class ReceiptPointTests(unittest.TestCase):
    """The receipt-observed point's rules have teeth: the three variants'
    journals are consistent with one surviving history and both witnesses;
    a second article, a release without a committed carrier, and a receipt
    sent without its route are each a violation citing its rule; a lost
    completion leaves two fates until the probe narrows them."""

    def test_each_variant_is_consistent_with_one_history_and_both_witnesses(self):
        for variant in ("duplicate", "reorder", "lose-completion"):
            s, j = receipt_journal(variant, first="lost" if variant == "lose-completion"
                                   else "accepted")
            v = checker.check(s, j, registry=REGISTRY)
            self.assertEqual(v.kind, "consistent", (variant, v.to_json()))
            self.assertTrue(v.green, variant)
            self.assertEqual(v.surviving, 1, variant)
            self.assertEqual(v.witnesses_observed, ["receipt-delivered", "receipt-effect-once"])
            self.assertEqual(v.diagnostics, [], variant)

    def test_a_duplicate_carrier_that_stored_a_second_article_is_a_violation(self):
        s, j = receipt_journal("duplicate", articles=2)
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation")
        self.assertEqual(v.explanation["record"]["event"], "probe")
        self.assertIn("receipt-once", v.explanation["rules"])

    def test_a_lost_completion_leaves_two_fates_until_the_probe(self):
        s, j = receipt_journal("lose-completion", first="lost")
        hist = contract.histories(s, 64)
        self.assertEqual(len(hist), 2)
        kept = [h for h in hist
                if contract.narrow(s, h, j.of_kind("client")[0], j, REGISTRY)[0]]
        self.assertEqual(len(kept), 2, "a lost transfer narrows nothing")
        s, j = receipt_journal("lose-completion", first="lost", present=False, articles=0,
                               pinned="yes")
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "no-witness", v.to_json())
        self.assertEqual(v.surviving, 1)

    def test_a_release_without_a_committed_carrier_is_a_violation(self):
        s, j = receipt_journal("lose-completion", first="lost", present=False, articles=0,
                               pinned="no")
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation", v.to_json())
        self.assertEqual(v.explanation["record"]["event"], "probe")
        self.assertIn("receipt-once", v.explanation["rules"])

    def test_a_receipt_sent_without_its_route_is_a_violation_citing_policy_order(self):
        s, j = receipt_journal("reorder", held_forward="sent")
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation", v.to_json())
        self.assertEqual(v.explanation["record"]["operation"], "dispatch-held")
        self.assertEqual(v.explanation["rules"], ["receipt-policy-order"])
        self.assertIn("receipt-policy-order", v.pending_rules)

    def test_the_receipt_scenarios_are_bp_node_recipes_the_adapter_dispatches(self):
        for s in schedule_points.scenarios():
            if s.id.startswith("schedule-receipt-observed-"):
                self.assertEqual(s.initial["recipe"], "bp-node")
                self.assertEqual(validate(s, REGISTRY), [], s.id)
                self.assertTrue(executable_on_native(s, REGISTRY), s.id)
                self.assertEqual(s.witnesses, ["receipt-delivered", "receipt-effect-once"])


def cross_route_journal(outcome="refused", status="441 posting failed; a different article "
                        "with this Message-ID is stored here", xref=None, count_after=1):
    """The cross-route scenario's journal as the box writes it, with the
    knobs a tooth turns: the retry's outcome and line, the served Xref of
    the reads (None: the LISTGROUP number in the one group), the final
    record count."""
    s = adapter.cross_route_retry_scenario()
    j = Journal(s.id)
    j.bind(adapter.PRIOR, adapter.mid(adapter.PRIOR))
    j.stage("workload", "begun")
    j.client("reply", operation=adapter.PRIOR, outcome="accepted", route="store-post", returncode=0)
    j.environment("persisted-records", count=1, last="x", phase="at-cut", source="log scan-store")
    done = heal(j)
    j.client("recover", operation="recover", outcome="completed", phase="healing", returncode=0)
    j.environment("persisted-records", count=1, last="x", phase="after-recovery",
                  source="log scan-store")
    j.client("list-group", operation="list-letters", group=adapter.GROUP,
             members=[adapter.PRIOR], numbers=[1], route="served")
    served_xref = xref or {"server": "node.invalid", "locations": {adapter.GROUP: 1},
                           "malformed": False}
    j.client("read", operation="read-before", article=adapter.PRIOR, result="match",
             route="served", status="220 1 <x>", xref=served_xref)
    j.client("reply", operation="retry-served", outcome=outcome, route="served-post",
             status=status, cross_route=True)
    j.client("read", operation="read-after", article=adapter.PRIOR, result="match",
             route="served", status="220 1 <x>", xref=served_xref)
    j.client("list-group", operation="list-after", group=adapter.GROUP,
             members=[adapter.PRIOR], numbers=[1], route="served")
    j.environment("persisted-records", count=count_after, last="x", phase="final",
                  source="log scan-store")
    done()
    return s, j


class XrefAndCrossRouteTests(unittest.TestCase):
    """The two findings as scenarios with teeth (brief item 2)."""

    def test_served_split_takes_exactly_one_leading_xref(self):
        stored = b"Path: a!b\r\nMessage-ID: <x>\r\n\r\nbody\r\n"
        xref, rest = adapter.served_split(b"Xref: node.invalid fn.letters:3 fn.replies:7\r\n"
                                          + stored)
        self.assertEqual(rest, stored)
        self.assertEqual(xref, {"server": "node.invalid", "malformed": False,
                                "locations": {"fn.letters": 3, "fn.replies": 7}})
        self.assertEqual(adapter.served_split(stored), (None, stored))
        two = b"Xref: n a:1\r\nXref: n a:1\r\n" + stored
        xref, rest = adapter.served_split(two)
        self.assertTrue(rest.startswith(b"Xref:"), "a second Xref stays in the stored bytes")
        self.assertFalse(adapter.served_matches(two, stored))
        self.assertTrue(adapter.served_split(b"Xref: n\r\n" + stored)[0]["malformed"])
        self.assertTrue(adapter.served_split(b"Xref: n a:x\r\n" + stored)[0]["malformed"])

    def test_the_cross_route_journal_is_consistent_with_its_witness(self):
        s, j = cross_route_journal()
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "consistent", v.to_json())
        self.assertTrue(v.green)
        self.assertEqual(v.surviving, 1)
        self.assertIn("cross-route-retry-refused", v.witnesses_observed)
        self.assertEqual(v.pending_rules, ["atomic-memberships", "identity-is-the-bytes"])

    def test_a_cross_route_retry_answered_duplicate_or_accepted_is_a_violation(self):
        for outcome, status in (("duplicate", "441 posting failed; this article is already "
                                              "stored here"),
                                ("accepted", "240 article received"),
                                ("refused", "441 posting failed; the store refused the "
                                            "article as malformed")):
            s, j = cross_route_journal(outcome=outcome, status=status)
            v = checker.check(s, j, registry=REGISTRY)
            self.assertEqual(v.kind, "violation", (outcome, v.to_json()))
            self.assertEqual(v.explanation["record"]["operation"], "retry-served")
            self.assertEqual(v.explanation["rules"], ["identity-is-the-bytes"])

    def test_a_store_changed_by_the_refused_retry_is_a_violation(self):
        s, j = cross_route_journal(count_after=2)
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "violation", v.to_json())
        self.assertEqual(v.explanation["record"]["phase"], "final")

    def test_an_xref_naming_other_locations_than_listgroup_is_a_violation(self):
        for bad in ({"server": "n", "locations": {adapter.GROUP: 2}, "malformed": False},
                    {"server": "n", "locations": {adapter.GROUP: 1, "other": 1},
                     "malformed": False},
                    {"server": "n", "locations": {}, "malformed": True}):
            s, j = cross_route_journal(xref=bad)
            v = checker.check(s, j, registry=REGISTRY)
            self.assertEqual(v.kind, "violation", (bad, v.to_json()))
            self.assertEqual(v.explanation["record"]["operation"], "read-before")
            self.assertEqual(v.explanation["rules"], ["xref-locations-exact"])

    def test_a_read_without_an_xref_is_judged_as_before(self):
        s, j = cross_route_journal()
        for r in j.records:
            if r.get("event") == "read":
                r["xref"] = None
        v = checker.check(s, j, registry=REGISTRY)
        self.assertEqual(v.kind, "consistent", v.to_json())


class PowerLossBackendTests(unittest.TestCase):
    """W7d, first increment: the block replay rig's records (the 2026-09-26
    evidence, 236 crash images) as scenarios and journals judged whole-
    history.  Every cut record is consistent under the composition; every
    control record (a POST judged acknowledged whose writes follow the cut)
    is a violation citing the composition's rules; recover-crash records
    carry the second fault; a tampered count is caught."""

    @classmethod
    def setUpClass(cls):
        from tools.resilience.adapters import power_loss
        cls.pl = power_loss
        cls.records = power_loss.records()

    def test_every_evidence_record_reaches_its_expected_verdict(self):
        self.assertGreaterEqual(len(self.records), 200)
        kinds = collections.Counter()
        init_stuck = []
        for rec in self.records:
            s, j, v = self.pl.check_record(rec)
            with self.subTest(scenario=s.id):
                self.assertEqual(validate(s, REGISTRY), [], s.id)
                self.assertEqual(s.replay, "image")
                kinds[(rec["phase"] in self.pl.CONTROL_PHASES, v.kind)] += 1
                if rec["phase"] == "init" and v.kind == "violation":
                    # The documented constraint (planning/evidence/power-
                    # loss-2026-09-26.md, "Constraint"): a cut inside
                    # `operator init` can leave a store directory that
                    # neither recovers (a missing staging directory, config
                    # or allocation frontier) nor re-initializes
                    # (STORE-EXISTS).  The rig footnoted it; the whole-
                    # history checker judges it: init is not old-or-new.
                    init_stuck.append(rec["cut"])
                    self.assertEqual(v.explanation["rules"], ["recovery-keeps-history"])
                    self.assertEqual(rec["reinit"], 1, rec)
                    continue
                self.assertEqual(v.kind, s.expected, (s.id, v.cause, v.explanation))
                if v.kind == "consistent":
                    # Counts alone leave the in-flight posts' fates open
                    # where no recovery count narrows them (the reclaim
                    # and reference phases): more than one history may
                    # survive; a post or checkpoint image narrows to one.
                    self.assertGreaterEqual(v.surviving, 1, s.id)
                    if rec.get("first_phase", rec["phase"]) in ("post", "checkpoint"):
                        self.assertEqual(v.surviving, 1, s.id)
                    self.assertTrue(v.green, (s.id, v.witnesses_missing))
                if rec["phase"] in self.pl.CONTROL_PHASES:
                    # Caught by the recovery's own count (articles= below
                    # the acknowledged) or by the served counts.
                    self.assertTrue(set(v.explanation["rules"]) & {
                        "recovery-keeps-history", "power-loss-prefix"}, v.explanation)
                if rec.get("second"):
                    fired = [r["boundary"] for r in j.of_kind("environment")
                             if r.get("event") == "fault-fired"]
                    self.assertEqual(fired, [self.pl.BOUNDARY, self.pl.RECOVERY_BOUNDARY])
        self.assertEqual(kinds[(True, "violation")], 6)
        self.assertEqual(sorted(init_stuck), [169, 187, 200, 222, 234, 236])
        self.assertEqual(kinds[(False, "violation")], len(init_stuck))
        self.assertEqual(sorted(row[0] for row in self.pl.summary()["unexpected"]),
                         sorted("power-loss-init-{}".format(c) for c in init_stuck))

    def test_a_served_count_below_the_acknowledged_is_a_violation(self):
        rec = dict(next(r for r in self.records if r["phase"] == "post" and r["acked"] >= 3))
        rec["served_ref"] -= 1
        rec["absent"] += 1
        s, j, v = self.pl.check_record(rec)
        self.assertEqual(v.kind, "violation", v.to_json())
        self.assertIn(v.explanation["record"]["event"], ("persisted-records", "served-counts"))

    def test_a_non_prefix_selection_is_no_history(self):
        s = self.pl.scenario_for({"phase": "post", "cut": 1, "mode": "subset", "acked": 1,
                                  "refused": 0, "served_ref": 2, "absent": 1, "other": 0})
        history = {"post-1": "committed", "post-2": "absent", "post-3": "committed"}
        rec = {"seq": 0, "kind": "environment", "event": "persisted-write-selection",
               "open": ["post-2", "post-3"]}
        ok, rules = contract.narrow(s, history, rec, Journal(s.id), REGISTRY)
        self.assertFalse(ok)
        self.assertEqual(rules, ("power-loss-prefix",))
        history["post-2"] = "committed"
        self.assertTrue(contract.narrow(s, history, rec, Journal(s.id), REGISTRY)[0])

    def test_a_reused_number_is_a_violation(self):
        rec = dict(next(r for r in self.records if r["phase"] == "post" and r.get("binding")))
        rec["binding"] = dict(rec["binding"], fresh_number=rec["binding"]["max_served"])
        s, j, v = self.pl.check_record(rec)
        self.assertEqual(v.kind, "violation", v.to_json())
        self.assertEqual(v.explanation["rules"], ["number-stability"])

    def test_per_article_outcomes_are_reads_and_the_prefix_is_judged_per_article(self):
        """W7d-2: a record carrying the rig's per-article outcomes is judged
        article by article: the same counts with the served unacknowledged
        post AFTER an absent one in log order is no prefix (a violation the
        counts alone cannot see), and an acknowledged article absent is one."""
        import re
        real = next(r for r in self.records if r["phase"] == "post" and r["acked"] >= 1
                    and not r.get("second"))
        # One acknowledged post, then two in flight at the cut: the store
        # recovered two articles (the acknowledged one and the first in
        # flight), the second in flight is absent.
        rec = dict(real, acked=1, refused=0, served_ref=2, absent=1, other=0,
                   binding=None, second=None, violations=[],
                   recover_out=re.sub(r"articles=\d+", "articles=2", real["recover_out"]))
        n, served = self.pl.attempted(rec), rec["served_ref"]
        self.assertEqual((n, served), (3, 2))
        per = [[i, "ref" if i < served else "absent"] for i in range(n)]
        s, j, v = self.pl.check_record(dict(rec, per=per))
        self.assertEqual(v.kind, "consistent", v.to_json())
        reads = [r for r in j.of_kind("client") if r.get("event") == "read"]
        self.assertEqual([(r["article"], r["result"]) for r in reads],
                         [("post-{}".format(i + 1), "match" if i < served else "absent")
                          for i in range(n)])
        self.assertEqual([r for r in j.of_kind("client") if r.get("event") == "served-counts"], [])
        swapped = [list(x) for x in per]
        swapped[served - 1][1], swapped[served][1] = "absent", "ref"
        s, j, v = self.pl.check_record(dict(rec, per=swapped))
        self.assertEqual(v.kind, "violation", v.to_json())
        self.assertIn("power-loss-prefix", v.explanation["rules_used"])
        # The counts are unchanged; a per-article read is what no history
        # survives (the prefix history dies at post-2 absent, the swapped
        # one at the selection).
        self.assertEqual(v.explanation["record"]["event"], "read")
        gone = [list(x) for x in per]
        gone[0][1] = "absent"
        s, j, v = self.pl.check_record(dict(rec, per=gone))
        self.assertEqual(v.kind, "violation", v.to_json())

    def test_an_observed_number_is_judged_on_its_own(self):
        """W7d-2: each number a reader was served before the cut is its own
        `number` observation: the same article after recovery is consistent,
        another article (reissued) a violation, unlisted a violation before
        the reclaim and consistent from the reclaim on."""
        mid = "<t17-000000@example.invalid>"
        rec = dict(next(r for r in self.records if r["phase"] == "post" and r.get("binding")))
        for kind, expected in (("same", "consistent"), ("reissued", "violation"),
                               ("unlisted", "violation")):
            with self.subTest(kind=kind):
                s, j, v = self.pl.check_record(
                    dict(rec, binding=dict(rec["binding"], observed_numbers=[[1, mid, kind]])))
                self.assertEqual(v.kind, expected, v.to_json())
                self.assertIn("observed", s.healing)
                numbers = [r for r in j.of_kind("client") if r.get("event") == "number"]
                self.assertEqual([(r["number"], r["msgid"], r["result"], r["article"],
                                   r["reclaimed"]) for r in numbers],
                                 [(1, mid, kind, "post-1", False)])
                if expected == "violation":
                    self.assertIn("number-stability", v.explanation["rules"])
        after = dict(next(r for r in self.records
                          if r["phase"] == "reclaim" and r.get("binding") and not r["violations"]))
        s, j, v = self.pl.check_record(
            dict(after, binding=dict(after["binding"], observed_numbers=[[1, mid, "unlisted"]])))
        self.assertEqual(v.kind, "consistent", v.to_json())
        self.assertTrue([r for r in j.of_kind("client") if r.get("event") == "number"][0]["reclaimed"])

    def test_the_rig_classify_writes_per_article_outcomes_summing_to_its_counts(self):
        import tools.power_loss as rig
        ref = [b"220 a", b"220 b", b"220 c"]
        got = [b"220 a", b"430 no such article", b"220 x"]
        violations = []
        c = rig.classify(got, "post", {0}, ref, list(ref), violations)
        self.assertEqual(c["per"], [[0, "ref"], [1, "absent"], [2, "other"]])
        self.assertEqual((c["served_ref"], c["served_reclaimed"], c["absent"], c["other"]),
                         (1, 0, 1, 1))
        self.assertEqual(violations, ["unacked-mismatch:2:b'220 x'"])


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
