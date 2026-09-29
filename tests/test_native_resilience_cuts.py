"""The native cut campaigns as scenarios (rows W7b and W7c): the post,
recovery, served, served-recovery and checkpoint families generate one
scenario per cut; on the developer image the adapter runs them and the
verdict is the whole-history checker's (each scenario's expected verdict);
a run with the fault hook disabled is a harness failure by name (the
tester's test on the box); the offline per-group observation runs through
`store inspect --group` when the image carries it and is PENDING BY NAME
when it does not; the review's schedule points run where they have a host
coordinate and are named pending where they do not.

Runtime tests exist only when FN_NATIVE_CRASH_HOST names a source-matched
developer image; their absence is zero runtime evidence, never a skip.
FN_NATIVE_RESILIENCE_CUT=NAME selects one cut; FN_NATIVE_LOWLEVEL_CUT is
honoured for the post family as before."""
from __future__ import annotations

import os
from pathlib import Path
import tempfile
import unittest

from tests.campaign import native_cuts
from tools.resilience import schedule_points
from tools.resilience.adapters import native_cuts as adapter
from tools.resilience.journal import Journal
from tools.resilience.scenario import boundary_registry, validate

IMAGE = Path(os.environ.get("FN_NATIVE_CRASH_HOST", ""))
IMAGE_AVAILABLE = IMAGE.is_file() and os.access(IMAGE, os.X_OK)
SELECTED = os.environ.get("FN_NATIVE_RESILIENCE_CUT")
# Harness-failure causes that mean "the held form is not on this image":
# the adapters raise them from the image's own evidence (the receipt path
# past its hold point; `store inspect --group` refused), never from a timeout.
PENDING_BY_NAME = ("hold-unavailable:", "inspect-group-unavailable:",
                   # a nemesis verb refused by the image under the running node
                   # (`bp-route remove`: store-held, no control socket)
                   "live-route-unavailable:")


class CutScenarioTableTests(unittest.TestCase):
    def test_one_scenario_per_post_log_cut_at_its_boundary(self):
        registry = boundary_registry()
        scenarios = adapter.scenarios()
        self.assertEqual([s.id for s in scenarios],
                         ["native-cut-" + c.name for c in native_cuts.POST_LOG_CUTS])
        for cut, s in zip(native_cuts.POST_LOG_CUTS, scenarios):
            self.assertEqual(validate(s, registry), [])
            (fault,) = s.faults
            self.assertEqual((fault.operation, fault.boundary, fault.action, fault.fault_class,
                              fault.route),
                             (adapter.CANDIDATE, cut.name, "kill", "contract-admissible",
                              "store-post"))
            self.assertEqual(registry[cut.name]["rule"], native_cuts.POST_LOG_ONE_CANDIDATE[cut.name])
            self.assertEqual(registry[cut.name]["rules"]["served-post"], cut.candidate)
            self.assertEqual(registry[cut.name]["program"], cut.program)
            self.assertEqual(s.witnesses, ["post-accepted", "retry-reconciled", "read-completed",
                                           "recovery-completed"])
            self.assertEqual(s.healing_bound["kind"], "experimental")

    def test_the_recovery_and_served_families_name_their_cuts(self):
        self.assertEqual([s.id for s in adapter.family_scenarios("recovery")],
                         ["native-recovery-" + n for n in
                          ("recover-replayed", "recover-barrier-1", "recover-barrier-2",
                           "recover-barrier-3", "recovery-stage-unlinked", "log-truncated",
                           "log-recovered")])
        for s in adapter.family_scenarios("recovery"):
            self.assertEqual([f.boundary for f in s.faults],
                             [adapter.ORPHAN_BOUNDARY, s.id[len("native-recovery-"):]])
        for s in adapter.family_scenarios("served"):
            (fault,) = s.faults
            self.assertEqual(fault.route, "served-post")
            self.assertEqual(s.operation(adapter.CANDIDATE).args["groups"],
                             [adapter.GROUP, adapter.GROUP2])
            self.assertIn("memberships-listed", s.witnesses)
        self.assertEqual([s.id for s in adapter.family_scenarios("served-recovery")],
                         ["native-served-recovery-recover-barrier-{}".format(i) for i in (1, 2, 3)])
        self.assertEqual([s.id for s in adapter.family_scenarios("checkpoint")],
                         ["native-checkpoint-" + c.name for c in native_cuts.STATE_CHECKPOINT_CUTS])

    def test_missing_image_is_not_a_skipped_campaign(self):
        self.assertEqual(IMAGE_AVAILABLE, "NativeResilienceCutTests" in globals())


if IMAGE_AVAILABLE:
    class NativeResilienceCutTests(unittest.TestCase):
        def run_expected(self, s, prefix):
            """Run S; its verdict is the expected one and green; the fired
            faults are exactly the scheduled ones; the journal lives beside
            the store and is what the verdict was made over."""
            with tempfile.TemporaryDirectory(prefix=prefix) as tmp:
                journal, verdict = adapter.run(s, IMAGE, Path(tmp))
                if (verdict.kind == "harness-failure"
                        and (verdict.cause or "").startswith(PENDING_BY_NAME)):
                    # The adapter found, from the image's own lines, that the
                    # held form is not on this image: no verdict, pending by
                    # name (the mode, 2026-09-29), never a skipped campaign.
                    self.skipTest("pending by name ({}): {}".format(s.id, verdict.cause))
                self.assertEqual(verdict.kind, s.expected, (s.id, verdict.to_json()))
                self.assertTrue(verdict.green, (s.id, verdict.to_json()))
                self.assertEqual(verdict.surviving, 1, s.id)
                self.assertEqual(verdict.diagnostics, [], (s.id, verdict.diagnostics))
                fired = [r["boundary"] for r in journal.of_kind("environment")
                         if r.get("event") == "fault-fired"]
                self.assertEqual(fired, [f.boundary for f in s.faults], s.id)
                self.assertTrue((Path(tmp) / "journal.jsonl").is_file())
                self.assertFalse((Path(tmp) / "store" / "journal.jsonl").exists())
                self.assertFalse((Path(tmp) / "node" / "store" / "journal.jsonl").exists())
                self.assertEqual(Journal.read(Path(tmp) / "journal.jsonl").digest(),
                                 verdict.journal_digest)
                self.assertIsNotNone(verdict.healing)
                return journal, verdict

        def family(self, name):
            for s in adapter.family_scenarios(name):
                cut = s.faults[-1].boundary
                if SELECTED and cut != SELECTED:
                    continue
                if name == "post" and os.environ.get("FN_NATIVE_LOWLEVEL_CUT") not in (None, cut):
                    continue
                with self.subTest(scenario=s.id):
                    yield s, self.run_expected(s, "fn-resilience-{}-".format(name))

        def test_every_post_log_cut_is_green_by_the_checker(self):
            for s, (journal, verdict) in self.family("post"):
                self.assertEqual(verdict.pending_rules, [])

        def test_recovery_killed_at_every_cut_keeps_the_history_and_recovers_again(self):
            for s, (journal, verdict) in self.family("recovery"):
                scans = {r["phase"]: r["count"] for r in journal.of_kind("environment")
                         if r.get("event") == "persisted-records"}
                self.assertEqual(scans["at-cut"], scans["after-killed-recovery"], s.id)
                self.assertEqual(scans["after-recovery"], scans["at-cut"], s.id)
                writes = [r for r in journal.of_kind("environment") if r.get("event") == "recovery-writes"]
                self.assertEqual(len(writes), 1, s.id)
                self.assertIn("recovery-completed", verdict.witnesses_observed)

        def test_served_owner_killed_at_every_post_cut_lists_both_memberships_or_neither(self):
            for s, (journal, verdict) in self.family("served"):
                listed = {r["group"]: set(r["members"]) for r in journal.of_kind("client")
                          if r.get("event") == "list-group"}
                self.assertEqual(set(listed), {adapter.GROUP, adapter.GROUP2}, s.id)
                self.assertIn(adapter.PRIOR, listed[adapter.GROUP], s.id)
                self.assertEqual(adapter.CANDIDATE in listed[adapter.GROUP],
                                 adapter.CANDIDATE in listed[adapter.GROUP2], s.id)
                self.assertIn("memberships-listed", verdict.witnesses_observed)

        def test_owner_open_killed_at_every_recovery_barrier_is_healed_by_operator_recover(self):
            for s, (journal, verdict) in self.family("served-recovery"):
                restarted = [r for r in journal.of_kind("client") if r.get("event") == "restart"]
                self.assertEqual([r["outcome"] for r in restarted], ["died"], s.id)
                self.assertIn("recovery-completed", verdict.witnesses_observed)

        def test_checkpoint_killed_at_every_cut_reads_one_whole_checkpoint(self):
            for s, (journal, verdict) in self.family("checkpoint"):
                installed = [r for r in journal.of_kind("environment")
                             if r.get("event") == "checkpoint-installed"]
                self.assertEqual(len(installed), 1, s.id)
                self.assertIn(installed[0]["which"], ("old", "new"), (s.id, installed))
                self.assertIn("checkpoint-installed", verdict.witnesses_observed)

        def test_offline_memberships_through_inspect_group_or_pending_by_name(self):
            s = adapter.scenario_for(native_cuts.POST_LOG_CUTS[3], memberships=True)
            with tempfile.TemporaryDirectory(prefix="fn-resilience-offline-members-") as tmp:
                journal, verdict = adapter.run(s, IMAGE, Path(tmp))
                if (verdict.kind == "harness-failure"
                        and (verdict.cause or "").startswith("inspect-group-unavailable")):
                    self.skipTest("pending by name: store inspect --group ({}) is not on this "
                                  "image: {}".format(adapter.OFFLINE_MEMBERSHIP_SOURCE,
                                                     verdict.cause))
                self.assertTrue(verdict.green, (s.id, verdict.to_json()))
                listed = {r["group"]: set(r["members"]) for r in journal.of_kind("client")
                          if r.get("event") == "list-group"}
                self.assertEqual(set(listed), {adapter.GROUP, adapter.GROUP2})
                self.assertEqual(adapter.CANDIDATE in listed[adapter.GROUP],
                                 adapter.CANDIDATE in listed[adapter.GROUP2])

        def test_schedule_point_scenarios_reach_their_expected_verdict_or_are_pending_by_name(self):
            rows = {r["scenario"]: r for r in schedule_points.status()}
            pending = sorted(k for k, r in rows.items() if r["status"] == "pending")
            self.assertEqual(pending, ["schedule-page-read-outstanding",
                                       "schedule-receipt-observed-reorder",
                                       "schedule-reclaim-candidate-selected"],
                             "a pending point changed status: run it, or name why not")
            for s in schedule_points.scenarios():
                if rows[s.id]["status"] != "executable":
                    continue
                if SELECTED and s.faults[-1].boundary != SELECTED:
                    continue
                with self.subTest(scenario=s.id, point=rows[s.id]["point"]):
                    self.run_expected(s, "fn-resilience-schedule-")

        def test_true_issued_page_io_settles_cancelled_token_and_reads_retained_article(self):
            if SELECTED and SELECTED != "page-read-outstanding":
                return
            from tools.resilience.adapters import page_io
            s = page_io.example()
            with tempfile.TemporaryDirectory(prefix="fn-resilience-issued-page-") as tmp:
                journal, verdict = page_io.run_scenario(s, IMAGE, Path(tmp))
                self.assertTrue(verdict.green, verdict.to_json())
                self.assertIn("page-io-native-composition", verdict.pending_rules)
                self.assertIn("cancelled-read-settled", verdict.witnesses_observed)
                self.assertIn("read-completed", verdict.witnesses_observed)
                self.assertEqual(Journal.read(Path(tmp) / "journal.jsonl").digest(),
                                 journal.digest())

        def test_disabling_the_real_issued_page_io_hold_cannot_pass(self):
            if SELECTED and SELECTED != "page-read-outstanding":
                return
            from tools.resilience.adapters import page_io
            with tempfile.TemporaryDirectory(prefix="fn-resilience-no-issued-hold-") as tmp:
                _, verdict = page_io.run_scenario(page_io.example(), IMAGE, Path(tmp), False)
                self.assertFalse(verdict.green, verdict.to_json())
                self.assertEqual(verdict.kind, "harness-failure", verdict.to_json())
                self.assertTrue((verdict.cause or "").startswith("fault-never-occurred:"),
                                 verdict.to_json())

        def test_running_bp_route_control_reorders_receipt_then_heals(self):
            if SELECTED and SELECTED != "receipt-observed":
                return
            scenario = next(s for s in schedule_points.scenarios()
                            if s.id == "schedule-receipt-observed-reorder")
            self.run_expected(scenario, "fn-resilience-live-route-")

        def test_capture_first_reclaim_waits_for_independent_response_then_makes_progress(self):
            if SELECTED and SELECTED != "reclaim-candidate-selected":
                return
            from tools.resilience.adapters import reclaim_hold
            with tempfile.TemporaryDirectory(prefix="fn-resilience-new-response-hold-") as tmp:
                _, verdict = reclaim_hold.run_scenario(reclaim_hold.example(), IMAGE, Path(tmp))
                self.assertTrue(verdict.green, verdict.to_json())
                self.assertIn("independent-response-held", verdict.witnesses_observed)
                self.assertIn("response-hold-settled", verdict.witnesses_observed)
                self.assertIn("reclaim-freed", verdict.witnesses_observed)

        def test_disabling_the_capture_first_reclaim_hold_cannot_pass(self):
            if SELECTED and SELECTED != "reclaim-candidate-selected":
                return
            from tools.resilience.adapters import reclaim_hold
            with tempfile.TemporaryDirectory(prefix="fn-resilience-no-capture-hold-") as tmp:
                _, verdict = reclaim_hold.run_scenario(reclaim_hold.example(), IMAGE, Path(tmp), False)
                self.assertFalse(verdict.green, verdict.to_json())
                self.assertEqual(verdict.kind, "harness-failure", verdict.to_json())
                self.assertTrue((verdict.cause or "").startswith("fault-never-occurred:"),
                                verdict.to_json())

        def test_a_retry_across_routes_is_refused_by_name_and_the_store_is_unchanged(self):
            """The route finding as a scenario (adapter.cross_route_retry_
            scenario): the store-posted article POSTed again on the served
            listener answers the named 441 conflict, the reads before and
            after match the bytes as posted behind the one served Xref, and
            the log's record count is the same at the cut and at the end."""
            journal, verdict = self.run_expected(adapter.cross_route_retry_scenario(),
                                                 "fn-resilience-xroute-")
            reply = [r for r in journal.of_kind("client")
                     if r.get("event") == "reply" and r.get("operation") == "retry-served"]
            self.assertEqual(len(reply), 1)
            self.assertEqual(reply[0]["outcome"], "refused", reply[0])
            self.assertIn("a different article with this Message-ID is stored", reply[0]["status"])
            self.assertTrue(reply[0]["cross_route"])
            reads = [r for r in journal.of_kind("client") if r.get("event") == "read"]
            self.assertEqual([r["result"] for r in reads], ["match", "match"], reads)
            self.assertTrue(all(r["xref"] and not r["xref"]["malformed"] for r in reads), reads)
            counts = [r["count"] for r in journal.of_kind("environment")
                      if r.get("event") == "persisted-records"]
            self.assertEqual(counts, [1, 1, 1], counts)
            self.assertIn("cross-route-retry-refused", verdict.witnesses_observed)
            self.assertIn("identity-is-the-bytes", verdict.pending_rules)

        def test_disabled_fault_hook_is_a_harness_failure(self):
            s = adapter.scenarios()[3]      # log-written
            with tempfile.TemporaryDirectory(prefix="fn-resilience-nofault-") as tmp:
                _, verdict = adapter.run(s, IMAGE, Path(tmp), fault_hook=False)
                self.assertEqual(verdict.kind, "harness-failure", verdict.to_json())
                self.assertTrue(verdict.cause.startswith("fault-never-occurred:post-candidate@log-written"))
                self.assertFalse(verdict.green)


if __name__ == "__main__":
    if not IMAGE_AVAILABLE:
        raise SystemExit("FN_NATIVE_CRASH_HOST must name a source-matched developer image")
    unittest.main()
