"""The native cut campaign as scenarios (row W7b): POST_LOG_CUTS generate
one scenario each; on the developer image the adapter runs them and the
verdict is the whole-history checker's; a run with the fault hook disabled
is a harness failure by name (the tester's test on the box).

Runtime tests exist only when FN_NATIVE_CRASH_HOST names a source-matched
developer image; their absence is zero runtime evidence, never a skip."""
from __future__ import annotations

import os
from pathlib import Path
import tempfile
import unittest

from tests.campaign import native_cuts
from tools.resilience.adapters import native_cuts as adapter
from tools.resilience.journal import Journal
from tools.resilience.scenario import boundary_registry, validate

IMAGE = Path(os.environ.get("FN_NATIVE_CRASH_HOST", ""))
IMAGE_AVAILABLE = IMAGE.is_file() and os.access(IMAGE, os.X_OK)


class CutScenarioTableTests(unittest.TestCase):
    def test_one_scenario_per_post_log_cut_at_its_boundary(self):
        registry = boundary_registry()
        scenarios = adapter.scenarios()
        self.assertEqual([s.id for s in scenarios],
                         ["native-cut-" + c.name for c in native_cuts.POST_LOG_CUTS])
        for cut, s in zip(native_cuts.POST_LOG_CUTS, scenarios):
            self.assertEqual(validate(s, registry), [])
            (fault,) = s.faults
            self.assertEqual((fault.operation, fault.boundary, fault.action, fault.fault_class),
                             (adapter.CANDIDATE, cut.name, "kill", "contract-admissible"))
            self.assertEqual(registry[cut.name]["rule"], native_cuts.POST_LOG_ONE_CANDIDATE[cut.name])
            self.assertEqual(registry[cut.name]["program"], cut.program)
            self.assertEqual(s.witnesses, ["post-accepted", "retry-reconciled", "read-completed"])

    def test_missing_image_is_not_a_skipped_campaign(self):
        self.assertEqual(IMAGE_AVAILABLE, "NativeResilienceCutTests" in globals())


if IMAGE_AVAILABLE:
    class NativeResilienceCutTests(unittest.TestCase):
        def test_every_post_log_cut_is_green_by_the_checker(self):
            selected = os.environ.get("FN_NATIVE_LOWLEVEL_CUT")
            for s in adapter.scenarios():
                if selected and s.id != "native-cut-" + selected:
                    continue
                with self.subTest(scenario=s.id), tempfile.TemporaryDirectory(
                        prefix="fn-resilience-cut-") as tmp:
                    journal, verdict = adapter.run(s, IMAGE, Path(tmp))
                    self.assertTrue(verdict.green, (s.id, verdict.to_json()))
                    self.assertEqual(verdict.surviving, 1, s.id)
                    self.assertEqual(verdict.pending_rules, [])
                    self.assertEqual(verdict.diagnostics, [])
                    fired = [r for r in journal.of_kind("environment")
                             if r.get("event") == "fault-fired"]
                    self.assertEqual(len(fired), 1, s.id)
                    self.assertTrue((Path(tmp) / "journal.jsonl").is_file())
                    self.assertFalse((Path(tmp) / "store" / "journal.jsonl").exists())
                    self.assertEqual(Journal.read(Path(tmp) / "journal.jsonl").digest(),
                                     verdict.journal_digest)

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
