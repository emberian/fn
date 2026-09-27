"""Served-owner process deaths on the record log (format 9).

FN_NATIVE_CRASH_HOST must be a source-matched developer image.  No test class
is registered without it; an absent image contributes zero runtime evidence.

The served owner commits a POST as P-BATCH on the record log (lane
commit-onto-log); its process-death cuts are native_cuts.POST_LOG_CUTS and the
recovery's five barriers (fnn-recover-log's recover-barrier-N).  At each the
killed store's committed history -- the image's scan of the segment,
tests/native_log_observation.py -- is the prior history, or the prior history
and the candidate, as the cut's column says; `operator recover' keeps exactly
that history, serves the prior as stored and the candidate whole exactly when
it is in the history (tests.test_native_crash_model's NativeCampaignMixin).
The per-file programs' model-image differential this module ran before
(fn-bs-record-program and fn-bs-marker-program's cuts, fn-bs-recover-program's
image) is not reachable on a format-9 store and is retired with them.
"""
import os
from pathlib import Path
import tempfile
import unittest

from tests.campaign import native_cuts
from tests.campaign.native_operator_campaign import (
    CANDIDATE_ID, GROUP, PRIOR_ID, Node, article, parse_recover,
)
from tests.test_native_crash_model import IMAGE_AVAILABLE, NativeCampaignMixin


if IMAGE_AVAILABLE:
    class NativeServedCrashModelTests(NativeCampaignMixin, unittest.TestCase):
        def seeded(self, base, name):
            prior = base / "prior.art"
            prior.write_bytes(article(PRIOR_ID, "prior", "prior retained body"))
            node = Node(Path(os.environ["FN_NATIVE_CRASH_HOST"]), base, name)
            init = node.operator("init", GROUP)
            self.assertEqual(init["rc"], 0, init)
            owner = node.start_owner()
            self.assertTrue(owner["ready"],
                            node.stop_owner(owner) if not owner["ready"] else owner)
            seeded = node.post(PRIOR_ID, prior)
            self.assertEqual(seeded["rc"], 0, seeded)
            node.stop_owner(owner)
            return node, node.inspect(PRIOR_ID)["_out"]

        def recovered_as(self, node, name, at_cut, prior_bytes):
            recovery = node.operator("recover")
            self.assertEqual(recovery["rc"], 0, (name, recovery))
            self.assertIsNotNone(parse_recover(recovery["_out"]))
            self.assertEqual(self.history(node.store), at_cut, name)
            prior_after = node.inspect(PRIOR_ID)
            self.assertEqual(prior_after["rc"], 0, prior_after)
            self.assertEqual(prior_after["_out"], prior_bytes)
            return node.inspect(CANDIDATE_ID)["rc"] == 0

        def test_served_post_log_cuts(self):
            selected = os.environ.get("FN_NATIVE_SERVED_CUT")
            for cut in native_cuts.POST_LOG_CUTS:
                if selected and cut.name != selected:
                    continue
                with self.subTest(cut=cut.name), tempfile.TemporaryDirectory(
                        prefix="fn-served-log-") as scratch:
                    base = Path(scratch)
                    candidate = base / "candidate.art"
                    candidate.write_bytes(article(CANDIDATE_ID, "candidate", "interrupted body"))
                    node, prior_bytes = self.seeded(base, cut.name)
                    try:
                        before = self.history(node.store)
                        owner = node.start_owner({"FN_NATIVE_POST_FAULT": cut.name + ":kill"})
                        self.assertTrue(owner["ready"],
                                        node.stop_owner(owner) if not owner["ready"] else owner)
                        result = node.post(CANDIDATE_ID, candidate)
                        killed = node.stop_owner(owner)
                        self.assertEqual(killed["rc"], -9, (cut.name, result, killed))
                        at_cut = self.history(node.store)
                        self.assert_cut_history(cut.name, cut.candidate, before, at_cut)
                        present = self.recovered_as(node, cut.name, at_cut, prior_bytes)
                        self.assertEqual(present, len(at_cut) == len(before) + 1, cut.name)
                    finally:
                        node.reap()

        def test_five_served_recovery_barriers_are_distinct_cuts(self):
            selected = os.environ.get("FN_NATIVE_SERVED_CUT")
            cuts = [cut for cut in native_cuts.RECOVERY_CUTS
                    if cut.model_name == "recover-barrier"
                    and (selected is None or cut.name == selected)]
            self.assertEqual(len(cuts), 5 if selected is None else 1)
            for cut in cuts:
                with self.subTest(cut=cut.name), tempfile.TemporaryDirectory(
                        prefix="fn-served-recover-") as scratch:
                    base = Path(scratch)
                    candidate = base / "candidate.art"
                    candidate.write_bytes(article(CANDIDATE_ID, "candidate", "orphan body"))
                    node, prior_bytes = self.seeded(base, cut.name)
                    try:
                        before = self.history(node.store)
                        orphan = node.store_post(CANDIDATE_ID, candidate, {
                            "FN_NATIVE_POST_FAULT": "log-written:kill"})
                        self.assertEqual(orphan["rc"], -9, orphan)
                        at_cut = self.history(node.store)
                        self.assert_cut_history("log-written", "either", before, at_cut)
                        killed = node.start_owner({
                            "FN_NATIVE_RECOVERY_FAULT": cut.name + ":kill"})
                        self.assertFalse(killed["ready"], cut.name)
                        stopped = node.stop_owner(killed)
                        self.assertEqual(stopped["rc"], -9, stopped)
                        self.assertEqual(self.history(node.store), at_cut, cut.name)
                        present = self.recovered_as(node, cut.name, at_cut, prior_bytes)
                        self.assertEqual(present, len(at_cut) == len(before) + 1, cut.name)
                    finally:
                        node.reap()


if __name__ == "__main__":
    unittest.main()
