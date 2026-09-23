"""Served-owner process deaths against ACL2's visible byte-store relation.

FN_NATIVE_CRASH_HOST must be a source-matched developer image.  No test class
is registered without it; an absent image contributes zero runtime evidence.
"""
import os
from pathlib import Path
import tempfile
import unittest

from tests.campaign import model_images, native_cuts
from tests.campaign.native_operator_campaign import (
    CANDIDATE_ID, GROUP, PRIOR_ID, Node, article, parse_recover,
)
from tests.test_native_crash_model import IMAGE_AVAILABLE, NativeCampaignMixin


if IMAGE_AVAILABLE:
    class NativeServedCrashModelTests(NativeCampaignMixin, unittest.TestCase):
        def assert_recovery_cut_image(self, before, store, cut):
            bridge = model_images.ModelBridge()
            try:
                bridge.call('(include-book "books/byte-store-observation")')
                index = model_images.cut_index(cut.program,
                                               cut.model_name or cut.name,
                                               cut.occurrence)
                observed = bridge.value(
                    "(let* ((before {}) (physical {})"
                    " (run (fn-bs-run before (fn-sf-initial-state)"
                    " (fn-bs-recover-program) nil nil nil))"
                    " (cut-bs (car (nth {} run)))"
                    " (model-image (fn-bs-crash cut-bs nil)))"
                    " (list (equal (fn-bs-pending cut-bs) nil)"
                    "       (fn-bso-served-image-agree model-image physical)))".format(
                        before, model_images.import_image(store), index))
                self.assertRegex(observed, r"\(T\s+T\)\s*$",
                                 "{} occurrence {}: {}".format(
                                     cut.name, cut.occurrence, observed))
            finally:
                bridge.close()

        def test_served_prepare_publish_finish_cuts(self):
            # One cut on each side of publication and each durable completion
            # boundary.  The lower-level post test covers the intervening
            # syscall cuts; this test drives the served owner itself.
            names = ("frontier-replaced", "record-staged-durable",
                     "record-linked", "record-durable", "finish-consumed",
                     "finish-durable")
            selected = os.environ.get("FN_NATIVE_SERVED_CUT")
            if selected:
                names = (selected,)
            cuts = {cut.name: cut for cut in native_cuts.POST_CUTS}
            for name in names:
                cut = cuts[name]
                with self.subTest(cut=name), tempfile.TemporaryDirectory(
                        prefix="fn-served-byte-") as scratch:
                    base = Path(scratch)
                    prior = base / "prior.art"
                    candidate = base / "candidate.art"
                    prior.write_bytes(article(PRIOR_ID, "prior", "prior retained body"))
                    candidate.write_bytes(article(CANDIDATE_ID, "candidate", "interrupted body"))
                    node = Node(Path(os.environ["FN_NATIVE_CRASH_HOST"]), base, name)
                    try:
                        init = node.operator("init", GROUP)
                        self.assertEqual(init["rc"], 0, init)
                        owner = node.start_owner()
                        self.assertTrue(owner["ready"],
                                        node.stop_owner(owner) if not owner["ready"] else owner)
                        seeded = node.post(PRIOR_ID, prior)
                        self.assertEqual(seeded["rc"], 0, seeded)
                        node.stop_owner(owner)
                        prior_bytes = node.inspect(PRIOR_ID)["_out"]
                        prior_names = self.transaction_bytes(node.store)
                        before = model_images.import_image(node.store)

                        owner = node.start_owner({"FN_NATIVE_POST_FAULT": name + ":kill"})
                        self.assertTrue(owner["ready"],
                                        node.stop_owner(owner) if not owner["ready"] else owner)
                        result = node.post(CANDIDATE_ID, candidate)
                        killed = node.stop_owner(owner)
                        self.assertEqual(killed["rc"], -9, (name, result, killed))
                        self.assert_observed_scan_is_program_image(
                            before, node.store, cut, prior_names)

                        recovery = node.operator("recover")
                        self.assertEqual(recovery["rc"], 0, (name, recovery))
                        self.assertIsNotNone(parse_recover(recovery["_out"]))
                        prior_after = node.inspect(PRIOR_ID)
                        self.assertEqual(prior_after["rc"], 0, prior_after)
                        self.assertEqual(prior_after["_out"], prior_bytes)
                        present = node.inspect(CANDIDATE_ID)["rc"] == 0
                        if cut.candidate == "absent":
                            self.assertFalse(present, name)
                        elif cut.candidate == "present":
                            self.assertTrue(present, name)
                    finally:
                        node.reap()

        def test_five_served_recovery_barriers_are_distinct_model_cuts(self):
            selected = os.environ.get("FN_NATIVE_SERVED_CUT")
            cuts = [cut for cut in native_cuts.RECOVERY_CUTS
                    if cut.model_name == "recover-barrier"
                    and (selected is None or cut.name == selected)]
            for cut in cuts:
                with self.subTest(cut=cut.name), tempfile.TemporaryDirectory(
                        prefix="fn-served-recover-byte-") as scratch:
                    base = Path(scratch)
                    prior = base / "prior.art"
                    candidate = base / "candidate.art"
                    prior.write_bytes(article(PRIOR_ID, "prior", "prior retained body"))
                    candidate.write_bytes(article(CANDIDATE_ID, "candidate", "orphan body"))
                    node = Node(Path(os.environ["FN_NATIVE_CRASH_HOST"]), base, cut.name)
                    try:
                        self.assertEqual(node.operator("init", GROUP)["rc"], 0)
                        owner = node.start_owner()
                        self.assertTrue(owner["ready"], owner)
                        self.assertEqual(node.post(PRIOR_ID, prior)["rc"], 0)
                        node.stop_owner(owner)
                        prior_bytes = node.inspect(PRIOR_ID)["_out"]
                        orphan = node.store_post(CANDIDATE_ID, candidate, {
                            "FN_NATIVE_POST_FAULT": "record-staged-durable:kill"})
                        self.assertEqual(orphan["rc"], -9, orphan)
                        self.assertTrue(list((node.store / "staging").glob(".stage-*")))
                        before = model_images.import_image(node.store)
                        killed = node.start_owner({
                            "FN_NATIVE_RECOVERY_FAULT": cut.name + ":kill"})
                        self.assertFalse(killed["ready"], cut.name)
                        stopped = node.stop_owner(killed)
                        self.assertEqual(stopped["rc"], -9, stopped)
                        self.assert_recovery_cut_image(before, node.store, cut)
                        recovered = node.operator("recover")
                        self.assertEqual(recovered["rc"], 0, recovered)
                        prior_after = node.inspect(PRIOR_ID)
                        self.assertEqual(prior_after["rc"], 0, prior_after)
                        self.assertEqual(prior_after["_out"], prior_bytes)
                        self.assertNotEqual(node.inspect(CANDIDATE_ID)["rc"], 0)
                    finally:
                        node.reap()
