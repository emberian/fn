"""Served-owner process deaths against ACL2's visible byte-store relation.

FN_NATIVE_CRASH_HOST must be a source-matched developer image.  No test class
is registered without it; an absent image contributes zero runtime evidence.
"""
import os
from pathlib import Path
import tempfile
import time
import unittest

from tests.campaign import model_images, native_cuts
from tests.campaign.native_operator_campaign import (
    CANDIDATE_ID, GROUP, PRIOR_ID, Node, article, parse_recover,
)
from tests.test_native_crash_model import IMAGE_AVAILABLE, NativeCampaignMixin


# The books and host bridge the stored-octets derivation below needs, loaded
# as host/native/build.lisp loads them.
SERVED_BRIDGE_SETUP = (
    '(include-book "books/records-concrete-owner")',
    # host/store-node-host.lisp declares the octet buffer stobj
    # (fn-store-sco-publish-plan, rep-wave-d-2) and reads the checkpoint
    # from it (fn-store-sco-decode, rep-wave-d-3): the same three books
    # tools/bridge_image.py loads before this ld (qual-b6759850 C18).
    '(include-book "books/octets-stobj")',
    '(include-book "books/store-checkpoint-buffer")',
    '(include-book "books/store-checkpoint-reader")',
    '(ld "host/store-node-host.lisp" :ld-error-action :error)',
    '(include-book "books/config-observed")',
    '(include-book "books/owner")',
    '(include-book "books/owner-agent")',
    '(include-book "books/owner-served-invariants")',
)


def octets(data: bytes) -> str:
    return "({})".format(" ".join(str(x) for x in data))


def served_stored_payload(store: Path, message_id: str, source: bytes) -> str:
    """ACL2's form for the octets the served owner stores for `operator post`.

    The owner does not store the file it was handed.  For `fn operator CONFIG
    post` (host/native/owner.lisp fnn-owner-control-submit-serialized) it takes
    one clock reading, submits (fn-owner-operator-submit, whose decision is
    books/owner.lisp fn-own-operator-decision under the owner's posting
    configuration and clock), and stores what fn-owner-take stages:
    fn-own-sub-stored-octets of the submission under the live configuration
    (books/owner-served-invariants.lisp).  The same reading stamps the record,
    so the form's `{unix_ms}` hole is the helper's bracketed second.

    The live configuration is the one fn-owner-recover builds: the store's
    config records (the config/ files in name order, decoded by the host's
    fn-store-cfg-decode-records) replayed over the pre-post store events
    (fn-cpr-replay).  Those events are the byte-store scan's: each committed
    frame unframed and decoded by fn-store-event-decode-exact
    (fn-bs-record-of-octets), the decoder the host's fn-store-decode-records
    applies to the unframed octets it passes.  The posting configuration is
    fn-owner-post-config's, fn-oag-post-config under *fn-record-max-payload*;
    the node is the one fn-cpo-open-observed opens.  Only the config inputs are read here; the
    article octets are derived, never read off the store.  A refused decision
    or an unopenable history yields nil, which frames no stored article.
    """
    return ("(let* ({}) (if (and (equal (fn-sn-open-kind opened) :ok)"
            " (fn-inj-injectedp decision))"
            " (fn-own-sub-stored-octets cfg"
            "  (fn-own-sub-make *fn-own-control-id* 0 nil decision))"
            " nil))").format(served_decision_bindings(store, message_id, source))


def served_decision_bindings(store: Path, message_id: str, source: bytes) -> str:
    """The let* bindings of `served_stored_payload`, up to the decision."""
    configs = sorted(p for p in (store / "config").iterdir() if p.is_file())
    config_octets = "'({})".format(" ".join(octets(p.read_bytes()) for p in configs))
    return (
        "(config-records (fn-store-cfg-decode-records {configs}))"
        " (events (fn-bs-scan-records before-scan))"
        " (opened (fn-cpo-open-observed config-records"
        "  (fn-bs-scan-frontier before-scan) events))"
        " (cfg (fn-cnode-config (fn-replay-result-node"
        "  (fn-cpr-replay config-records events))))"
        " (clock (fn-clock-observation 0 (fn-nntp-unix-dtn-ms {{unix_ms}}) 0 t))"
        " (decision (fn-own-operator-decision"
        "  (fn-oag-post-config cfg *fn-record-max-payload*) clock"
        "  (fn-sn-node (fn-sn-open-state opened))"
        "  '{msgid} '({group}) '{source}))").format(
            configs=config_octets,
            msgid=octets(message_id.encode("ascii")),
            group=octets(GROUP.encode("ascii")),
            source=octets(source))


if IMAGE_AVAILABLE:
    class NativeServedCrashModelTests(NativeCampaignMixin, unittest.TestCase):
        def assert_recovery_cut_image(self, before, store, cut):
            bridge = model_images.ModelBridge()
            try:
                bridge.call('(include-book "books/byte-store-observation-scan")')
                bridge.call('(include-book "books/codec-attach")')
                bridge.call('(include-book "books/byte-store-frame")')
                bridge.call('(include-book "books/byte-store-txn-name")')
                index = model_images.cut_index(cut.program,
                                               cut.model_name or cut.name,
                                               cut.occurrence)
                observed = bridge.value(
                    "(let* ((before {}) (physical {})"
                    " (run (fn-bs-run before (fn-sf-initial-state)"
                    " (fn-bs-recover-program) nil nil nil))"
                    " (cut-bs (car (nth {} run)))"
                    " (model-image (fn-bs-crash cut-bs nil))"
                    " (model-scan (fn-bs-scan-store model-image))"
                    " (physical-scan (fn-bs-scan-store physical))"
                    " (model-opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                    " 10000000 (fn-bs-scan-frontier model-scan)"
                    " (fn-bs-scan-records model-scan)))"
                    " (physical-opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                    " 10000000 (fn-bs-scan-frontier physical-scan)"
                    " (fn-bs-scan-records physical-scan))))"
                    " (list (equal (fn-bs-pending cut-bs) nil)"
                    "       (fn-bso-served-image-agree model-image physical)"
                    "       (equal (fn-bs-names model-image :transactions)"
                    "              (fn-bs-names physical :transactions))"
                    "       (fn-bs-scan-okp model-scan)"
                    "       (equal model-scan physical-scan)"
                    "       (equal model-opened physical-opened)))".format(
                        before, model_images.import_image(store), index))
                self.assertRegex(observed, r"\(T\s+T\s+T\s+T\s+T\s+T\)\s*$",
                                 "{} occurrence {}: {}".format(
                                     cut.name, cut.occurrence, observed))
            finally:
                bridge.close()

        def test_served_prepare_publish_finish_cuts(self):
            # Every native post cut is driven through the served owner.  A
            # named selector is evidence only if its byte-program coordinate
            # and physical image agree at the exact selected cut.
            names = tuple(cut.name for cut in native_cuts.POST_CUTS)
            selected = os.environ.get("FN_NATIVE_SERVED_CUT")
            if selected:
                names = (selected,)
            cuts = {cut.name: cut for cut in native_cuts.POST_CUTS}
            for name in names:
                with self.subTest(cut=name):
                    self.run_served_cut(cuts[name])

        def test_the_served_frame_is_the_injected_articles_not_anothers(self):
            # Teeth for the derivation: at record-written the frame on disk is
            # a prefix of no frame of a different source article, of the file
            # the operator handed the owner stored as read (the derivation
            # before injection), nor of this injection outside the bracketed
            # second.
            cut = next(c for c in native_cuts.POST_CUTS if c.name == "record-written")
            for label, claimed, skew in (("other article", "other", 0),
                                         ("file as read", "file", 0),
                                         ("other second", None, 100)):
                with self.subTest(label), self.assertRaisesRegex(
                        AssertionError, "prefix of no intended frame"):
                    self.run_served_cut(cut, claimed=claimed, skew=skew)

        def run_served_cut(self, cut, claimed=None, skew=0):
            """CLAIMED replaces what the differential is told was stored
            ("other": the injection of a different source; "file": the
            candidate file's octets as read), SKEW shifts the clock bracket."""
            name = cut.name
            with tempfile.TemporaryDirectory(prefix="fn-served-byte-") as scratch:
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
                    self.assertEqual(len(prior_names), 1)
                    before = model_images.import_image(node.store)
                    before_frontier = (node.store / "allocation-frontier.json").read_bytes()
                    before_marker = (node.store / "committed-history.json").read_bytes()
                    source = candidate.read_bytes()
                    if claimed == "other":
                        source = article(CANDIDATE_ID, "candidate", "interrupted bodY")
                    stored = (source if claimed == "file"
                              else served_stored_payload(node.store, CANDIDATE_ID, source))

                    owner = node.start_owner({"FN_NATIVE_POST_FAULT": name + ":kill"})
                    self.assertTrue(owner["ready"],
                                    node.stop_owner(owner) if not owner["ready"] else owner)
                    t0 = time.time()
                    result = node.post(CANDIDATE_ID, candidate)
                    t1 = time.time()
                    killed = node.stop_owner(owner)
                    self.assertEqual(killed["rc"], -9, (name, result, killed))
                    self.assertEqual(self.transaction_bytes(node.store).get(
                        next(iter(prior_names))), next(iter(prior_names.values())))
                    self.assert_observed_scan_is_program_image(
                        before, node.store, cut, prior_names,
                        sent=(CANDIDATE_ID, stored, (GROUP,), (t0 + skew, t1 + skew)),
                        before_frontier=before_frontier,
                        prior_frame=next(iter(prior_names.values())),
                        bridge_setup=SERVED_BRIDGE_SETUP,
                        before_marker=before_marker)

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
