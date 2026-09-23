"""Actual native process death checked through byte scan/open and cut programs."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from tests.campaign import model_images, native_cuts

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_CRASH_HOST", ""))
IMAGE_AVAILABLE = IMAGE.is_file() and os.access(IMAGE, os.X_OK)
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


class NativeCrashFaultSurfaceTests(unittest.TestCase):
    def test_post_fault_environment_is_developer_image_only(self):
        source = (ROOT / "host/native/io.lisp").read_text()
        start = source.index("(defun fnn-post-test-fault")
        end = source.index("\n(defun fnn-command-post", start)
        body = source[start:end]
        # Read through the accessor that answers NIL on a production image;
        # a production image refuses to start with the variable set
        # (`fnn-developer-selector-gate', run by fnn-main before dispatch).
        self.assertIn('(fnn-developer-selector "FN_NATIVE_POST_FAULT")', body)
        self.assertNotIn("posix-getenv", body)
        main = source[source.index("(defun fnn-main ()"):]
        self.assertLess(main.index("(fnn-developer-selector-gate argv)"),
                        main.index("(fnn-dispatch argv)"))

    def test_every_native_cut_has_a_byte_program_coordinate(self):
        native_cuts.verify_native_cut_map()

    def test_missing_image_is_not_reported_as_a_skipped_campaign(self):
        self.assertEqual("NativeCrashModelTests" in globals(), IMAGE_AVAILABLE)
        self.assertFalse(getattr(NativeCampaignMixin, "__unittest_skip__", False))


class NativeCampaignMixin:
    def invoke(self, store, command, *arguments, expected=0, env=None):
        host_env = dict(os.environ)
        host_env.update(env or {})
        if command == "inspect" and arguments[:1] == ("--message-id",):
            arguments = arguments[1:]
        result = subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), command,
             *map(str, arguments)], cwd=ROOT, env=host_env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(result.returncode, expected,
                         "stdout={}\nstderr={}".format(result.stdout, result.stderr))
        return result

    def native_post(self, store, message_id, payload, env):
        return subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), "post",
             message_id, str(payload), "-", "-", "fn.letters"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False)

    @staticmethod
    def transaction_bytes(store):
        return {p.name: p.read_bytes()
                for p in sorted((store / "transactions").iterdir()) if p.is_file()}

    def assert_observed_scan_is_program_image(self, before_form, store, cut,
                                              prior_names=()):
        """Compare exact scan values with the model's process-death image.

        SIGKILL does not simulate loss of dirty kernel state.  Therefore the
        model choice used here applies every issued entry operation and keeps
        every pending write new.  This checks that the observed namespace and
        decoded event sequence are an allowed model image without making a
        power-loss claim.
        """
        bridge = model_images.ModelBridge()
        try:
            bridge.call('(include-book "books/byte-store-keystones")')
            bridge.call('(include-book "books/byte-store-observation-scan")')
            bridge.call('(include-book "books/codec-attach")')
            bridge.call('(include-book "books/byte-store-frame")')
            bridge.call('(include-book "books/byte-store-txn-name")')
            bridge.call("(defun fn-native-visible-choices (ops unit)"
                        " (if (atom ops) nil"
                        "  (cons (if (equal (car (car ops)) :write)"
                        "            (fn-bs-all-new (fn-bs-unit-count"
                        "             (nth 2 (car ops)) (len (nth 3 (car ops))) unit))"
                        "          :apply)"
                        "        (fn-native-visible-choices (cdr ops) unit))))")
            bindings = ["(before {})".format(before_form),
                        "(before-scan (fn-bs-scan-store before))",
                        "(opened-before (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                        " 10000000 (fn-bs-scan-frontier before-scan)"
                        " (fn-bs-scan-records before-scan)))",
                        "(ks (fn-sn-files (fn-sn-open-state opened-before)))"]
            frontier = (store / "allocation-frontier.json").read_bytes()
            stages = sorted((store / "staging").glob(".allocation-*"))
            next_frontier = stages[0].read_bytes() if stages else frontier
            frontier_stage = stages[0].name if stages else ".allocation-campaign"
            # The program receives exact frontier octets observed at this cut.
            frontier_program = "(fn-bs-frontier-program \"{}\" '({}))".format(
                frontier_stage, " ".join(str(x) for x in next_frontier))
            bindings.append("(frontier-run (fn-bs-run before ks {} nil"
                            " '(\"fn.letters\" \"fn.test\") 10000000))".format(
                                frontier_program))
            if cut.program == "fn-bs-frontier-program":
                index = model_images.cut_index(cut.program,
                                               cut.model_name or cut.name,
                                               cut.occurrence)
                bindings.append("(cut-bs (car (nth {} frontier-run)))".format(index))
            else:
                bindings.extend(["(after-frontier (car (car (last frontier-run))))",
                                 "(reserved (cdr (car (last frontier-run))))"])
                txns = self.transaction_bytes(store)
                candidate_names = sorted(set(txns).difference(prior_names))
                candidate_frame = txns[candidate_names[0]] if candidate_names else None
                candidates = sorted((store / "staging").glob(".stage-*"))
                if candidate_frame is None:
                    self.assertTrue(candidates, "candidate frame absent from final and staging names")
                    candidate_frame = candidates[0].read_bytes()
                record_stage = candidates[0].name if candidates else ".stage-campaign"
                octets = " ".join(str(x) for x in candidate_frame)
                bindings.append("(candidate-record (fn-bs-record-of-octets '({})))".format(octets))
                bindings.append("(prepared (fn-sf-prepare-record reserved"
                                " candidate-record '(\"fn.letters\" \"fn.test\") 10000000))")
                next_name = "{:020d}.txn".format(len(prior_names))
                record_program = "(fn-bs-record-program \"{}\"".format(record_stage)
                record_program += " \"{}\" '({}))".format(next_name, octets)
                bindings.append("(record-run (fn-bs-run after-frontier prepared {} nil"
                                " '(\"fn.letters\" \"fn.test\") 10000000))".format(
                                    record_program))
                if cut.program == "fn-bs-record-program":
                    index = model_images.cut_index(cut.program, cut.name)
                    bindings.append("(cut-bs (car (nth {} record-run)))".format(index))
                else:
                    bindings.extend(["(after-record (car (car (last record-run))))",
                                     "(completing (cdr (car (last record-run))))"])
                    finish = "(fn-bs-finish-program {} {})".format(
                        len(prior_names), len(prior_names))
                    bindings.append("(finish-run (fn-bs-run after-record completing"
                                    " {} nil '(\"fn.letters\" \"fn.test\") 10000000))".format(finish))
                    index = model_images.cut_index(cut.program,
                                                   cut.model_name or cut.name,
                                                   cut.occurrence)
                    bindings.append("(cut-bs (car (nth {} finish-run)))".format(index))
            bindings.extend([
                "(observed {})".format(model_images.import_image(store)),
                "(choices (fn-native-visible-choices (fn-bs-pending cut-bs) (fn-bs-unit cut-bs)))",
                "(model-image (fn-bs-crash cut-bs choices))",
                "(scan (fn-bs-scan-store observed))",
                "(opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                " 10000000 (fn-bs-scan-frontier scan) (fn-bs-scan-records scan)))",
            ])
            observed = bridge.value(
                "(let* ({} ) (list"
                " (fn-bs-crash-choicesp choices (fn-bs-pending cut-bs) (fn-bs-unit cut-bs))"
                " (fn-bs-scan-okp scan) (fn-sn-open-okp opened)"
                " (fn-bso-served-image-agree model-image observed)"
                " (equal (fn-bs-names model-image :transactions)"
                "        (fn-bs-names observed :transactions))"
                " (fn-bs-scan-okp (fn-bs-scan-store model-image))"
                " (equal (fn-bs-scan-store model-image) scan)"
                " (list (fn-bso-directory-agree model-image observed :root)"
                "       (fn-bso-directory-agree model-image observed :transactions)"
                "       (fn-bso-directory-agree model-image observed :staging)"
                "       (fn-bs-names model-image :staging)"
                "       (fn-bs-names observed :staging))))".format(
                    " ".join(bindings)))
            self.assertRegex(observed, r"\(T\s+T\s+T\s+T\s+T\s+T\s+T\s+\(T\s+T\s+T",
                             "{}: {}".format(cut.name, observed))
        finally:
            bridge.close()

    def run_post_cut(self, cut):
        with tempfile.TemporaryDirectory(prefix="fn-native-cut-") as tmp:
            root = Path(tmp); store = root / "store"
            prior = root / "prior"; prior.write_bytes(b"prior accepted protected content")
            candidate = root / "candidate"; candidate.write_bytes(b"candidate protected content")
            self.invoke(store, "init")
            self.invoke(store, "post", "<prior@example.invalid>", prior, "-", "-", "fn.letters")
            before_form = model_images.import_image(store)
            prior_frames = self.transaction_bytes(store)
            self.assertEqual(len(prior_frames), 1)
            env = dict(os.environ); env["FN_NATIVE_POST_FAULT"] = cut.name + ":kill"
            killed = self.native_post(store, "<candidate@example.invalid>", candidate, env)
            self.assertEqual(killed.returncode, -9, killed.stderr)
            killed_frames = self.transaction_bytes(store)
            self.assertEqual(killed_frames.get(next(iter(prior_frames))),
                             next(iter(prior_frames.values())))
            self.assert_observed_scan_is_program_image(before_form, store, cut,
                                                       prior_frames)
            recovered = self.invoke(store, "recover")
            self.assertIn(b"articles=", recovered.stdout)
            self.assertEqual(self.transaction_bytes(store), killed_frames)
            inspected = self.invoke(store, "inspect", "--message-id",
                                    "<prior@example.invalid>")
            self.assertEqual(inspected.stdout, prior.read_bytes())
            candidate_present = len(killed_frames) == 2
            self.assertIn(candidate_present, {"absent": {False}, "present": {True},
                                               "either": {False, True}}[cut.candidate])


# Runtime tests only exist when the caller supplies a source-matched executable.
# Absence is therefore zero runtime evidence, never a skipped passing campaign.
if IMAGE_AVAILABLE:
    class NativeCrashModelTests(NativeCampaignMixin, unittest.TestCase):
        def test_all_native_post_process_death_cuts(self):
            for cut in native_cuts.POST_CUTS:
                selected = os.environ.get("FN_NATIVE_LOWLEVEL_CUT")
                if selected and cut.name != selected:
                    continue
                with self.subTest(cut=cut.name):
                    self.run_post_cut(cut)

        def test_recovery_stage_unlink_process_death_scans_and_reopens(self):
            with tempfile.TemporaryDirectory(prefix="fn-native-recovery-cut-") as tmp:
                root = Path(tmp); store = root / "store"
                prior = root / "prior"; prior.write_bytes(b"prior recovery content")
                candidate = root / "candidate"; candidate.write_bytes(b"orphan candidate")
                self.invoke(store, "init")
                self.invoke(store, "post", "<prior-recovery@example.invalid>",
                            prior, "-", "-", "fn.letters")
                prior_frames = self.transaction_bytes(store)
                env = dict(os.environ)
                env["FN_NATIVE_POST_FAULT"] = "record-staged-durable:kill"
                killed = self.native_post(store, "<orphan@example.invalid>", candidate, env)
                self.assertEqual(killed.returncode, -9, killed.stderr)
                self.assertTrue(list((store / "staging").glob(".stage-*")))
                recover_env = dict(os.environ)
                recover_env["FN_NATIVE_RECOVERY_FAULT"] = "recovery-stage-unlinked:kill"
                killed_recovery = subprocess.run(
                    [str(IMAGE), "--fn", "store", str(store), "recover"],
                    cwd=ROOT, env=recover_env, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, check=False)
                self.assertEqual(killed_recovery.returncode, -9, killed_recovery.stderr)
                self.assertFalse(list((store / "staging").glob(".stage-*")))
                bridge = model_images.ModelBridge()
                try:
                    bridge.call('(include-book "books/byte-store-keystones")')
                    bridge.call('(include-book "books/codec-attach")')
                    bridge.call('(include-book "books/byte-store-frame")')
                    bridge.call('(include-book "books/byte-store-txn-name")')
                    bridge.call("(defconst *fn-native-recovery-observed* {})".format(
                        model_images.import_image(store)))
                    value = bridge.value(
                        "(let* ((scan (fn-bs-scan-store *fn-native-recovery-observed*))"
                        " (opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                        "  10000000 (fn-bs-scan-frontier scan)"
                        "  (fn-bs-scan-records scan))))"
                        " (list (fn-bs-scan-okp scan) (fn-sn-open-okp opened)))")
                    self.assertRegex(value, r"\(T\s+T\)\s*$", value)
                finally:
                    bridge.close()
                self.invoke(store, "recover")
                self.assertEqual(self.transaction_bytes(store), prior_frames)
                inspected = self.invoke(store, "inspect", "--message-id",
                                        "<prior-recovery@example.invalid>")
                self.assertEqual(inspected.stdout, prior.read_bytes())

        def test_injected_outcomes_stay_refused_or_uncertain_and_recover(self):
            cases = (("prepublish", 1), ("postpublish", 3),
                     ("frontierbarrier", 3), ("recordbarrier", 3))
            for inject, expected in cases:
                with self.subTest(inject=inject), tempfile.TemporaryDirectory(
                        prefix="fn-native-eio-") as tmp:
                    root = Path(tmp); store = root / "store"
                    prior = root / "prior"; prior.write_bytes(b"prior")
                    candidate = root / "candidate"; candidate.write_bytes(b"candidate")
                    self.invoke(store, "init")
                    self.invoke(store, "post", "<prior-eio@example.invalid>",
                                prior, "-", "-", "fn.letters")
                    prior_frames = self.transaction_bytes(store)
                    self.invoke(store, "post", "<candidate-eio@example.invalid>",
                                candidate, "-", inject, "fn.letters", expected=expected)
                    after = self.transaction_bytes(store)
                    self.assertEqual(after.get(next(iter(prior_frames))),
                                     next(iter(prior_frames.values())))
                    self.invoke(store, "recover")
                    self.assertEqual(self.transaction_bytes(store), after)


if __name__ == "__main__":
    if not IMAGE_AVAILABLE:
        raise SystemExit("FN_NATIVE_CRASH_HOST must name a source-matched developer image")
    unittest.main()
