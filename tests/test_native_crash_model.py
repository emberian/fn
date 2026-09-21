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
        self.assertIn("(fnn-developer-image-p)", body)
        self.assertIn("FN_NATIVE_POST_FAULT requires a developer image", body)

    def test_every_native_cut_has_a_byte_program_coordinate(self):
        native_cuts.verify_native_cut_map()

    def test_missing_image_is_not_reported_as_a_skipped_campaign(self):
        self.assertEqual("NativeCrashModelTests" in globals(), IMAGE_AVAILABLE)
        self.assertFalse(getattr(NativeCampaignMixin, "__unittest_skip__", False))


class NativeCampaignMixin:
    def invoke(self, store, command, *arguments, expected=0, env=None):
        host_env = dict(os.environ)
        host_env.update(env or {})
        host_env["FN_HOST"] = "native"
        host_env["FN_NATIVE_HOST"] = str(IMAGE)
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store),
             command, *map(str, arguments)], cwd=ROOT, env=host_env,
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

    def assert_observed_scan_is_program_image(self, before_form, store, cut):
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
            bridge.call("(defun fn-native-visible-choices (ops unit)"
                        " (if (atom ops) nil"
                        "  (cons (if (equal (car (car ops)) :write)"
                        "            (fn-bs-all-new (fn-bs-unit-count"
                        "             (nth 2 (car ops)) (len (nth 3 (car ops))) unit))"
                        "          :apply)"
                        "        (fn-native-visible-choices (cdr ops) unit))))")
            bridge.call("(defconst *fn-native-before* {})".format(before_form))
            bridge.call("(defconst *fn-native-before-scan*"
                        " (fn-bs-scan-store *fn-native-before*))")
            bridge.call("(defconst *fn-native-open*"
                        " (fn-sn-open-observed '(\"fn.letters\" \"fn.test\") 10000000"
                        "  (fn-bs-scan-frontier *fn-native-before-scan*)"
                        "  (fn-bs-scan-records *fn-native-before-scan*)))")
            bridge.call("(defconst *fn-native-ks*"
                        " (fn-sn-files (fn-sn-open-state *fn-native-open*)))")
            frontier = (store / "allocation-frontier.json").read_bytes()
            stages = sorted((store / "staging").glob(".allocation-*"))
            next_frontier = stages[0].read_bytes() if stages else frontier
            frontier_program = "(fn-bs-frontier-program \".native-campaign\" '{} )".format(
                tuple(next_frontier)).replace(",", "").replace("'(", "'(")
            # Python tuple formatting is not ACL2 syntax for singleton/empty;
            # byte lists here are nonempty, and spaces plus parentheses suffice.
            frontier_program = "(fn-bs-frontier-program \".native-campaign\" '({}))".format(
                " ".join(str(x) for x in next_frontier))
            bridge.call("(defconst *fn-native-frontier-run*"
                        " (fn-bs-run *fn-native-before* *fn-native-ks* {} nil"
                        "  '(\"fn.letters\" \"fn.test\") 10000000))".format(frontier_program))
            if cut.program == "fn-bs-frontier-program":
                index = model_images.cut_index(cut.program, cut.name)
                bridge.call("(defconst *fn-native-cut-bs*"
                            " (car (nth {} *fn-native-frontier-run*)))".format(index))
            else:
                bridge.call("(defconst *fn-native-after-frontier*"
                            " (car (car (last *fn-native-frontier-run*))))")
                bridge.call("(defconst *fn-native-reserved*"
                            " (cdr (car (last *fn-native-frontier-run*))))")
                txns = self.transaction_bytes(store)
                candidate_frame = txns.get("00000000000000000001.txn")
                if candidate_frame is None:
                    candidates = sorted((store / "staging").glob(".stage-*"))
                    self.assertTrue(candidates, "candidate frame absent from final and staging names")
                    candidate_frame = candidates[0].read_bytes()
                octets = " ".join(str(x) for x in candidate_frame)
                bridge.call("(defconst *fn-native-candidate*"
                            " (fn-bs-record-of-octets '({})))".format(octets))
                bridge.call("(defconst *fn-native-prepared*"
                            " (fn-sf-prepare-record *fn-native-reserved*"
                            "  *fn-native-candidate* '(\"fn.letters\" \"fn.test\") 10000000))")
                record_program = "(fn-bs-record-program \".stage-native\""
                record_program += " \"00000000000000000001.txn\" '({}))".format(octets)
                bridge.call("(defconst *fn-native-record-run*"
                            " (fn-bs-run *fn-native-after-frontier* *fn-native-prepared* {} nil"
                            "  '(\"fn.letters\" \"fn.test\") 10000000))".format(record_program))
                if cut.program == "fn-bs-record-program":
                    index = model_images.cut_index(cut.program, cut.name)
                    bridge.call("(defconst *fn-native-cut-bs*"
                                " (car (nth {} *fn-native-record-run*)))".format(index))
                else:
                    bridge.call("(defconst *fn-native-after-record*"
                                " (car (car (last *fn-native-record-run*))))")
                    bridge.call("(defconst *fn-native-completing*"
                                " (cdr (car (last *fn-native-record-run*))))")
                    finish = "(fn-bs-finish-program 1 1)"
                    bridge.call("(defconst *fn-native-finish-run*"
                                " (fn-bs-run *fn-native-after-record* *fn-native-completing*"
                                "  {} nil '(\"fn.letters\" \"fn.test\") 10000000))".format(finish))
                    index = model_images.cut_index(cut.program, cut.name)
                    bridge.call("(defconst *fn-native-cut-bs*"
                                " (car (nth {} *fn-native-finish-run*)))".format(index))
            bridge.call("(defconst *fn-native-observed* {})".format(
                model_images.import_image(store)))
            observed = bridge.value(
                "(let* ((choices (fn-native-visible-choices"
                "                  (fn-bs-pending *fn-native-cut-bs*)"
                "                  (fn-bs-unit *fn-native-cut-bs*)))"
                "       (model-image (fn-bs-crash *fn-native-cut-bs* choices))"
                "       (scan (fn-bs-scan-store *fn-native-observed*))"
                "       (opened (fn-sn-open-observed '(\"fn.letters\" \"fn.test\")"
                "                 10000000 (fn-bs-scan-frontier scan)"
                "                 (fn-bs-scan-records scan))))"
                "  (list (fn-bs-scan-okp scan) (fn-sn-open-okp opened)"
                "        (equal scan (fn-bs-scan-store model-image))))")
            self.assertRegex(observed, r"\(T\s+T\s+T\)\s*$", observed)
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
            self.assert_observed_scan_is_program_image(before_form, store, cut)
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
