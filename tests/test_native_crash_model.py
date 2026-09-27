"""Actual native process death on the record log, checked through the image's scan
of the segment, the open, and the served octets (format 9)."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests import native_log_observation
from tests.campaign import native_cuts

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_CRASH_HOST", ""))
IMAGE_AVAILABLE = IMAGE.is_file() and os.access(IMAGE, os.X_OK)


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
    """Process deaths on the record log (format 9; lane log-recovery-mod).

    The per-file POST programs (fn-bs-frontier-program, fn-bs-record-program,
    fn-bs-marker-program) and their 23 cuts are not reachable on a format-9
    store: a POST is P-BATCH on the record log, whose cuts are
    native_cuts.POST_LOG_CUTS (log-written, log-fenced, and the member's two
    finish cuts).  At each cut the killed store's committed history -- the
    image's own scan of the segment (tests/native_log_observation.py: the
    records and the chained last trailer) -- is the prior history, or the
    prior history and the candidate, as the cut's column says (T2 of
    books/store-log-crash.lisp: a crash reads committed ++ a prefix of the
    batch; for a batch of one, old or new); P-LOG-RECOVER keeps exactly that
    history (it truncates only past the last complete entry); the prior is
    served as stored; the candidate is served whole exactly when it is in the
    history, and the client's retry is then a duplicate, else it commits.
    The byte-level model image of P-BATCH at every write boundary is the
    power-loss rig's (planning/evidence/commit-onto-log-2026-09-27.md
    section 4); this module checks the process-death cuts the native image
    names."""

    def invoke(self, store, command, *arguments, expected=0, env=None):
        host_env = dict(os.environ)
        host_env.pop("FN_NATIVE_POST_FAULT", None)
        host_env.pop("FN_NATIVE_LOG_FAULT", None)
        host_env.pop("FN_NATIVE_RECOVERY_FAULT", None)
        host_env.update(env or {})
        if command == "inspect" and arguments[:1] == ("--message-id",):
            arguments = arguments[1:]
        result = subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), command,
             *map(str, arguments)], cwd=ROOT, env=host_env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        if expected is not None:
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
    def history(store):
        return native_log_observation.committed_history(IMAGE, store, cwd=ROOT)

    def assert_cut_history(self, cut_name, candidate, prior, killed):
        """KILLED is PRIOR, or PRIOR and one record more, as CANDIDATE says."""
        self.assertIn(len(killed), {"absent": {len(prior)},
                                    "present": {len(prior) + 1},
                                    "either": {len(prior), len(prior) + 1}}[candidate],
                      (cut_name, prior, killed))
        if len(killed) == len(prior):
            self.assertEqual(killed, prior, cut_name)

    def run_post_log_cut(self, cut):
        with tempfile.TemporaryDirectory(prefix="fn-native-log-cut-") as tmp:
            root = Path(tmp); store = root / "store"
            prior = root / "prior"; prior.write_bytes(b"prior accepted protected content")
            candidate = root / "candidate"; candidate.write_bytes(b"candidate protected content")
            self.invoke(store, "init")
            self.invoke(store, "post", "<prior@example.invalid>", prior, "-", "-", "fn.letters")
            before = self.history(store)
            self.assertEqual(len(before), 1)
            env = dict(os.environ); env["FN_NATIVE_POST_FAULT"] = cut.name + ":kill"
            killed = self.native_post(store, "<candidate@example.invalid>", candidate, env)
            self.assertEqual(killed.returncode, -9, killed.stderr)
            at_cut = self.history(store)
            # `store post' commits a batch of one: the append and its barrier
            # precede the member's finish (POST_LOG_ONE_CANDIDATE).
            self.assert_cut_history(cut.name, native_cuts.POST_LOG_ONE_CANDIDATE[cut.name],
                                    before, at_cut)
            recovered = self.invoke(store, "recover")
            self.assertIn(b"articles=", recovered.stdout)
            self.assertEqual(self.history(store), at_cut, cut.name)
            inspected = self.invoke(store, "inspect", "--message-id", "<prior@example.invalid>")
            self.assertEqual(inspected.stdout, prior.read_bytes())
            present = len(at_cut) == 2
            shown = self.invoke(store, "inspect", "--message-id",
                                "<candidate@example.invalid>", expected=None)
            if present:
                self.assertEqual(shown.returncode, 0, shown.stderr)
                self.assertEqual(shown.stdout, candidate.read_bytes())
            else:
                self.assertNotEqual(shown.returncode, 0, cut.name)
            retry = self.invoke(store, "post", "<candidate@example.invalid>", candidate,
                                "-", "-", "fn.letters")
            self.assertIn(b"duplicate" if present else b"committed sequence=", retry.stdout,
                          cut.name)
            self.assertEqual(len(self.history(store)), 2)


# Runtime tests only exist when the caller supplies a source-matched executable.
# Absence is therefore zero runtime evidence, never a skipped passing campaign.
if IMAGE_AVAILABLE:
    class NativeCrashModelTests(NativeCampaignMixin, unittest.TestCase):
        def test_all_native_post_log_process_death_cuts(self):
            names = tuple(cut.name for cut in native_cuts.POST_LOG_CUTS)
            self.assertEqual(names, ("finish-consumed", "finish-durable",
                                     "log-written", "log-fenced"))
            for cut in native_cuts.POST_LOG_CUTS:
                selected = os.environ.get("FN_NATIVE_LOWLEVEL_CUT")
                if selected and cut.name != selected:
                    continue
                with self.subTest(cut=cut.name):
                    self.run_post_log_cut(cut)

        def test_recovery_log_cuts_reopen_the_same_history(self):
            # P-LOG-RECOVER's cuts (fnn-log-recover: log-truncated after the
            # tail's zero write, log-recovered after its barrier) and the
            # staging sweep's: a death at each leaves the history the next
            # open reads, and that open completes.  A torn candidate is left
            # first (a death at log-written of a batch of one).
            for label, env in (("log-truncated", {"FN_NATIVE_LOG_FAULT": "log-truncated"}),
                               ("log-recovered", {"FN_NATIVE_LOG_FAULT": "log-recovered"}),
                               ("recovery-stage-unlinked",
                                {"FN_NATIVE_RECOVERY_FAULT": "recovery-stage-unlinked:kill"})):
                with self.subTest(cut=label), tempfile.TemporaryDirectory(
                        prefix="fn-native-recovery-cut-") as tmp:
                    root = Path(tmp); store = root / "store"
                    prior = root / "prior"; prior.write_bytes(b"prior recovery content")
                    candidate = root / "candidate"; candidate.write_bytes(b"orphan candidate")
                    self.invoke(store, "init")
                    self.invoke(store, "post", "<prior-recovery@example.invalid>",
                                prior, "-", "-", "fn.letters")
                    before = self.history(store)
                    post_env = dict(os.environ)
                    post_env["FN_NATIVE_POST_FAULT"] = "log-written:kill"
                    killed = self.native_post(store, "<orphan@example.invalid>", candidate,
                                              post_env)
                    self.assertEqual(killed.returncode, -9, killed.stderr)
                    at_cut = self.history(store)
                    self.assert_cut_history("log-written", "either", before, at_cut)
                    if label == "recovery-stage-unlinked":
                        (store / "staging" / ".stage-a").write_bytes(b"interrupted")
                        (store / "staging" / ".stage-b").write_bytes(b"interrupted")
                    killed_recovery = self.invoke(store, "recover", env=env, expected=None)
                    self.assertEqual(killed_recovery.returncode, -9, killed_recovery.stderr)
                    self.assertEqual(self.history(store), at_cut, label)
                    self.invoke(store, "recover")
                    self.assertEqual(self.history(store), at_cut, label)
                    self.assertEqual(list((store / "staging").glob(".stage-*")), [])
                    inspected = self.invoke(store, "inspect", "--message-id",
                                            "<prior-recovery@example.invalid>")
                    self.assertEqual(inspected.stdout, prior.read_bytes())

        def test_injected_outcomes_stay_refused_or_uncertain_and_recover(self):
            # The CLI's injected outcomes on the log route (host/native/io.lisp
            # +fnn-cli-faults+): postpublish arms log-fenced (the record
            # durable, the answer uncertain), recordbarrier fails the batch's
            # write (uncertain).  prepublish and frontierbarrier name steps of
            # the per-file programs (the record stage, the frontier file) the
            # log route does not run; they are retired with them.
            cases = (("postpublish", 3), ("recordbarrier", 3))
            for inject, expected in cases:
                with self.subTest(inject=inject), tempfile.TemporaryDirectory(
                        prefix="fn-native-eio-") as tmp:
                    root = Path(tmp); store = root / "store"
                    prior = root / "prior"; prior.write_bytes(b"prior")
                    candidate = root / "candidate"; candidate.write_bytes(b"candidate")
                    self.invoke(store, "init")
                    self.invoke(store, "post", "<prior-eio@example.invalid>",
                                prior, "-", "-", "fn.letters")
                    before = self.history(store)
                    self.invoke(store, "post", "<candidate-eio@example.invalid>",
                                candidate, "-", inject, "fn.letters", expected=expected)
                    after = self.history(store)
                    self.assert_cut_history(inject, "either", before, after)
                    self.invoke(store, "recover")
                    self.assertEqual(self.history(store), after)


if __name__ == "__main__":
    if not IMAGE_AVAILABLE:
        raise SystemExit("FN_NATIVE_CRASH_HOST must name a source-matched developer image")
    unittest.main()
