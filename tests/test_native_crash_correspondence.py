"""Pin the native crash-model subject and its publication cut order.

This is a source transcription check, not a proof about Common Lisp or the
platform.  Its job is to make drift from the ACL2 correspondence book loud.
"""
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parent.parent


def function_body(source: str, name: str) -> str:
    start = source.index("(defun {} ".format(name))
    next_defun = source.find("\n(defun ", start + 1)
    return source[start:] if next_defun < 0 else source[start:next_defun]


class NativeCrashCorrespondenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.io = (ROOT / "host/native/io.lisp").read_text()
        cls.owner = (ROOT / "host/native/owner.lisp").read_text()
        cls.bridge = (ROOT / "host/store-node-host.lisp").read_text()

    def assert_ordered(self, body, tokens):
        positions = [body.index(token) for token in tokens]
        self.assertEqual(positions, sorted(positions), tokens)

    def test_actual_owner_calls_the_three_native_persistence_subjects(self):
        # The frontier advance stays in each committing arm; the publish and
        # the finish moved together into fnn-owner-publish-prepared, which
        # every arm calls after its advance.  Read the call, then the callee,
        # so the three subjects are still shown in order on every path: this
        # check had been red since that move and nothing ran it (found by
        # the owner-defects lane, 2026-09-22).
        for arm in ("fnn-owner-attempt", "fnn-owner-retention-commit",
                    "fnn-owner-identity-commit"):
            self.assert_ordered(function_body(self.owner, arm),
                                ["(fnn-advance-frontier ",
                                 "(fnn-owner-publish-prepared "])
        self.assert_ordered(function_body(self.owner, "fnn-owner-publish-prepared"),
                            ["(fnn-publish ", "(fnn-finish "])

    def test_store_post_calls_the_same_three_subjects(self):
        # The sibling entry the cut table used to be run through.  Its cuts
        # are the same fnn-at lines as the owner's because both entries call
        # these three functions; what differs is the ACL2 subject driving them
        # (the store-node bridge here, fn-owner there), which is why the
        # campaign now kills the served owner itself (campaign dabebb84, F1).
        self.assert_ordered(function_body(self.io, "fnn-command-post"),
                            ["(fnn-post-entry-fault inject)",
                             "(fnn-open-live-store root t fault)",
                             "(fnn-advance-frontier store ",
                             "(fnn-publish store ", "(fnn-finish store)"])

    def test_the_served_owner_is_armed_by_the_same_function(self):
        # `operator CFG run' reaches fnn-owner-run-normalized
        # (host/native/control.lisp fnn-control-owner-run-normalized); it and
        # the developer `owner run' verb hand fnn-owner-run the fault
        # fnn-post-entry-fault reads, which fnn-owner-install passes to the
        # store every fnn-at tests.
        normalized = function_body(self.owner, "fnn-owner-run-normalized")
        self.assertIn("(fnn-post-entry-fault nil)", normalized)
        self.assertNotRegex(normalized, r"max-connections\s+nil ")
        self.assertIn("(fnn-post-entry-fault", function_body(self.owner, "fnn-command-owner"))
        self.assertIn("(fnn-owner-install root max-connections fault)",
                      function_body(self.owner, "fnn-owner-run"))
        self.assertIn("(fnn-open-live-store root t fault)",
                      function_body(self.owner, "fnn-owner-install"))
        entry = function_body(self.io, "fnn-post-entry-fault")
        for reader in ("(fnn-post-test-fault)", "(fnn-recovery-test-fault)",
                       "+fnn-cli-faults+"):
            self.assertIn(reader, entry)

    def test_recovery_cuts_run_in_program_order_and_sweep_after_the_barriers(self):
        from tests.campaign import model_images, native_cuts
        native_cuts.verify_recovery_order()
        indices = [model_images.cut_index(cut.program, cut.model_name,
                                          cut.occurrence)
                   for cut in native_cuts.RECOVERY_CUTS
                   if cut.model_name == "recover-barrier"]
        self.assertEqual(len(indices), 5)
        self.assertEqual(indices, sorted(set(indices)))
        self.assert_ordered(function_body(self.io, "fnn-recover"), [
            "(fnn-at store :recover-replayed)",
            "(fnn-observe store :recovery-barrier :ok)",
            '(fnn-at store (intern (format nil "RECOVER-BARRIER-~d" ordinal) :keyword))',
            "(unless (eq phase :ready)",
            "(fnn-sweep-staging store)",
        ])
        self.assert_ordered(function_body(self.io, "fnn-sweep-staging"), [
            "(fnn-unlink (fnn-join (fnn-staging store) name))",
            "(fnn-at store :recovery-stage-unlinked)",
        ])

    def test_native_observation_wrapper_calls_composed_subject(self):
        body = function_body(self.bridge, "fn-store-sn-io")
        self.assertIn("(fn-sn-io ", body)

    def test_allocator_observations_and_cuts_follow_syscalls(self):
        body = function_body(self.io, "fnn-advance-frontier")
        self.assert_ordered(body, [
            "(fnn-observe store :start-frontier)",
            "(fnn-write-staged stage contents)",
            "(fnn-observe store :frontier-file :ok)",
            "(fnn-at store :frontier-staged-durable)",
            "(fnn-replace stage (fnn-frontier-path store))",
            "(fnn-at store :frontier-replaced)",
            "(fnn-observe store :frontier-replace :ok)",
            "(fnn-at store :frontier-attempted)",
            "(fnn-fsync-dir (fnn-store-root store))",
            "(fnn-at store :frontier-durable)",
            "(fnn-observe store :frontier-directory :ok)",
            "(fnn-at store :frontier-reserved)",
        ])

    def test_record_observations_and_cuts_follow_syscalls(self):
        body = function_body(self.io, "fnn-publish")
        self.assert_ordered(body, [
            "(fnn-write-staged stage data)",
            "(fnn-observe store :record-file :ok)",
            "(fnn-at store :record-staged-durable)",
            "(fnn-link stage final)",
            "(fnn-at store :record-linked)",
            "(fnn-observe store :record-link :ok)",
            "(fnn-at store :record-attempted)",
            "(fnn-fsync-dir (fnn-transactions store))",
            "(fnn-at store :record-durable)",
            "(fnn-observe store :record-directory :ok)",
            "(fnn-at store :record-completing)",
            "(fnn-at store :record-staging-cleaned)",
        ])

    def test_recovery_is_the_only_restart_entry(self):
        body = function_body(self.io, "fnn-open-live-store")
        self.assertIn("(fnn-recover store)", body)
        recover = function_body(self.io, "fnn-recover")
        self.assertEqual(len(re.findall(r"fnn-observe store :recovery-barrier :ok", recover)), 1)
        self.assertIn("(loop for barrier", recover)
        self.assertIn("for ordinal from 1", recover)


if __name__ == "__main__":
    unittest.main()
