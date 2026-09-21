"""Current native existing-store recovery observations.

The native recovery host calls the ACL2 store-sweep subject after replay and
the five recovery barriers.  These tests use a saved native image and separate
processes; they do not turn the older Python/native differential finding into
a claim about this source revision.
"""

import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", str(ROOT / "build" / "fn-host")))
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
import frame_bridge  # noqa: E402


def missing_enrollment_fixture():
    """Return transaction/frontier bytes produced entirely by ACL2."""
    bridge = frame_bridge.session()
    bridge.store.call('(include-book "books/hybrid-store")')
    bridge.store.call('(include-book "books/store-node")')
    transaction = bytes(bridge.call(
        "(let* ((msgid \"<missing-keyring@example.invalid>\")"
        " (source '(70 114 111 109 58 32 97 64 98 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 116 101 115 116 13 10 83 117 98 106 101 99 116 58 32 120 13 10 77 101 115 115 97 103 101 45 73 68 58 32 60 109 105 115 115 105 110 103 45 107 101 121 114 105 110 103 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10 120 13 10))"
        " (profile *fn-hsig-profile-tag*) (subject \"fixture-subject\")"
        " (record (fn-record-make 0 0 0 msgid source '(\"fn.test\")"
        "                         \"fixture-obligation\" subject \"fixture-release\" 2))"
        " (verdict (fn-stxe-make 0 0 0 msgid :verified '(1) 7 profile))"
        " (event (fn-stxa-make 0 0 0 7 profile"
        "                       (fn-record-string-octets subject)"
        "                       (fn-record-encode record)"
        "                       (fn-stxe-encode verdict))))"
        " (if (and (fn-stxa-bindsp event)"
        "          (fn-sn-observed-historyp 1 (list event))"
        "          (fn-sf-history-recoverablep '(\"fn.test\") 32 (list event) 1)"
        "          (equal (fn-stxk-context-kind (fn-replay-identity (list event)))"
        "                 :fault))"
        "     (fn-store-event-encode event) nil))"))
    if not transaction:
        raise AssertionError("fixture must pass article replay and fail identity replay")
    return bridge.store_frame(transaction), bridge.metadata_frontier_frame(1)


class NativeRecoverySourceMapTests(unittest.TestCase):
    def test_acquire_checks_staging_and_recovery_calls_the_acl2_sweep_subject(self):
        source = (ROOT / "host" / "native" / "io.lisp").read_text()
        acquire = re.search(r"\(defun fnn-acquire .*?\n\n\(defun fnn-store-close", source, re.S)
        self.assertIsNotNone(acquire)
        self.assertIn("(fnn-safe-directory (fnn-staging store))", acquire.group(0))
        recover = re.search(r"\(defun fnn-recover .*?\n\n\(defun fnn-require-writer", source, re.S)
        self.assertIsNotNone(recover)
        self.assertLess(recover.group(0).index("(fnn-sweep-staging store)"),
                        recover.group(0).index("(setf (fnn-store-fenced store) nil)"))
        self.assertIn("(fnn-bridge-sweep-staging observed)", source)
        self.assertIn("fn-store-sn-sweep-staging-list", source)
        self.assertIn("FN_NATIVE_RECOVERY_FAULT", source)

    def test_missing_enrollment_fixture_is_acl2_encoded_and_nonempty(self):
        try:
            transaction, frontier = missing_enrollment_fixture()
            decoded = frame_bridge.session().store_unframe(transaction)
            self.assertTrue(decoded.startswith(b"\x44fn-e"))
            self.assertTrue(frontier.startswith(b"FNSM"))
        finally:
            frame_bridge.close()


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeRecoveryFidelityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-recovery-")
        self.base = Path(self.temporary.name)

    def tearDown(self):
        frame_bridge.close()
        self.temporary.cleanup()

    def invoke(self, store, command, recovery_fault=None):
        env = dict(os.environ)
        env.pop("FN_NATIVE_INIT_FAULT", None)
        env.pop("FN_NATIVE_RECOVERY_FAULT", None)
        if recovery_fault is not None:
            env["FN_NATIVE_RECOVERY_FAULT"] = recovery_fault
        return subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), command], cwd=ROOT,
            env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)

    def initialized(self, name):
        store = self.base / name
        result = self.invoke(store, "init")
        self.assertEqual(result.returncode, run_store.EXIT_OK, result.stderr)
        return store

    def test_missing_staging_is_a_current_native_fault(self):
        store = self.initialized("missing-staging")
        (store / "staging").rmdir()
        result = self.invoke(store, "status")
        self.assertEqual(result.returncode, run_store.EXIT_FAULT, result.stderr)
        self.assertIn(b"missing store directory", result.stderr)

    def test_recover_removes_only_acl2_stage_names_and_preserves_unknown_names(self):
        store = self.initialized("policy")
        stage = store / "staging" / ".stage-interrupted"
        unknown = store / "staging" / ".operator-evidence"
        stage.write_bytes(b"staged but uncommitted")
        unknown.write_bytes(b"do not classify in raw Lisp")
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, run_store.EXIT_OK, recovered.stderr)
        self.assertFalse(stage.exists())
        self.assertTrue(unknown.exists())
        self.assertIn(b"staging-orphans=1 [.operator-evidence]", recovered.stdout)

    def test_over_limit_staging_namespace_faults_without_partial_sweep(self):
        store = self.initialized("over-limit")
        for number in range(65):
            (store / "staging" / ".stage-{:02d}".format(number)).write_bytes(b"x")
        result = self.invoke(store, "recover")
        self.assertEqual(result.returncode, run_store.EXIT_FAULT, result.stderr)
        self.assertIn(b"staging namespace exceeds ACL2 observation bound", result.stderr)
        self.assertEqual(len(list((store / "staging").iterdir())), 65)

    def test_post_unlink_eio_is_uncertain_then_a_new_process_recovers(self):
        store = self.initialized("post-unlink-eio")
        stage = store / "staging" / ".stage-post-unlink"
        stage.write_bytes(b"interrupted")
        failed = self.invoke(store, "recover", "recovery-stage-unlinked:eio")
        self.assertEqual(failed.returncode, run_store.EXIT_UNCERTAIN, failed.stderr)
        # The test seam runs after unlink.  It exercises source-cut routing;
        # it does not claim a platform EIO occurred after every successful unlink.
        self.assertFalse(stage.exists())
        restarted = self.invoke(store, "recover")
        self.assertEqual(restarted.returncode, run_store.EXIT_OK, restarted.stderr)
        self.assertIn(b"staging-orphans=0", restarted.stdout)

    def test_sigkill_after_one_unlink_restarts_and_reconciles_remaining_stage(self):
        store = self.initialized("post-unlink-kill")
        for suffix in ("a", "b"):
            (store / "staging" / ".stage-{}".format(suffix)).write_bytes(b"interrupted")
        killed = self.invoke(store, "recover", "recovery-stage-unlinked:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        self.assertEqual(len(list((store / "staging").iterdir())), 1)
        restarted = self.invoke(store, "recover")
        self.assertEqual(restarted.returncode, run_store.EXIT_OK, restarted.stderr)
        self.assertEqual(list((store / "staging").iterdir()), [])
        self.assertIn(b"staging-orphans=0", restarted.stdout)

    def test_atomic_hybrid_article_without_enrollment_faults_and_retains_bytes(self):
        """ACL2 emits kind-4 history whose missing kind-3 predecessor is fatal."""
        store = self.initialized("missing-hybrid-enrollment")
        transaction, frontier = missing_enrollment_fixture()
        transaction_path = store / "transactions" / "00000000000000000000.txn"
        frontier_path = store / "allocation-frontier.json"
        transaction_path.write_bytes(transaction)
        frontier_path.write_bytes(frontier)
        before_transaction = transaction_path.read_bytes()
        before_frontier = frontier_path.read_bytes()

        reopened = self.invoke(store, "status")
        self.assertEqual(reopened.returncode, run_store.EXIT_FAULT, reopened.stderr)
        self.assertIn(b"ACL2 replay rejected committed transaction history",
                      reopened.stderr)
        self.assertEqual(transaction_path.read_bytes(), before_transaction)
        self.assertEqual(frontier_path.read_bytes(), before_frontier)


if __name__ == "__main__":
    unittest.main()
