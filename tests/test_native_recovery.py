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


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeRecoveryFidelityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-recovery-")
        self.base = Path(self.temporary.name)

    def tearDown(self):
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


if __name__ == "__main__":
    unittest.main()
