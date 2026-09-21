"""Source-pinned fresh native initializer and restart evidence.

The cut names below are the labels of fn-bsi-current-init-program from the
reviewed fresh-initializer packet.  This test does not claim its static map is
a general relation theorem: it checks that the native source offers every one
of those post-syscall cuts, exercises representative post-call EIO behavior,
and kills a real native child before reopening its on-disk image.
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


MODEL_CUTS = {
    "init-root-mkdir", "init-root-parent-fenced", "init-lock-created",
    "init-transactions-mkdir", "init-transactions-parent-fenced",
    "init-staging-mkdir", "init-staging-parent-fenced",
    "init-config-dir-mkdir", "init-config-dir-parent-fenced",
    "init-config-created", "init-config-written", "init-config-file-fenced",
    "init-config-linked", "init-config-root-fenced", "init-config-stage-unlinked",
    "init-history-created", "init-history-written", "init-history-file-fenced",
    "init-history-linked", "init-history-root-fenced", "init-history-stage-unlinked",
    "init-config-history-fenced",
    "init-frontier-created", "init-frontier-written", "init-frontier-file-fenced",
    "init-frontier-linked", "init-frontier-root-fenced", "init-frontier-stage-unlinked",
    "init-final-config-file-fenced", "init-final-config-record-file-fenced",
    "init-final-frontier-file-fenced", "init-transactions-fenced",
    "init-root-fenced", "init-parent-fenced",
}


class NativeInitializerSourceMapTests(unittest.TestCase):
    def test_source_map_exposes_each_current_initializer_model_cut(self):
        source = (ROOT / "host" / "native" / "io.lisp").read_text()
        block = re.search(r"\(defparameter \+fnn-init-model-cuts\+(.*?)\n\n;; These controls",
                          source, re.S)
        self.assertIsNotNone(block)
        native_cuts = set(re.findall(r'"(init-[^"]+)"', block.group(1)))
        self.assertEqual(native_cuts, MODEL_CUTS)
        # These source anchors establish that the table is attached to the
        # actual native init helper, rather than a sibling test routine.
        for anchor in ("(fnn-safe-directory (fnn-store-root store) t store",
                       "(fnn-init-cut store \"init-lock-created\")",
                       "(fnn-publish-initial-file store (fnn-config-path store) config \"init-config-\")",
                       "(fnn-publish-initial-file store (fnn-config-record-path store 1)",
                       "(fnn-publish-initial-file store (fnn-frontier-path store)",
                       "(fnn-init-cut store \"init-parent-fenced\")"):
            self.assertIn(anchor, source)


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeInitializerFidelityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-init-")
        self.base = Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def invoke(self, store, command, fault=None):
        env = dict(os.environ)
        env.pop("FN_NATIVE_INIT_FAULT", None)
        if fault is not None:
            env["FN_NATIVE_INIT_FAULT"] = fault
        return subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), command], cwd=ROOT,
            env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)

    def test_fresh_init_then_new_process_recover(self):
        store = self.base / "fresh"
        initialized = self.invoke(store, "init")
        self.assertEqual(initialized.returncode, run_store.EXIT_OK, initialized.stderr)
        self.assertTrue((store / "config.json").is_file())
        self.assertTrue((store / "config" / "00000001.cfg").is_file())
        self.assertTrue((store / "allocation-frontier.json").is_file())
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, run_store.EXIT_OK, recovered.stderr)
        self.assertIn(b"recovered transactions=0 articles=0", recovered.stdout)

    def test_post_history_fence_eio_is_a_real_source_cut_and_reopens(self):
        store = self.base / "eio"
        failed = self.invoke(store, "init", "init-config-history-fenced:eio")
        self.assertEqual(failed.returncode, run_store.EXIT_FAULT, failed.stderr)
        self.assertIn(b"Input/output error", failed.stderr)
        # The injection happens after the actual fsync returned.  This checks
        # source-cut routing only; it does not assert a platform EIO outcome.
        self.assertTrue((store / "config" / "00000001.cfg").is_file())
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_OK, reopened.stderr)

    def test_second_config_enumeration_fault_is_not_an_empty_history(self):
        store = self.base / "enumeration"
        failed = self.invoke(store, "init", "init-config-records-final-enumerate:eio")
        self.assertEqual(failed.returncode, run_store.EXIT_FAULT, failed.stderr)
        self.assertIn(b"Input/output error", failed.stderr)
        # Both publication helpers have run.  The injected error is before the
        # second directory enumeration, so a silent NIL conversion would have
        # continued to final barriers and reported a successful init instead.
        self.assertTrue((store / "config" / "00000001.cfg").is_file())
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_OK, reopened.stderr)

    def test_sigkill_at_history_fence_is_process_death_then_restart(self):
        store = self.base / "killed-history"
        killed = self.invoke(store, "init", "init-config-history-fenced:kill")
        self.assertLess(killed.returncode, 0, killed.stderr)
        self.assertEqual(-killed.returncode, 9)
        # This is a separate executable process.  It is deliberately not an
        # exception retry within fnn-initialize, whose unwind-protect could
        # erase the staging evidence before the restart.
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_OK, reopened.stderr)
        self.assertIn(b"recovered transactions=0 articles=0", reopened.stdout)

    def test_sigkill_before_metadata_makes_restart_fault(self):
        store = self.base / "killed-lock"
        killed = self.invoke(store, "init", "init-lock-created:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_FAULT, reopened.stderr)


if __name__ == "__main__":
    unittest.main()
