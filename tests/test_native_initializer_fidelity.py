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
import fcntl


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", str(ROOT / "build" / "fn-host")))
# A fault selector is a developer-image selector: a production image refuses
# to start with FN_NATIVE_INIT_FAULT in its environment (exit 5, host/native/io.lisp
# `fnn-developer-selector-gate'), so every faulted step runs this image.
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", str(ROOT / "build" / "fn-host-developer")))
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


MODEL_CUTS = {
    "init-root-mkdir", "init-root-parent-fenced", "init-lock-created",
    "init-transactions-mkdir", "init-transactions-parent-fenced",
    "init-staging-mkdir", "init-staging-parent-fenced",
    "init-config-dir-mkdir", "init-config-dir-parent-fenced",
    "init-config-created", "init-config-written", "init-config-file-fenced",
    "init-config-linked", "init-config-link-eexist", "init-config-root-fenced", "init-config-stage-unlinked",
    "init-history-created", "init-history-written", "init-history-file-fenced",
    "init-history-linked", "init-history-link-eexist", "init-history-root-fenced", "init-history-stage-unlinked",
    "init-config-history-fenced",
    "init-frontier-created", "init-frontier-written", "init-frontier-file-fenced",
    "init-frontier-linked", "init-frontier-link-eexist", "init-frontier-root-fenced", "init-frontier-stage-unlinked",
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
                       '(fnn-init-cut store (fnn-concat initializer-prefix "link-eexist"))',
                       "(fnn-init-cut store \"init-parent-fenced\")"):
            self.assertIn(anchor, source)
        config_names = re.search(r"\(defun fnn-config-record-names.*?\n\n\(defun fnn-config-records",
                                 source, re.S)
        self.assertIsNotNone(config_names)
        self.assertNotIn("handler-case", config_names.group(0))
        self.assertIn(":init-config-records-final-enumerate", source)
        self.assertIn(":fnn-test-config-no-read", source)


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
        image = IMAGE
        if fault is not None:
            if not (DEVELOPER.is_file() and os.access(DEVELOPER, os.X_OK)):
                self.skipTest(
                    "build/fn-host-developer (or FN_NATIVE_DEVELOPER_HOST) is "
                    "required: FN_NATIVE_INIT_FAULT is a developer-image selector and a "
                    "production image refuses to start with it")
            image = DEVELOPER
        return subprocess.run(
            [str(image), "--fn", "store", str(store), command], cwd=ROOT,
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

    def test_existing_valid_init_takes_actual_eexist_links_then_reopens(self):
        store = self.base / "existing"
        self.assertEqual(self.invoke(store, "init").returncode, run_store.EXIT_OK)
        # config.json and allocation-frontier.json are immutable link targets.
        # The second init stages/fences a candidate, receives real EEXIST at
        # both links, and retains the existing bytes for the later recover.
        repeated = self.invoke(store, "init")
        self.assertEqual(repeated.returncode, run_store.EXIT_OK, repeated.stderr)
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, run_store.EXIT_OK, recovered.stderr)

    def test_history_fenced_process_death_retries_through_config_eexist(self):
        store = self.base / "history-retry"
        killed = self.invoke(store, "init", "init-config-history-fenced:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        self.assertTrue((store / "config.json").is_file())
        self.assertTrue((store / "config" / "00000001.cfg").is_file())
        self.assertFalse((store / "allocation-frontier.json").exists())
        retried = self.invoke(store, "init")
        self.assertEqual(retried.returncode, run_store.EXIT_OK, retried.stderr)
        self.assertEqual(self.invoke(store, "recover").returncode, run_store.EXIT_OK)

    def test_sigkill_after_actual_config_eexist_leaves_existing_store_openable(self):
        store = self.base / "eexist-cut"
        self.assertEqual(self.invoke(store, "init").returncode, run_store.EXIT_OK)
        # The model cut is inside the EEXIST handler, after fnn-link returned.
        killed = self.invoke(store, "init", "init-config-link-eexist:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, run_store.EXIT_OK, recovered.stderr)

    def test_live_initializer_lock_refuses_second_initializer_before_metadata(self):
        store = self.base / "contended"
        store.mkdir(mode=0o700)
        lock_path = store / "writer.lock"
        with lock_path.open("wb") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            blocked = self.invoke(store, "init")
            self.assertEqual(blocked.returncode, run_store.EXIT_REFUSED, blocked.stderr)
            self.assertFalse((store / "config.json").exists())
        # The losing initializer created neither metadata nor a replacement
        # lock and a later owner can initialize the same namespace.
        initialized = self.invoke(store, "init")
        self.assertEqual(initialized.returncode, run_store.EXIT_OK, initialized.stderr)

    def test_post_history_fence_eio_stops_before_frontier_publication(self):
        store = self.base / "eio"
        failed = self.invoke(store, "init", "init-config-history-fenced:eio")
        self.assertEqual(failed.returncode, run_store.EXIT_FAULT, failed.stderr)
        self.assertIn(b"Input/output error", failed.stderr)
        # The injection happens after the actual fsync returned.  This checks
        # source-cut routing only; it does not assert a platform EIO outcome.
        self.assertTrue((store / "config" / "00000001.cfg").is_file())
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_FAULT, reopened.stderr)
        self.assertIn(b"allocation frontier", reopened.stderr)

    def test_second_config_enumeration_eacces_is_not_empty_history(self):
        store = self.base / "enumeration"
        config_dir = store / "config"
        try:
            failed = self.invoke(store, "init", "init-config-records-final-enumerate:eacces")
            self.assertEqual(failed.returncode, run_store.EXIT_FAULT, failed.stderr)
            # The test control removes directory access immediately before
            # fnn-list-directory.  EACCES therefore comes from that real call;
            # the former handler would have returned NIL and init would pass.
            self.assertEqual(config_dir.stat().st_mode & 0o777, 0)
        finally:
            if config_dir.exists():
                os.chmod(config_dir, 0o700)
        self.assertTrue((config_dir / "00000001.cfg").is_file())
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_OK, reopened.stderr)

    def test_sigkill_at_history_fence_is_process_death_then_faulted_restart(self):
        store = self.base / "killed-history"
        killed = self.invoke(store, "init", "init-config-history-fenced:kill")
        self.assertLess(killed.returncode, 0, killed.stderr)
        self.assertEqual(-killed.returncode, 9)
        # This is a separate executable process.  It is deliberately not an
        # exception retry within fnn-initialize, whose unwind-protect could
        # erase the staging evidence before the restart.
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_FAULT, reopened.stderr)
        self.assertIn(b"allocation frontier", reopened.stderr)

    def test_sigkill_after_frontier_publication_recovers_in_a_new_process(self):
        store = self.base / "killed-frontier"
        killed = self.invoke(store, "init", "init-final-frontier-file-fenced:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
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
