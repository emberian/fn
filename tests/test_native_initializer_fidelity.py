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
    "init-staging-mkdir", "init-staging-parent-fenced",
    "init-config-dir-mkdir", "init-config-dir-parent-fenced",
    "init-config-created", "init-config-written", "init-config-file-fenced",
    "init-config-linked", "init-config-link-eexist", "init-config-root-fenced", "init-config-stage-unlinked",
    "init-history-created", "init-history-written", "init-history-file-fenced",
    "init-history-linked", "init-history-link-eexist", "init-history-root-fenced", "init-history-stage-unlinked",
    "init-config-history-fenced",
    "init-final-config-file-fenced", "init-final-config-record-file-fenced",
    "init-root-fenced", "init-parent-fenced",
    # books/byte-store-log-initializer.lisp fn-bsi-log-init-program (format 9).
    "init-journal-mkdir", "init-journal-parent-fenced",
    "init-segment-created", "init-segment-written", "init-segment-file-fenced",
    "init-journal-segment-fenced",
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
                       "(fnn-log-init-segment store)",
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
        # Format 9 (books/byte-store-log-initializer.lisp): the segment, no
        # allocator file, no transactions/.
        segment = store / "journal" / "000001.log"
        self.assertTrue(segment.is_file())
        self.assertEqual(segment.read_bytes().count(0), segment.stat().st_size)
        self.assertFalse((store / "allocation-frontier.json").exists())
        self.assertFalse((store / "transactions").exists())
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
        self.assertFalse((store / "journal" / "000001.log").exists())
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
        # Format 9: the store is complete when its record log's segment is
        # (init's last step); before it the open faults naming the journal,
        # and init again completes the store.
        self.assert_incomplete_then_completed_by_init(store)

    def assert_incomplete_then_completed_by_init(self, store):
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_FAULT, reopened.stderr)
        self.assertIn(b"missing store directory", reopened.stderr)
        self.assertIn(b"journal", reopened.stderr)
        self.assertFalse((store / "journal" / "000001.log").exists())
        retried = self.invoke(store, "init")
        self.assertEqual(retried.returncode, run_store.EXIT_OK, retried.stderr)
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, run_store.EXIT_OK, recovered.stderr)
        self.assertIn(b"recovered transactions=0 articles=0", recovered.stdout)

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
        # Format 9: the segment (the store's last durable step) was made
        # before this enumeration, so the store the failed init leaves is
        # complete: a new process recovers it empty, and init again succeeds.
        self.assertTrue((store / "journal" / "000001.log").is_file())
        recovered = self.invoke(store, "recover")
        self.assertEqual(recovered.returncode, run_store.EXIT_OK, recovered.stderr)
        self.assertIn(b"recovered transactions=0 articles=0", recovered.stdout)
        self.assertEqual(self.invoke(store, "init").returncode, run_store.EXIT_OK)

    def test_sigkill_at_history_fence_is_process_death_then_faulted_restart(self):
        store = self.base / "killed-history"
        killed = self.invoke(store, "init", "init-config-history-fenced:kill")
        self.assertLess(killed.returncode, 0, killed.stderr)
        self.assertEqual(-killed.returncode, 9)
        # This is a separate executable process.  It is deliberately not an
        # exception retry within fnn-initialize, whose unwind-protect could
        # erase the staging evidence before the restart.
        self.assert_incomplete_then_completed_by_init(store)

    def test_sigkill_at_segment_created_is_completed_by_the_open(self):
        # Format 9 has no allocator file (init-final-frontier-file-fenced is
        # the per-file layout's cut).  A death just after the segment's
        # create (before its extent of zeros and its fence) leaves an empty
        # segment: the writable open completes it as it completes an
        # interrupted rotation (fnn-log-complete-rotation) and recovers the
        # store empty.
        store = self.base / "killed-segment-created"
        killed = self.invoke(store, "init", "init-segment-created:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        self.assertEqual((store / "journal" / "000001.log").stat().st_size, 0)
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_OK, reopened.stderr)
        self.assertIn(b"recovered transactions=0 articles=0", reopened.stdout)
        self.assertGreater((store / "journal" / "000001.log").stat().st_size, 0)

    def test_sigkill_after_the_segment_recovers_in_a_new_process(self):
        # Lane log-2: init's last cut is the fenced segment; the store is
        # complete and a new process recovers it empty.
        store = self.base / "killed-segment"
        killed = self.invoke(store, "init", "init-journal-segment-fenced:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_OK, reopened.stderr)
        self.assertIn(b"recovered transactions=0 articles=0", reopened.stdout)

    def test_sigkill_before_metadata_makes_restart_refuse_by_name(self):
        store = self.base / "killed-lock"
        killed = self.invoke(store, "init", "init-lock-created:kill")
        self.assertEqual(killed.returncode, -9, killed.stderr)
        # PKT-579 (books/store-mount-identity.lisp fn-smid-empty-root-is-refused):
        # a root with no filesystem record and no config.json is refused by
        # name before the structural checks that used to fault here; the
        # line names `init' again as the remedy.  Nothing is written.
        reopened = self.invoke(store, "recover")
        self.assertEqual(reopened.returncode, run_store.EXIT_REFUSED, reopened.stderr)
        self.assertIn(b"store filesystem unrecorded: ", reopened.stderr)
        self.assertIn(b"run init again if it was interrupted", reopened.stderr)
        self.assertFalse((store / "config.json").exists())
        retried = self.invoke(store, "init")
        self.assertEqual(retried.returncode, run_store.EXIT_OK, retried.stderr)
        self.assertEqual(self.invoke(store, "recover").returncode, run_store.EXIT_OK)


if __name__ == "__main__":
    unittest.main()
