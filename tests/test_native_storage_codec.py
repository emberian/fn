"""Native store evidence for the ACL2-owned metadata codec (format 9).

The per-file allocator and transaction namespace (allocation-frontier.json,
transactions/NNN.txn) are not read by a format-9 store: its history and its
frontier are the record log's (books/store-log*.lisp).  The cases that
exercised them -- the Python/native cross-open of per-file stores, the
frontier file's maximum and barrier, the file name bound to the record's
sequence, the frontier frame refusals -- are retired with that layout (lane
log-recovery-mod); the configuration namespace, the profile frame and the
injected commit outcomes stay."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", str(ROOT / "build" / "fn-host-developer")))
sys.path.insert(0, str(ROOT / "tools"))
import frame_bridge  # noqa: E402
import run_store  # noqa: E402


def host_env(native):
    env = dict(os.environ)
    if native:
        env["FN_HOST"] = "native"
        env["FN_NATIVE_HOST"] = str(IMAGE)
    else:
        env.pop("FN_HOST", None)
        env.pop("FN_NATIVE_HOST", None)
    return env


class NativeConfigNamespaceSourceTests(unittest.TestCase):
    def test_native_config_scan_is_bounded_and_acl2_bound(self):
        source = (ROOT / "host" / "native" / "io.lisp").read_text()
        block = source[source.index("(defun fnn-config-record-observation"):
                       source.index("(defun fnn-open-lock")]
        self.assertIn("fnn-list-directory-bounded", block)
        self.assertIn("fnn-bridge-config-observation-limit", block)
        self.assertIn("fnn-bridge-config-observation", block)
        self.assertIn("fnn-check-regular", block)
        self.assertNotIn("remove-if-not", block)
        self.assertNotIn("fnn-list-directory (fnn-config-dir", block)
        model = (ROOT / "books" / "native-config-observation.lisp").read_text()
        self.assertIn("fn-cfg-decode-exact", model)
        self.assertIn("fn-cfg-record-generation", model)
        self.assertIn("fn-native-admin-config-name", model)
        self.assertIn("fn-nco-canonical-contiguousp", model)


class NativeTransactionNamespaceSourceTests(unittest.TestCase):
    def test_native_scan_uses_bounded_acl2_transaction_observation(self):
        source = (ROOT / "host" / "native" / "io.lisp").read_text()
        block = source[source.index("(defun fnn-transaction-files"):
                       source.index("(defun fnn-staging-observation")]
        self.assertIn("fnn-list-directory-bounded", block)
        self.assertIn("fnn-bridge-transaction-observation", block)
        self.assertNotIn("fnn-list-directory (fnn-transactions", block)
        self.assertNotIn("parse-integer", block)
        self.assertNotIn("fnn-seq-name-p", block)
        bridge = source[source.index("(defun fnn-bridge-transaction-observation"):
                        source.index("(defun fnn-bridge-staging-observation-limit")]
        self.assertIn("fn-store-txn-observation", bridge)
        model = (ROOT / "books" / "byte-store-scan.lisp").read_text()
        self.assertIn("(defun fn-bs-txn-observation-pairs", model)


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host-developer is required for raw Store fixtures")
class NativeStorageCodecTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-metadata-")
        self.base = Path(self.temporary.name)
        self.payload = self.base / "payload"
        self.payload.write_bytes(b"native metadata")

    def tearDown(self):
        frame_bridge.close()
        self.temporary.cleanup()

    def invoke(self, native, store, command, *arguments, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store),
             command, *map(str, arguments)], cwd=ROOT, env=host_env(native),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(
            result.returncode, expected,
            "{} host {} returned {}\nstdout={}\nstderr={}".format(
                "native" if native else "python", command, result.returncode,
                result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result

    @staticmethod
    def post_arguments(message_id):
        return ("--message-id", message_id, "--payload", "PAYLOAD",
                "--group", "fn.letters")

    def post(self, native, store, message_id, expected=0):
        arguments = list(self.post_arguments(message_id))
        arguments[3] = self.payload
        return self.invoke(native, store, "post", *arguments, expected=expected)

    def direct_native_post(self, store, message_id, fault, expected):
        result = subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), "post", message_id,
             str(self.payload), "-", fault, "fn.letters"], cwd=ROOT,
            env=host_env(True), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False)
        self.assertEqual(result.returncode, expected, result.stderr.decode("utf-8", "replace"))
        return result

    def test_native_config_namespace_refuses_mismatched_name_and_symlink(self):
        store = self.base / "config-namespace"
        self.invoke(True, store, "init")
        config_dir = store / "config"
        generation_one = config_dir / "00000001.cfg"

        # The bytes decode to generation 1 but their observed basename claims
        # generation 2.  Recovery must fault rather than ignore or replay a
        # shorter configuration prefix.
        mismatch = config_dir / "00000002.cfg"
        mismatch.write_bytes(generation_one.read_bytes())
        self.invoke(True, store, "recover", expected=run_store.EXIT_FAULT)
        mismatch.unlink()

        # A selected canonical-looking name that is a symlink is a physical
        # observation fault before the ACL2 plan receives its bytes.
        alias = config_dir / "00000002.cfg"
        alias.symlink_to(generation_one.name)
        self.invoke(True, store, "recover", expected=run_store.EXIT_FAULT)

    def test_native_refuses_truncated_or_malformed_metadata(self):
        original = self.base / "original"
        self.invoke(True, original, "init")
        cases = (
            ("config-truncated", "config.json", lambda raw: raw[:-1], b"configuration frame"),
            ("config-kind", "config.json",
             lambda raw: raw[:5] + bytes([2]) + raw[6:], b"configuration frame"),
        )
        for label, relative, damage, diagnostic in cases:
            with self.subTest(label=label):
                store = self.base / label
                shutil.copytree(original, store)
                path = store / relative
                path.write_bytes(damage(path.read_bytes()))
                result = self.invoke(True, store, "status", expected=run_store.EXIT_FAULT)
                self.assertIn(diagnostic, result.stderr)

    def test_legacy_json_is_retained_and_refused_by_name(self):
        store = self.base / "legacy"
        self.invoke(True, store, "init")
        legacy = b'{"format":"fn-store-experiment-5"}\n'
        path = store / "config.json"
        path.write_bytes(legacy)
        # D34: a JSON profile of an earlier experiment is refused at the open
        # by ACL2's name (host/native/io.lisp fnn-load-config), and kept.
        result = self.invoke(True, store, "status", expected=run_store.EXIT_REFUSED)
        self.assertIn(b"open refused reason=store-format", result.stderr)
        self.assertEqual(path.read_bytes(), legacy)

    def test_native_publication_cut_stays_uncertain_until_recovery(self):
        store = self.base / "uncertain"
        self.invoke(True, store, "init")
        result = self.invoke(
            True, store, "post", "--message-id", "<uncertain@example.invalid>",
            "--payload", self.payload, "--group", "fn.letters",
            "--inject-fault", "postpublish", expected=run_store.EXIT_UNCERTAIN)
        self.assertIn(b"indeterminate", result.stderr)
        recovered = self.invoke(True, store, "recover")
        self.assertIn(b"transactions=1 articles=1", recovered.stdout)
        inspected = self.invoke(True, store, "inspect", "--message-id",
                                "<uncertain@example.invalid>")
        self.assertEqual(inspected.stdout, self.payload.read_bytes())

    def test_injected_record_barrier_failure_replays_visible_publication(self):
        store = self.base / "record-barrier"
        self.invoke(True, store, "init")
        failed = self.direct_native_post(
            store, "<record-barrier@example.invalid>", "recordbarrier",
            run_store.EXIT_UNCERTAIN)
        # Format 9: the record's write is P-BATCH's append (the log batch).
        self.assertIn(b"log batch outcome is indeterminate", failed.stderr)
        self.invoke(True, store, "recover")
        inspected = self.invoke(True, store, "inspect", "--message-id",
                                "<record-barrier@example.invalid>")
        self.assertEqual(inspected.stdout, self.payload.read_bytes())



if __name__ == "__main__":
    unittest.main()
