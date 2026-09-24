"""Native store evidence for the ACL2-owned metadata and allocator codec."""

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

    def assert_frames_identical_but_for_the_stamp(self, python_frame, native_frame):
        """The two runtimes frame the same article identically but for its stamp.

        Each record carries its acceptance stamp (`fn-record-stamp',
        books/records-shape.lisp; specs/acceptance-stamp.md), read from the
        clock when it was prepared, so two posts made apart in time differ in
        that field and in the trailer over it.  ACL2 opens both frames and
        decodes both records; the native record, given the Python record's
        stamp by `fn-record-with-stamp', must then encode and frame to the
        Python transaction file byte for byte.
        """
        session = frame_bridge.session()
        python_record = session.store_unframe(python_frame)
        native_record = session.store_unframe(native_frame)
        answer = session.call(
            "(let ((n (fn-record-decode-exact {})) (p (fn-record-decode-exact {})))"
            " (if (and (consp n) (equal (car n) :ok) (consp (cdr n))"
            "          (fn-record-p (cadr n))"
            "          (consp p) (equal (car p) :ok) (consp (cdr p))"
            "          (fn-record-p (cadr p)))"
            "     (list (fn-record-stamp (cadr n)) (fn-record-stamp (cadr p))"
            "           (fn-record-encode (fn-record-with-stamp (cadr n)"
            "                                                  (fn-record-stamp (cadr p)))))"
            "   :undecodable))".format(frame_bridge._octets(native_record),
                                       frame_bridge._octets(python_record)))
        self.assertIsInstance(answer, list, f"ACL2 could not decode both records: {answer}")
        native_stamp, python_stamp, restamped = answer
        # Both runtimes stamped the article: neither wrote a legacy record.
        self.assertIsInstance(native_stamp, int, native_stamp)
        self.assertIsInstance(python_stamp, int, python_stamp)
        self.assertEqual(bytes(restamped), python_record)
        self.assertEqual(session.store_frame(bytes(restamped)), python_frame)

    def test_native_and_python_cross_open_identical_acl2_frames(self):
        native_store = self.base / "native-store"
        self.invoke(True, native_store, "init")
        config = (native_store / "config.json").read_bytes()
        frontier = (native_store / "allocation-frontier.json").read_bytes()
        self.assertTrue(config.startswith(b"FNSM\x01\x01"))
        self.assertTrue(frontier.startswith(b"FNSM\x01\x02"))
        self.invoke(False, native_store, "status")
        cross_id = "<cross-runtime@example.invalid>"
        self.post(False, native_store, cross_id)
        inspected = self.invoke(True, native_store, "inspect", "--message-id",
                                cross_id)
        self.assertEqual(inspected.stdout, self.payload.read_bytes())

        python_store = self.base / "python-store"
        self.invoke(False, python_store, "init")
        self.post(True, python_store, cross_id)
        inspected = self.invoke(False, python_store, "inspect", "--message-id",
                                cross_id)
        self.assertEqual(inspected.stdout, self.payload.read_bytes())
        self.assertEqual((python_store / "config.json").read_bytes(), config)
        self.assertEqual(
            (python_store / "allocation-frontier.json").read_bytes(),
            (native_store / "allocation-frontier.json").read_bytes())
        self.assert_frames_identical_but_for_the_stamp(
            (python_store / "transactions" / "00000000000000000000.txn").read_bytes(),
            (native_store / "transactions" / "00000000000000000000.txn").read_bytes())

        scale_store = self.base / "scale-store"
        run_store.Store(scale_store, writable=True, profile="scale").initialize()
        scale_status = self.invoke(True, scale_store, "status")
        self.assertIn(b"transactions=0 articles=0", scale_status.stdout)

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
            ("frontier-truncated", "allocation-frontier.json",
             lambda raw: raw[:-1], b"frontier frame"),
            ("frontier-kind", "allocation-frontier.json",
             lambda raw: raw[:5] + bytes([1]) + raw[6:], b"frontier frame"),
        )
        for label, relative, damage, diagnostic in cases:
            with self.subTest(label=label):
                store = self.base / label
                shutil.copytree(original, store)
                path = store / relative
                path.write_bytes(damage(path.read_bytes()))
                result = self.invoke(True, store, "status", expected=run_store.EXIT_FAULT)
                self.assertIn(diagnostic, result.stderr)

    def test_legacy_json_is_retained_and_requires_offline_migration(self):
        store = self.base / "legacy"
        self.invoke(True, store, "init")
        legacy = b'{"format":"fn-store-experiment-5"}\n'
        path = store / "config.json"
        path.write_bytes(legacy)
        result = self.invoke(True, store, "status", expected=run_store.EXIT_FAULT)
        self.assertIn(b"explicit offline migration", result.stderr)
        self.assertEqual(path.read_bytes(), legacy)

    def test_acl2_frontier_maximum_refuses_before_staging(self):
        store = self.base / "exhausted"
        self.invoke(True, store, "init")
        maximum = (1 << 32) - 1
        (store / "allocation-frontier.json").write_bytes(
            frame_bridge.session().metadata_frontier_frame(maximum))
        before = sorted(path.name for path in (store / "staging").iterdir())
        result = self.post(True, store, "<exhausted@example.invalid>",
                           expected=run_store.EXIT_REFUSED)
        self.assertIn(b"finite transaction-ID domain exhausted", result.stderr)
        self.assertEqual(sorted(path.name for path in (store / "staging").iterdir()), before)
        self.assertEqual(list((store / "transactions").iterdir()), [])

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
        inspected = self.invoke(False, store, "inspect", "--message-id",
                                "<uncertain@example.invalid>")
        self.assertEqual(inspected.stdout, self.payload.read_bytes())

    def test_injected_allocator_barrier_failure_consumes_the_id_after_recovery(self):
        store = self.base / "allocator-barrier"
        self.invoke(True, store, "init")
        failed = self.direct_native_post(
            store, "<allocator-barrier@example.invalid>", "frontierbarrier",
            run_store.EXIT_UNCERTAIN)
        self.assertIn(b"allocation-frontier update is indeterminate", failed.stderr)
        self.assertEqual(list((store / "transactions").iterdir()), [])
        self.invoke(True, store, "recover")
        self.post(True, store, "<after-allocator-barrier@example.invalid>")
        # Sequence remains local and gap-free; the stored transaction ID is
        # the ACL2 frontier after the uncertain reservation, not the old ID.
        self.assertEqual([path.name for path in (store / "transactions").iterdir()],
                         ["00000000000000000000.txn"])
        self.invoke(False, store, "recover")

    def test_injected_record_barrier_failure_replays_visible_publication(self):
        store = self.base / "record-barrier"
        self.invoke(True, store, "init")
        failed = self.direct_native_post(
            store, "<record-barrier@example.invalid>", "recordbarrier",
            run_store.EXIT_UNCERTAIN)
        self.assertIn(b"transaction publication outcome is indeterminate", failed.stderr)
        self.invoke(True, store, "recover")
        inspected = self.invoke(False, store, "inspect", "--message-id",
                                "<record-barrier@example.invalid>")
        self.assertEqual(inspected.stdout, self.payload.read_bytes())

    def test_native_namespace_codec_binds_filename_to_decoded_record_sequence(self):
        malformed = self.base / "namespace-malformed"
        self.invoke(True, malformed, "init")
        self.post(True, malformed, "<native-namespace@example.invalid>")
        original = malformed / "transactions" / "00000000000000000000.txn"
        os.link(original, malformed / "transactions" / "not-a-transaction")
        rejected = self.invoke(True, malformed, "status", expected=run_store.EXIT_FAULT)
        self.assertIn(b"ACL2 refused transaction namespace observation", rejected.stderr)
        self.assertEqual(original.read_bytes(),
                         (malformed / "transactions" / "not-a-transaction").read_bytes())

        mismatch = self.base / "namespace-binding"
        self.invoke(True, mismatch, "init")
        self.post(True, mismatch, "<native-binding@example.invalid>")
        first = mismatch / "transactions" / "00000000000000000000.txn"
        os.link(first, mismatch / "transactions" / "00000000000000000001.txn")
        bound = self.invoke(True, mismatch, "status", expected=run_store.EXIT_FAULT)
        self.assertIn(b"record sequence does not match immutable filename", bound.stderr)
        self.assertEqual(first.read_bytes(),
                         (mismatch / "transactions" / "00000000000000000001.txn").read_bytes())


if __name__ == "__main__":
    unittest.main()
