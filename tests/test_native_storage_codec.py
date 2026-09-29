"""Native store evidence for the ACL2-owned metadata codec.

The per-file allocator and transaction namespace (allocation-frontier.json,
transactions/NNN.txn) are not read by a store: its history and its
frontier are the record log's (books/store-log*.lisp).  The cases that
exercised them -- the Python/native cross-open of per-file stores, the
frontier file's maximum and barrier, the file name bound to the record's
sequence, the frontier frame refusals -- are retired with that layout (lane
log-recovery-mod); the configuration namespace, the profile frame and the
injected commit outcomes stay."""

import shutil
import unittest

from tests.native_harness import (
    EXIT_FAULT, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, ROOT, assert_outcome, native_image,
    requires, run, scratch)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


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


@requires(IMAGE)
class NativeStorageCodecTests(unittest.TestCase):
    """The raw Store verbs of the developer image (`IMAGE --fn store ROOT
    VERB ...`); these cases once went through tools/run_store.py with
    FN_HOST=native, which only re-parsed the words and exec'd the image."""

    def setUp(self):
        self.base = scratch(self, "fn-native-metadata-")
        self.payload = self.base / "payload"
        self.payload.write_bytes(b"native metadata")

    def invoke(self, store, *words, expected=EXIT_OK):
        """`IMAGE --fn store STORE WORDS...`, asserted to exit EXPECTED."""
        result = run([IMAGE, "--fn", "store", store, *words], timeout=None)
        assert_outcome(self, result, expected)
        return result

    def post(self, store, message_id, fault="-", expected=EXIT_OK):
        # The image's positional post: MESSAGE-ID PAYLOAD CHARGE FAULT GROUP...
        return self.invoke(store, "post", message_id, self.payload, "-", fault,
                           "fn.letters", expected=expected)

    def test_native_config_namespace_refuses_mismatched_name_and_symlink(self):
        store = self.base / "config-namespace"
        self.invoke(store, "init")
        config_dir = store / "config"
        generation_one = config_dir / "00000001.cfg"

        # The bytes decode to generation 1 but their observed basename claims
        # generation 2.  Recovery must fault rather than ignore or replay a
        # shorter configuration prefix.
        mismatch = config_dir / "00000002.cfg"
        mismatch.write_bytes(generation_one.read_bytes())
        self.invoke(store, "recover", expected=EXIT_FAULT)
        mismatch.unlink()

        # A selected canonical-looking name that is a symlink is a physical
        # observation fault before the ACL2 plan receives its bytes.
        alias = config_dir / "00000002.cfg"
        alias.symlink_to(generation_one.name)
        self.invoke(store, "recover", expected=EXIT_FAULT)

    def test_native_refuses_truncated_or_malformed_metadata(self):
        original = self.base / "original"
        self.invoke(original, "init")
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
                result = self.invoke(store, "status", expected=EXIT_FAULT)
                self.assertIn(diagnostic, result.stderr)

    def test_legacy_json_is_retained_and_is_a_fault(self):
        store = self.base / "legacy"
        self.invoke(store, "init")
        legacy = b'{"format":"fn-store-experiment-5"}\n'
        path = store / "config.json"
        path.write_bytes(legacy)
        # One format (ember 2026-09-28, no migrations): a profile FRAME of
        # another format word is refused by ACL2's name (store-format), but
        # the JSON of an earlier experiment is no frame at all, so the open
        # names it a fault (host/native/io.lisp fnn-metadata-config-decode:
        # "a frame that is no saved profile stays a fault") -- and keeps it.
        result = self.invoke(store, "status", expected=EXIT_FAULT)
        self.assertIn(b"ACL2 rejected durable configuration frame", result.stderr)
        self.assertEqual(path.read_bytes(), legacy)

    def test_native_publication_cut_stays_uncertain_until_recovery(self):
        store = self.base / "uncertain"
        self.invoke(store, "init")
        result = self.post(store, "<uncertain@example.invalid>", "postpublish",
                           expected=EXIT_UNCERTAIN)
        self.assertIn(b"indeterminate", result.stderr)
        recovered = self.invoke(store, "recover")
        self.assertIn(b"transactions=1 articles=1", recovered.stdout)
        inspected = self.invoke(store, "inspect", "<uncertain@example.invalid>")
        self.assertEqual(inspected.stdout, self.payload.read_bytes())

    def test_injected_record_barrier_failure_replays_visible_publication(self):
        store = self.base / "record-barrier"
        self.invoke(store, "init")
        failed = self.post(store, "<record-barrier@example.invalid>", "recordbarrier",
                           expected=EXIT_UNCERTAIN)
        # the record's write is P-BATCH's append (the log batch).
        self.assertIn(b"log batch outcome is indeterminate", failed.stderr)
        self.invoke(store, "recover")
        inspected = self.invoke(store, "inspect", "<record-barrier@example.invalid>")
        self.assertEqual(inspected.stdout, self.payload.read_bytes())



if __name__ == "__main__":
    unittest.main()
