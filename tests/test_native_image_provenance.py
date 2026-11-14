"""Temporary image-set controls; no ACL2, native process or shared cache use."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from native_image_provenance import _published_source


class PublishedPayloadBinding(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = "a" * 40
        self.launcher = self.root / "fn-host"
        self.payloads = {"fn-host": b"launcher", "fn-host.core": b"saved ACL2 world",
                         "runtime/sbcl": b"runtime", "lib/native.so": b"qualified library",
                         "host/helper.lisp": b"raw helper"}
        for name, data in self.payloads.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.manifest = dict(sha=self.source,
                             images={"production": dict(launcher="fn-host", core="fn-host.core")},
                             files={name: hashlib.sha256(data).hexdigest()
                                    for name, data in self.payloads.items()})
        (self.root / "TREE_SHA").write_text(self.source + "\n")
        self.write_manifest()

    def write_manifest(self):
        (self.root / "MANIFEST.json").write_text(json.dumps(self.manifest))

    def test_unchanged_set_and_launcher_alias_keep_source_coordinate(self):
        self.assertEqual(_published_source(self.launcher), self.source)
        alias = self.root / "alias"
        alias.symlink_to(self.launcher)
        self.assertEqual(_published_source(alias), self.source)

    def test_payload_replacement_after_receipt_is_refused(self):
        for name, data in self.payloads.items():
            with self.subTest(payload=name):
                path = self.root / name
                path.write_bytes(b"changed after qualification")
                try:
                    with self.assertRaises(ValueError):
                        _published_source(self.launcher)
                finally:
                    path.write_bytes(data)

    def test_core_cannot_be_omitted_from_hashes(self):
        del self.manifest["files"]["fn-host.core"]
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "input not bound: fn-host.core"):
            _published_source(self.launcher)

    def test_missing_or_malformed_payload_hash_is_refused(self):
        for hashes in (None, {}, {"fn-host": "not-a-digest", "fn-host.core": "f" * 64}):
            with self.subTest(hashes=hashes):
                self.manifest["files"] = hashes
                self.write_manifest()
                with self.assertRaises(ValueError):
                    _published_source(self.launcher)

    def test_payload_symlink_retarget_is_refused_even_with_identical_bytes(self):
        path = self.root / "lib/native.so"
        with tempfile.TemporaryDirectory() as external:
            target = Path(external) / "replacement.so"
            target.write_bytes(self.payloads["lib/native.so"])
            path.unlink()
            path.symlink_to(target)
            with self.assertRaisesRegex(ValueError, "payload differs"):
                _published_source(self.launcher)

    def test_recorded_path_escape_is_refused(self):
        for name in ("../outside", "/tmp/outside", ""):
            with self.subTest(path=name):
                self.manifest["files"][name] = "f" * 64
                self.write_manifest()
                with self.assertRaisesRegex(ValueError, "invalid published payload path"):
                    _published_source(self.launcher)
                del self.manifest["files"][name]

    def test_missing_recorded_library_is_refused(self):
        (self.root / "lib/native.so").unlink()
        with self.assertRaises(OSError):
            _published_source(self.launcher)

    def test_source_coordinates_still_require_matching_tree_sha(self):
        (self.root / "TREE_SHA").write_text("b" * 40)
        with self.assertRaisesRegex(ValueError, "TREE_SHA differs"):
            _published_source(self.launcher)


if __name__ == "__main__":
    unittest.main()
