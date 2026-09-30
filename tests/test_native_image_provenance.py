"""Composed fixture source checking without launching native processes."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from tests.native_image_provenance import assert_same_published_source


class PublishedSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def published(self, name, source="a" * 40):
        directory = self.root / name
        directory.mkdir()
        images = {}
        files = {}
        for kind in ("fn-host-developer", "fn-host-dtn-developer"):
            launcher = directory / kind
            launcher.write_text("#!/bin/sh\nexit 0\n")
            core = directory / (kind + ".core")
            core.write_bytes(b"fixture core")
            images[kind] = {"launcher": kind, "core": core.name}
            files[kind] = hashlib.sha256(launcher.read_bytes()).hexdigest()
        (directory / "TREE_SHA").write_text(source + "\n")
        (directory / "MANIFEST.json").write_text(json.dumps(
            {"sha": source, "images": images, "files": files}))
        return directory / "fn-host-developer", directory / "fn-host-dtn-developer"

    def test_same_set_symlinks_bind_actual_source(self):
        reader, bp = self.published("set")
        linked = self.root / "linked-reader"
        linked.symlink_to(reader)
        self.assertEqual(assert_same_published_source(self, linked, bp), "a" * 40)

    def test_mixed_sources_are_rejected(self):
        reader, _ = self.published("one")
        _, bp = self.published("two", "b" * 40)
        with self.assertRaisesRegex(AssertionError, "different source commits"):
            assert_same_published_source(self, reader, bp)

    def test_tree_label_cannot_override_manifest(self):
        reader, bp = self.published("set")
        (reader.parent / "TREE_SHA").write_text("b" * 40)
        with self.assertRaisesRegex(AssertionError, "TREE_SHA differs"):
            assert_same_published_source(self, reader, bp)

    def test_modified_launcher_is_rejected(self):
        reader, bp = self.published("set")
        reader.write_text("#!/bin/sh\nexec other-image\n")
        with self.assertRaisesRegex(AssertionError, "launcher differs"):
            assert_same_published_source(self, reader, bp)

    def test_unpublished_or_missing_core_is_rejected(self):
        reader, bp = self.published("set")
        (bp.parent / (bp.name + ".core")).unlink()
        with self.assertRaisesRegex(AssertionError, "core missing"):
            assert_same_published_source(self, reader, bp)
        (reader.parent / "MANIFEST.json").unlink()
        with self.assertRaisesRegex(AssertionError, "source unavailable"):
            assert_same_published_source(self, reader, bp)

    def test_undeclared_launcher_is_rejected(self):
        reader, bp = self.published("set")
        impostor = reader.parent / "unlisted"
        impostor.write_bytes(reader.read_bytes())
        with self.assertRaisesRegex(AssertionError, "published image entry"):
            assert_same_published_source(self, impostor, bp)


if __name__ == "__main__":
    unittest.main()
