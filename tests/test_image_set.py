"""tools/image_set.py: a published image set links into a tree in place of a build."""
from __future__ import annotations

import contextlib
import io
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import image_set  # noqa: E402

SHA = "a" * 40
LAUNCHER = ('#!/bin/sh\nexec "/sbcl" --core "{core}" --noinform "$@"\n')


class ImageSetTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.base = self.root / "images"
        self.tree = self.root / "built"
        build = self.tree / "build"
        (build / "lib").mkdir(parents=True)
        (build / "lib" / "libfn-blake3.so").write_bytes(b"lib")
        for file in ("fn-host", "fn-host-developer"):
            (build / f"{file}.core").write_bytes(file.encode() * 10)
            (build / file).write_text(LAUNCHER.format(core=build / f"{file}.core"))
        (build / "fn-host.world-deps").write_text("deps")

    def quiet(self, function, *args):
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()) as err:
            code = function(*args)
        return code, err.getvalue()

    def test_publish_then_link_gives_a_tree_the_published_images(self):
        self.assertEqual(self.quiet(image_set.publish, self.tree, SHA, self.base)[0], 0)
        published = self.base / SHA
        # The launcher names the PUBLISHED core, not the tree it came from.
        self.assertIn(f'--core "{published}/fn-host-developer.core"',
                      (published / "fn-host-developer").read_text())
        self.assertEqual((published / "TREE_SHA").read_text().strip(), SHA)
        self.assertEqual(image_set.verify(published), [])
        # Published once.
        self.assertEqual(self.quiet(image_set.publish, self.tree, SHA, self.base)[0], 1)
        other = self.root / "lane-tree"
        self.assertEqual(self.quiet(image_set.link, SHA, other, ["developer", "production"],
                                    self.base)[0], 0)
        launcher = other / "build" / "fn-host-developer"
        self.assertTrue(launcher.is_symlink())
        self.assertEqual(launcher.resolve(), published / "fn-host-developer")
        self.assertTrue((other / "build" / "fn-host.world-deps").is_symlink())
        self.assertEqual((other / "build" / "lib" / "libfn-blake3.so").read_bytes(), b"lib")

    def test_link_refuses_a_missing_image_and_a_damaged_set(self):
        self.quiet(image_set.publish, self.tree, SHA, self.base)
        code, err = self.quiet(image_set.link, SHA, self.root / "t", ["dtn"], self.base)
        self.assertEqual(code, 1)
        self.assertIn("has no dtn image", err)
        (self.base / SHA / "fn-host.core").write_bytes(b"changed")
        code, err = self.quiet(image_set.link, SHA, self.root / "t", ["production"], self.base)
        self.assertEqual(code, 1)
        self.assertIn("fails its SHA256SUMS: fn-host.core", err)
        self.assertEqual(self.quiet(image_set.link, "b" * 40, self.root / "t",
                                    ["production"], self.base)[0], 1)
        self.assertEqual(self.quiet(image_set.publish, self.tree, "short", self.base)[0], 2)


if __name__ == "__main__":
    unittest.main()
