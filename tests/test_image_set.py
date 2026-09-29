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



class LinkRunTests(unittest.TestCase):
    """hbox_native --reuse-image: an earlier run's images, with their source."""

    def run_dir(self, directory: str, log: str = "== source commit abc123\n") -> Path:
        run = Path(directory) / "native-old"
        build = run / "tree" / "build"
        build.mkdir(parents=True)
        (run / "run.log").write_text("#!/bin/sh\n" + log + "== load at start: x\n")
        for name in ("fn-host-developer", "fn-host-developer.core", "fn-host-developer.world-deps"):
            (build / name).write_text(name)
        (build / "lib").mkdir()
        return run

    def test_link_run_links_the_images_and_records_their_source(self):
        with tempfile.TemporaryDirectory() as directory:
            run = self.run_dir(directory)
            tree = Path(directory) / "new"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(image_set.main(["link-run", str(run), str(tree), "developer"]), 0)
            build = tree / "build"
            for name in ("fn-host-developer", "fn-host-developer.core",
                         "fn-host-developer.world-deps", "lib"):
                self.assertTrue((build / name).is_symlink(), name)
                self.assertEqual((build / name).resolve(), (run / "tree/build" / name).resolve())
            self.assertEqual((build / "REUSED_SOURCE").read_text(), "abc123\n")

    def test_link_run_refuses_a_missing_image_or_an_unknown_source(self):
        with tempfile.TemporaryDirectory() as directory:
            run = self.run_dir(directory)
            tree = Path(directory) / "new"
            with contextlib.redirect_stderr(io.StringIO()) as said:
                self.assertEqual(image_set.link_run(run, tree, ["production"]), 1)
            self.assertIn("no production image", said.getvalue())
            (run / "run.log").write_text("#!/bin/sh\n")
            with contextlib.redirect_stderr(io.StringIO()) as said:
                self.assertEqual(image_set.link_run(run, tree, ["developer"]), 1)
            self.assertIn("names no `== source` line", said.getvalue())
            self.assertFalse((tree / "build" / "fn-host-developer").exists())


if __name__ == "__main__":
    unittest.main()
