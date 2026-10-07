"""tools/image_set.py: a published image set links into a tree in place of a build."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import sys
import subprocess
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
            (build / f"{file}.catalog").write_text("paged\n")
            (build / f"{file}.source").write_text(f"commit {SHA}\n")
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
        for file in ("fn-host", "fn-host-developer"):
            self.assertEqual((other / "build" / f"{file}.catalog").read_text(), "paged\n")
        self.assertTrue((other / "build" / "fn-host.world-deps").is_symlink())
        self.assertEqual((other / "build" / "lib" / "libfn-blake3.so").read_bytes(), b"lib")
        # S063: a linked tree is NOT its own build; publishing it under a new
        # sha would relabel SHA's cores (this assertion used to expect 0).
        code, err = self.quiet(image_set.publish, other, "b" * 40, self.base)
        self.assertEqual(code, 1)
        self.assertIn("holds images it did not build", err)
        self.assertIn("fn-host.core is a symlink", err)
        self.assertFalse((self.base / ("b" * 40)).exists())

    def test_publish_requires_every_image_to_record_the_named_commit(self):
        """S057: the label is the build's own source record, not the caller's
        argument.  A tree built at one head and published as another, a
        dirty tree, and a build with no record are each refused by name."""
        build = self.tree / "build"
        other = "c" * 40
        code, err = self.quiet(image_set.publish, self.tree, other, self.base)
        self.assertEqual(code, 1)
        self.assertIn(f"do not record source commit {other}", err)
        self.assertIn(f"production (commit {SHA})", err)
        (build / "fn-host.source").write_text(f"worktree {SHA}+dirty\n")
        code, err = self.quiet(image_set.publish, self.tree, SHA, self.base)
        self.assertEqual(code, 1)
        self.assertIn(f"production (worktree {SHA}+dirty)", err)
        self.assertNotIn("developer (", err)
        (build / "fn-host.source").unlink()
        code, err = self.quiet(image_set.publish, self.tree, SHA, self.base)
        self.assertEqual(code, 1)
        self.assertIn("production (unknown)", err)
        self.assertFalse((self.base / SHA).exists())
        (build / "fn-host.source").write_text(f"commit {SHA}\n")
        self.assertEqual(self.quiet(image_set.publish, self.tree, SHA, self.base)[0], 0)
        manifest = json.loads((self.base / SHA / "MANIFEST.json").read_text())
        self.assertEqual(manifest["images"]["production"]["source"], f"commit {SHA}")

    def test_publish_refuses_a_tree_that_reused_another_runs_images(self):
        (self.tree / "build" / "REUSED_SOURCE").write_text("commit " + "d" * 40 + "\n")
        code, err = self.quiet(image_set.publish, self.tree, SHA, self.base)
        self.assertEqual(code, 1)
        self.assertIn("REUSED_SOURCE", err)
        self.assertFalse((self.base / SHA).exists())

    def test_link_refuses_a_manifest_recording_another_source(self):
        self.assertEqual(self.quiet(image_set.publish, self.tree, SHA, self.base)[0], 0)
        path = self.base / SHA / "MANIFEST.json"
        data = json.loads(path.read_text())
        data["images"]["production"]["source"] = "commit " + "e" * 40
        path.write_text(json.dumps(data))
        image_set.write_sums(self.base / SHA)
        code, err = self.quiet(image_set.link, SHA, self.root / "t", ["production"], self.base)
        self.assertEqual(code, 1)
        self.assertIn("records another source for production", err)

    def test_renamed_image_without_record_refuses_publish_and_link(self):
        build = self.tree / "build"
        for suffix in ("", ".core"):
            original = build / f"fn-host{suffix}"
            paged = build / f"fn-host-paged{suffix}"
            original.rename(paged)
            original.symlink_to(paged)
        (build / "fn-host.catalog").unlink()
        self.assertEqual(image_set.catalog_of(build, "fn-host"), "unknown")
        code, err = self.quiet(image_set.publish, self.tree, SHA, self.base)
        self.assertEqual(code, 1)
        self.assertIn("production (unknown)", err)
        self.assertIn("rebuild with tools/build_native_host.sh", err)
        self.assertFalse((self.base / SHA).exists())
        # An inert pre-record published set has the same missing evidence.
        published = self.base / SHA
        published.mkdir(parents=True)
        for suffix in ("", ".core"):
            (published / f"fn-host{suffix}").write_bytes((build / f"fn-host{suffix}").read_bytes())
        (published / "MANIFEST.json").write_text(json.dumps({"images": {
            "production": {"launcher": "fn-host", "core": "fn-host.core"}}}))
        image_set.write_sums(published)
        code, err = self.quiet(image_set.link, SHA, self.root / "t", ["production"], self.base)
        self.assertEqual(code, 1)
        self.assertIn("production (unknown)", err)
        self.assertIn("rebuild with tools/build_native_host.sh", err)
        self.assertFalse((self.root / "t" / "build").exists())

    def test_manifest_without_catalog_refuses_even_with_a_sidecar(self):
        self.assertEqual(self.quiet(image_set.publish, self.tree, SHA, self.base)[0], 0)
        published = self.base / SHA
        path = published / "MANIFEST.json"
        manifest = json.loads(path.read_text())
        del manifest["images"]["production"]["catalog"]
        path.write_text(json.dumps(manifest))
        (published / "fn-host.catalog").write_text("paged\n")
        image_set.write_sums(published)
        code, err = self.quiet(image_set.link, SHA, self.root / "t", ["production"], self.base)
        self.assertEqual(code, 1)
        self.assertIn("production (unknown)", err)
        self.assertIn("rebuild with tools/build_native_host.sh", err)
        self.assertFalse((self.root / "t" / "build").exists())

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


    def test_an_old_catalog_image_is_never_published_or_linked(self):
        # Codex r21 F2: the catalog is recorded beside the image
        # (tools/build_native_host.sh) and in the manifest; an image
        # not recorded paged (a pre-flip build) is refused at publish and at link.
        build = self.tree / "build"
        (build / "fn-host.catalog").write_text("old\n")
        code, err = self.quiet(image_set.publish, self.tree, SHA, self.base)
        self.assertEqual(code, 1)
        self.assertIn("production (old)", err)
        self.assertFalse((self.base / SHA).exists())
        (build / "fn-host.catalog").write_text("paged\n")
        self.assertEqual(self.quiet(image_set.publish, self.tree, SHA, self.base)[0], 0)
        manifest = (self.base / SHA / "MANIFEST.json").read_text()
        self.assertIn('"catalog": "paged"', manifest)
        # A manifest that records another catalog is not linked.
        import json
        path = self.base / SHA / "MANIFEST.json"
        data = json.loads(manifest)
        data["images"]["developer"]["catalog"] = "old"
        path.write_text(json.dumps(data))
        image_set.write_sums(self.base / SHA)
        code, err = self.quiet(image_set.link, SHA, self.root / "t", ["developer"], self.base)
        self.assertEqual(code, 1)
        self.assertIn("developer (old)", err)
        self.assertEqual(self.quiet(image_set.link, SHA, self.root / "t", ["production"],
                                    self.base)[0], 0)


class LinkRunTests(unittest.TestCase):
    """hbox_native --reuse-image: an earlier run's images, with their source."""

    def run_dir(self, directory: str, log: str = "== source commit abc123\n") -> Path:
        run = Path(directory) / "native-old"
        build = run / "tree" / "build"
        build.mkdir(parents=True)
        (run / "run.log").write_text("#!/bin/sh\n" + log + "== load at start: x\n")
        for name in ("fn-host-developer", "fn-host-developer.core", "fn-host-developer.world-deps"):
            (build / name).write_text(name)
        (build / "fn-host-developer").write_text(
            LAUNCHER.format(core=build / "fn-host-developer.core"))
        (build / "fn-host-developer.catalog").write_text("paged\n")
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
            self.assertEqual((build / "fn-host-developer.catalog").read_text(), "paged\n")
            # S063: a tree whose images were linked from a run is not
            # published under any sha (this assertion used to expect 0).
            with contextlib.redirect_stderr(io.StringIO()) as said:
                self.assertEqual(image_set.publish(tree, SHA, Path(directory) / "sets"), 1)
            self.assertIn("REUSED_SOURCE", said.getvalue())

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

    def test_link_run_refuses_a_renamed_image_without_record(self):
        with tempfile.TemporaryDirectory() as directory:
            run = self.run_dir(directory)
            build = run / "tree" / "build"
            for suffix in ("", ".core"):
                paged = build / f"fn-host-paged{suffix}"
                paged.write_text("inert paged fixture")
                (build / f"fn-host{suffix}").symlink_to(paged)
            tree = Path(directory) / "new"
            with contextlib.redirect_stderr(io.StringIO()) as said:
                self.assertEqual(image_set.link_run(run, tree, ["production"]), 1)
            self.assertIn("production (unknown)", said.getvalue())
            self.assertIn("rebuild with tools/build_native_host.sh", said.getvalue())
            self.assertFalse((tree / "build").exists())

    def test_link_run_refuses_an_old_catalog_image(self):
        with tempfile.TemporaryDirectory() as directory:
            run = self.run_dir(directory)
            (run / "tree" / "build" / "fn-host-developer.catalog").write_text("old\n")
            tree = Path(directory) / "new"
            with contextlib.redirect_stderr(io.StringIO()) as said:
                self.assertEqual(image_set.link_run(run, tree, ["developer"]), 1)
            self.assertIn("developer (old)", said.getvalue())
            self.assertFalse((tree / "build" / "fn-host-developer").exists())


if __name__ == "__main__":
    unittest.main()
