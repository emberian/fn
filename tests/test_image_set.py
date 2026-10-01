"""tools/image_set.py: a published image set links into a tree in place of a build."""
from __future__ import annotations

import contextlib
import io
import json
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
            (build / f"{file}.catalog").write_text("old\n")
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
            self.assertEqual((other / "build" / f"{file}.catalog").read_text(), "old\n")
        # The linked tree can supply affirmative evidence downstream.
        self.assertEqual(self.quiet(image_set.publish, other, "b" * 40, self.base)[0], 0)
        self.assertTrue((other / "build" / "fn-host.world-deps").is_symlink())
        self.assertEqual((other / "build" / "lib" / "libfn-blake3.so").read_bytes(), b"lib")

    def test_renamed_paged_image_without_record_refuses_publish_and_link(self):
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
        (published / "fn-host.catalog").write_text("old\n")
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


    def test_a_paged_catalog_image_is_never_published_or_linked_as_the_old(self):
        # Codex r21 F2: the catalog is recorded beside the image
        # (tools/build_native_host.sh) and in the manifest; a paged core
        # under the old catalog's name is refused at publish and at link.
        build = self.tree / "build"
        (build / "fn-host.catalog").write_text("paged\n")
        code, err = self.quiet(image_set.publish, self.tree, SHA, self.base)
        self.assertEqual(code, 1)
        self.assertIn("production (paged)", err)
        self.assertFalse((self.base / SHA).exists())
        (build / "fn-host.catalog").write_text("old\n")
        self.assertEqual(self.quiet(image_set.publish, self.tree, SHA, self.base)[0], 0)
        manifest = (self.base / SHA / "MANIFEST.json").read_text()
        self.assertIn('"catalog": "old"', manifest)
        # A manifest that records another catalog is not linked.
        import json
        path = self.base / SHA / "MANIFEST.json"
        data = json.loads(manifest)
        data["images"]["developer"]["catalog"] = "paged"
        path.write_text(json.dumps(data))
        image_set.write_sums(self.base / SHA)
        code, err = self.quiet(image_set.link, SHA, self.root / "t", ["developer"], self.base)
        self.assertEqual(code, 1)
        self.assertIn("developer (paged)", err)
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
        (build / "fn-host-developer.catalog").write_text("old\n")
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
            self.assertEqual((build / "fn-host-developer.catalog").read_text(), "old\n")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(image_set.publish(tree, SHA, Path(directory) / "sets"), 0)

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

    def test_link_run_refuses_renamed_paged_image_without_record(self):
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

    def test_link_run_refuses_a_paged_catalog_image(self):
        with tempfile.TemporaryDirectory() as directory:
            run = self.run_dir(directory)
            (run / "tree" / "build" / "fn-host-developer.catalog").write_text("paged\n")
            tree = Path(directory) / "new"
            with contextlib.redirect_stderr(io.StringIO()) as said:
                self.assertEqual(image_set.link_run(run, tree, ["developer"]), 1)
            self.assertIn("developer (paged)", said.getvalue())
            self.assertFalse((tree / "build" / "fn-host-developer").exists())


if __name__ == "__main__":
    unittest.main()
