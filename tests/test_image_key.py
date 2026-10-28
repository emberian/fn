"""tools/image_key.py: an image's key is its inputs and nothing else."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import image_key  # noqa: E402
import image_set  # noqa: E402


def tree(base: Path) -> Path:
    for name, text in {
        "host/native/build.lisp": '(ld "../host-a.lisp")\n(include-book "../../books/a")\n',
        "host/native/build-dtn.lisp": '(include-book "../../books/b")\n',
        "host/host-a.lisp": "; host a\n",
        "host/native/raw.lisp": "; raw\n",
        "third_party/zlib/z.c": "int z;\n",
        "books/a.lisp": '(in-package "ACL2")\n(include-book "base")\n',
        "books/base.lisp": '(in-package "ACL2")\n(defun base (x) x)\n',
        "books/b.lisp": '(in-package "ACL2")\n(defun b (x) x)\n',
        "books/unrelated.lisp": '(in-package "ACL2")\n(defun u (x) x)\n',
        "tools/build_native_host.sh": "# build\n",
        "tools/build_mldsa65.sh": "# lib\n",
        "tools/build_deflate.sh": "# lib\n",
        "tools/build_blake3.sh": "# lib\n",
        "tools/acl2_projects.py": "# p\n",
        "tools/cut_gate.sh": "# gate\n",
        "packaging/fn": "# fn\n",
        "packaging/launcher-decide.sh": "# decide\n",
    }.items():
        path = base / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    return base


class ImageKeyTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = tree(Path(self.directory.name))

    def keys(self, *images):
        return image_key.image_keys(self.root, list(images or ("production", "dtn")), None, None)

    def edit(self, name, text):
        (self.root / name).write_text(text)

    # host/ and third_party/ are keyed whole (the raw host files, the vendored
    # sources): one edit there moves every image.  Books move only the images
    # whose session script includes them.
    def test_a_change_to_tools_or_tests_leaves_every_key(self):
        before = self.keys()
        self.edit("tools/cut_gate.sh", "# a different gate\n")
        (self.root / "tools" / "new_tool.py").write_text("print(1)\n")
        (self.root / "tests").mkdir()
        (self.root / "tests" / "test_x.py").write_text("pass\n")
        self.edit("books/unrelated.lisp", '(in-package "ACL2")\n(defun u (x) (cons x x))\n')
        self.assertEqual(self.keys(), before)

    def test_each_input_changes_the_key_of_the_images_that_read_it(self):
        base = self.keys()
        cases = {
            "a loaded host file": ("host/host-a.lisp", "; host a'\n", {"production", "dtn"}),
            "a raw host file": ("host/native/raw.lisp", "; raw'\n", {"production", "dtn"}),
            "the session script": ("host/native/build.lisp",
                                   '(ld "../host-a.lisp")\n(include-book "../../books/a")\n; x\n',
                                   {"production", "dtn"}),
            "a book in the closure": ("books/base.lisp",
                                      '(in-package "ACL2")\n(defun base (x) (cons x x))\n',
                                      {"production"}),
            "a book of the dtn world": ("books/b.lisp", '(in-package "ACL2")\n(defun b (x) 1)\n',
                                        {"dtn"}),
            "a foreign library source": ("third_party/zlib/z.c", "int z2;\n",
                                         {"production", "dtn"}),
            "a build script": ("tools/build_native_host.sh", "# build'\n", {"production", "dtn"}),
            "a launcher rewrite input": ("packaging/launcher-decide.sh", "# decide'\n",
                                         {"production", "dtn"}),
        }
        for label, (name, text, moved) in cases.items():
            with self.subTest(label):
                original = (self.root / name).read_text()
                self.edit(name, text)
                after = self.keys()
                self.edit(name, original)
                self.assertEqual({image for image in after if after[image] != base[image]}, moved)

    def test_the_profile_and_world_flavour_are_part_of_the_key(self):
        keys = self.keys("production", "developer", "reference", "developer-stripped")
        self.assertEqual(len(set(keys.values())), 4)

    def test_the_environment_the_build_reads_is_part_of_the_key(self):
        base = self.keys()
        with mock.patch.dict(os.environ, {"FN_TLS_LIMIT": "1"}):
            self.assertNotEqual(self.keys(), base)

    def test_the_set_key_names_the_images_together(self):
        keys = self.keys()
        self.assertEqual(image_key.set_key(keys), image_key.set_key(dict(reversed(keys.items()))))
        self.assertNotEqual(image_key.set_key(keys), image_key.set_key({"production": keys["production"]}))


class StoreTests(unittest.TestCase):
    def build(self, root: Path, sha: str, images=("production", "dtn")):
        build = root / "build"
        build.mkdir()
        for image in images:
            file = image_set.IMAGES[image]
            (build / file).write_text(f'#!/bin/sh\nexec sbcl --core "{build / file}.core" "$@"\n')
            (build / f"{file}.core").write_bytes(b"core " + image.encode())
            (build / f"{file}.catalog").write_text("paged\n")
            (build / f"{file}.source").write_text(f"commit {sha}\n")

    def test_a_published_set_links_into_another_tree_under_its_key(self):
        sha = "a" * 40
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            first, second, store = base / "one", base / "two", base / "store"
            first.mkdir(), second.mkdir(), store.mkdir()
            self.build(first, sha)
            (first / "tools").mkdir()
            record = base / "keys.json"
            record.write_text(json.dumps({"set": "k" * 64}))
            self.assertEqual(image_key.publish(store, first, record, sha), 0)
            manifest = json.loads((store / ("k" * 64) / "MANIFEST.json").read_text())
            self.assertEqual(manifest["sha"], sha)
            # A second publication of the same key is refused, not replaced.
            self.assertEqual(image_key.publish(store, first, record, sha), 1)
            self.assertEqual(image_set.link(sha, second, ["production", "dtn"], store,
                                            name="k" * 64), 0)
            self.assertTrue((second / "build" / "fn-host.core").is_symlink())
            launcher = (store / ("k" * 64) / "fn-host").read_text()
            self.assertIn(str(store / ("k" * 64) / "fn-host.core"), launcher)
            image_key.unlink(store, second)
            self.assertFalse((second / "build" / "fn-host.core").exists())


if __name__ == "__main__":
    unittest.main()
