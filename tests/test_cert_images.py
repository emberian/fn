"""tools/cert_images.py: which image a book certifies from, and how one is built."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import cert_images  # noqa: E402

# base <- mid <- top, and side includes mid only locally.
BOOKS = {
    "books/base": '(in-package "ACL2")\n(defun fn-b (x) x)\n(defthm fn-b-id (equal (fn-b x) x))\n',
    "books/mid": '(in-package "ACL2")\n(include-book "base")\n(defun fn-m (x) (fn-b x))\n',
    "books/top": '(in-package "ACL2")\n(include-book "mid")\n(defun fn-t (x) (fn-m x))\n',
    "books/side": '(in-package "ACL2")\n(local (include-book "mid"))\n(defun fn-s (x) x)\n',
    "tests/acl2/top-tests": '(in-package "ACL2")\n(include-book "../../books/top")\n',
    "host/x-host": '(in-package "ACL2")\n(include-book "../books/mid")\n',
    # An attachable stobj, its attachment, and a book over the attachment.
    "books/arena": '(in-package "ACL2")\n(include-book "mid")\n(defabsstobj st :attachable t)\n',
    "books/arena-attach": '(in-package "ACL2")\n(include-book "mid")\n'
                          '(attach-stobj st st-impl)\n(include-book "arena")\n',
    "books/umbrella": '(in-package "ACL2")\n(include-book "arena-attach")\n',
}


def tree(directory: str) -> Path:
    root = Path(directory).resolve()
    for name, text in BOOKS.items():
        path = root / f"{name}.lisp"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    return root


class ImageForTests(unittest.TestCase):
    def test_a_book_takes_the_costliest_image_in_its_nonlocal_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            graph = cert_images.Graph(tree(directory))
            images = [{"name": "base", "roots": ["books/base"]},
                      {"name": "mid", "roots": ["books/mid"]}]
            self.assertEqual(cert_images.image_for("books/top", images, graph)["name"], "mid")
            self.assertEqual(cert_images.image_for("tests/acl2/top-tests", images, graph)["name"],
                             "mid")
            # An image never holds the book itself.
            self.assertEqual(cert_images.image_for("books/mid", images, graph)["name"], "base")
            self.assertIsNone(cert_images.image_for("books/base", images, graph))

    def test_a_locally_included_book_is_not_an_image_root_for_its_includer(self):
        # A plain-world include of `side' skips its local include of mid; a
        # portcullis naming mid would load mid into every includer.
        with tempfile.TemporaryDirectory() as directory:
            graph = cert_images.Graph(tree(directory))
            images = [{"name": "mid", "roots": ["books/mid"]}]
            self.assertIsNone(cert_images.image_for("books/side", images, graph))

    def test_only_book_directories_use_images(self):
        with tempfile.TemporaryDirectory() as directory:
            graph = cert_images.Graph(tree(directory))
            images = [{"name": "mid", "roots": ["books/mid"]}]
            self.assertIsNone(cert_images.image_for("host/x-host", images, graph))


class AttachStobjTests(unittest.TestCase):
    def test_no_image_defines_a_stobj_the_books_world_attaches(self):
        # batch BB: an image holding books/payload-arena (fn-arena) made the
        # umbrella's attach-stobj fail ("The name FN-ARENA is in use").
        with tempfile.TemporaryDirectory() as directory:
            graph = cert_images.Graph(tree(directory))
            images = [{"name": "arena", "roots": ["books/arena"]},
                      {"name": "mid", "roots": ["books/mid"]},
                      {"name": "attached", "roots": ["books/arena-attach"]}]
            self.assertEqual(graph.attached("books/umbrella"), {"st"})
            # An image that made the attachment itself is fine.
            self.assertEqual(cert_images.image_for("books/umbrella", images, graph)["name"],
                             "attached")
            images = images[:2]
            self.assertEqual(graph.defines(graph.nonlocal_closure("books/arena")), {"st"})
            self.assertEqual([i["name"] for i in cert_images.applicable(
                "books/umbrella", images, graph)], ["mid"])
            self.assertEqual(cert_images.image_for("books/arena-attach", images, graph)["name"],
                             "mid")

    def test_worlds_name_plain_and_each_allowed_image(self):
        with tempfile.TemporaryDirectory() as directory:
            root = tree(directory)
            (root / "tools").mkdir()
            (root / "tools/cert-images.json").write_text(
                '{"images": [{"name": "arena", "roots": ["books/arena"]},'
                ' {"name": "mid", "roots": ["books/mid"]}]}')
            self.assertEqual(cert_images.worlds(root, "books/umbrella"),
                             ["plain", "mid@books:books/mid"])
            self.assertEqual(cert_images.worlds(root, "host/x-host"), ["plain"])


class BuildTests(unittest.TestCase):
    def test_includes_are_issued_from_the_books_own_directory(self):
        # A portcullis include-book stays relative only when issued from the
        # certified book's directory (make-include-books-absolute-1).
        image = {"name": "mid", "roots": ["books/mid"]}
        core = Path("/run/images/books--mid.core")
        books = cert_images.build_script(image, "books", core)
        self.assertIn('(set-cbd "books/")\n(include-book "mid")\n', books)
        tests = cert_images.build_script(image, "tests/acl2", core)
        self.assertIn('(set-cbd "tests/acl2/")\n(include-book "../../books/mid")\n', tests)
        self.assertIn('(save-exec "/run/images/books--mid-saved"', books)
        # Non-local: a local portcullis makes certify-book's Step 3 replay it.
        self.assertNotIn("(local", books)

    def test_the_launcher_keeps_the_toolchain_flags_and_swaps_the_core(self):
        with tempfile.TemporaryDirectory() as directory:
            acl2 = Path(directory) / "acl2"
            acl2.write_text('#!/bin/sh\nexec "/sbcl" --tls-limit 16384 --dynamic-space-size 4096 '
                            '--core "/acl2/saved_acl2.core" --end-runtime-options "$@"\n')
            text = cert_images.launcher_for(acl2, Path("/run/images/books--mid.core"))
            self.assertIn('--core "/run/images/books--mid.core"', text)
            self.assertIn("--tls-limit 16384 --dynamic-space-size 4096", text)

    def test_the_fixup_relinks_only_equal_values(self):
        self.assertIn("(equal (cddr d) (symbol-value s))", cert_images.FIXUP)
        self.assertTrue(cert_images.FIXUP.startswith(":q\n"))
        self.assertTrue(cert_images.FIXUP.endswith("(lp)\n"))


class PlanTests(unittest.TestCase):
    def test_the_first_checkpoint_is_the_one_most_books_reuse_most(self):
        with tempfile.TemporaryDirectory() as directory:
            root = tree(directory)
            graph = cert_images.Graph(root)
            chosen = cert_images.plan(graph, ["books/top", "tests/acl2/top-tests", "books/side"], 2)
            self.assertEqual(chosen[0]["roots"], ["books/mid"])
            self.assertEqual(chosen[0]["users"], 2)


if __name__ == "__main__":
    unittest.main()


class TreeTests(unittest.TestCase):
    """The committed image set on this tree: the batch BB defect, pinned."""

    def test_the_umbrellas_never_start_from_an_image_that_defines_fn_arena(self):
        root = Path(__file__).resolve().parents[1]
        graph = cert_images.Graph(root)
        images = cert_images.load_config(root)
        for umbrella in ("books/image-world", "books/image-world-dtn",
                         "books/image-world-store-test"):
            self.assertIn("fn-arena", graph.attached(umbrella), umbrella)
            for image in cert_images.applicable(umbrella, images, graph):
                self.assertNotIn("fn-arena", graph.defines(
                    cert_images.image_closure(image, graph)), (umbrella, image["name"]))
            chosen = cert_images.image_for(umbrella, images, graph)
            self.assertNotIn(chosen and chosen["name"], ("owner", "served-catalog-owner",
                                                         "nntp-auth", "nntp"))
        # A book above the owner that attaches nothing still starts from one.
        for book in ("books/owner-invariants-relation", "books/owner-cold-line"):
            if (root / f"{book}.lisp").is_file():
                self.assertFalse(graph.attached(book) & graph.defines(
                    cert_images.image_closure(cert_images.image_for(book, images, graph),
                                              graph)), book)
                self.assertIsNotNone(cert_images.image_for(book, images, graph), book)
