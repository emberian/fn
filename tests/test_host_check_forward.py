"""host_check --forward: a call in an ld host file of a name only a later form defines.

limits-live-4 (2026-09-29): host/owner-host.lisp called fn-owner-record-octets
350 lines before its definition; `--load` (raw files only) passed and the
image build refused it.  At ba761eb06^ this check names exactly that call.
"""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import host_check                                             # noqa: E402

BUILD = """(in-package "ACL2")
(include-book "../../books/base")
(ld "host/a-host.lisp" :ld-error-action :error)
(ld "host/c-host.lisp" :ld-error-action :error)
(load "host/native/raw.lisp")
"""
BASE = '(in-package "ACL2")\n(defun fn-base-f (x) x)\n'
A_HOST = """(in-package "ACL2")
(ld "b-host.lisp" :ld-error-action :error)
(defun fn-a-use (x)
  (declare (xargs :mode :program))
  (list (fn-a-later x) (fn-b-early x) (fn-base-f x) '(fn-a-later quoted)))
(mutual-recursion
 (defun fn-a-even (n) (declare (xargs :mode :program)) (if (zp n) t (fn-a-odd (1- n))))
 (defun fn-a-odd (n) (declare (xargs :mode :program)) (if (zp n) nil (fn-a-even (1- n)))))
(defun fn-a-later (x)
  (declare (xargs :mode :program))
  x)
"""
B_HOST = '(in-package "ACL2")\n(defun fn-b-early (x) (declare (xargs :mode :program)) x)\n'
C_HOST = """(in-package "ACL2")
(defun fn-c-use (x) (declare (xargs :mode :program)) (fn-a-later x))
"""


class ForwardReferenceTests(unittest.TestCase):
    def tree(self, directory: str) -> Path:
        root = Path(directory).resolve()
        for name, text in (("host/native/build.lisp", BUILD), ("books/base.lisp", BASE),
                           ("host/a-host.lisp", A_HOST), ("host/b-host.lisp", B_HOST),
                           ("host/c-host.lisp", C_HOST),
                           ("host/native/raw.lisp", "(defun fnn-raw () (fn-a-nowhere))\n")):
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text(text)
        return root

    def test_only_a_call_before_its_definition_is_named(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            found = host_check.forward_references("host/native/build.lisp", root)
        # b-host (ld inside a-host, before its forms), the book, the quoted
        # list, the mutual-recursion members and c-host (a later file) are fine.
        self.assertEqual(found, [
            "host/a-host.lisp:5: fn-a-later is called before its definition "
            "(host/a-host.lisp:9); ACL2 refuses the call when it translates this form"])

    def test_the_ld_order_follows_an_ld_inside_a_host_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            self.assertEqual(host_check.ld_sequence("host/native/build.lisp", root),
                             ["host/a-host.lisp", "host/b-host.lisp", "host/c-host.lisp"])

    def test_the_forward_mode_exits_by_what_it_found(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            real = host_check.forward_references
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                host_check.forward_references = lambda build, root_=None: real(build, root)
                holes = host_check.book_holes
                host_check.book_holes = lambda builds: holes(builds, root)
                try:
                    code = host_check.main(["--forward", "--build", "host/native/build.lisp"])
                finally:
                    host_check.forward_references = real
                    host_check.book_holes = holes
            self.assertEqual(code, 1)
            self.assertIn("FAIL host/a-host.lisp:5: fn-a-later", out.getvalue())
            self.assertIn("call(s) into a book outside the image world (--books)",
                          out.getvalue())


class BookHoleTests(unittest.TestCase):
    """obstructions-9 item 83: a host file calls a name only a book outside the
    image world defines (store-checkpoint-digest, store-finalize-incremental)."""

    def tree(self, directory: str, include_it: bool) -> Path:
        root = Path(directory).resolve()
        host = ('(in-package "ACL2")\n'
                + ('(include-book "../books/digest")\n' if include_it else "")
                + "(defun fn-open (x)\n  (declare (xargs :mode :program))\n"
                  "  (list (fn-digest x) (fn-base-f x) (car x) '(fn-local-only q)))\n")
        build = BUILD.replace('"../../books/base"', '"books/base"')
        files = {"host/native/build.lisp": build, "books/base.lisp": BASE,
                 "books/digest.lisp": '(in-package "ACL2")\n(defun fn-digest (x) x)\n'
                                      '(local (defun fn-local-only (x) x))\n',
                 "host/a-host.lisp": host, "host/c-host.lisp": '(in-package "ACL2")\n',
                 "host/native/raw.lisp": ""}
        for name, text in files.items():
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text(text)
        return root

    def test_a_call_into_a_book_outside_the_world_is_named_with_the_book(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory, include_it=False)
            found = host_check.book_holes(("host/native/build.lisp",), root)
        self.assertEqual(found, [
            "host/native/build.lisp: host/a-host.lisp:4: fn-digest is defined in books/digest, "
            "which this image's world does not include: include-book it in host/a-host.lisp "
            "(and regenerate the umbrellas: tools/extract/world.py)"])

    def test_the_host_files_own_include_closes_the_hole(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory, include_it=True)
            self.assertEqual(host_check.book_holes(("host/native/build.lisp",), root), [])


if __name__ == "__main__":
    unittest.main()
