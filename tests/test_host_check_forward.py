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
                try:
                    code = host_check.main(["--forward", "--build", "host/native/build.lisp"])
                finally:
                    host_check.forward_references = real
            self.assertEqual(code, 1)
            self.assertIn("FAIL host/a-host.lisp:5: fn-a-later", out.getvalue())


if __name__ == "__main__":
    unittest.main()
