"""Teeth for `tools/tls_check.py`: each native build script loads its world once.

At ~600 top-level include-books the developer image used 60% of the
65536-slot TLS and b1 exhausted it (planning/evidence/arena-store-8-tls.md):
each top-level include reloads its closure's compiled files, and SBCL never
frees the TLS index a reloaded stub takes.  The real tree passes; each case
after it removes one premise of the shape and requires its finding.
"""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import tls_check  # noqa: E402
from tools import proof_cost  # noqa: E402
import world  # noqa: E402  (tools/extract/, on sys.path through tls_check)

UMBRELLA = "books/image-world"
BUILD = "host/native/build.lisp"


def script(first=UMBRELLA, prologue=world.PROLOGUE, late_include=False, tls=True):
    lines = [';; header', f'(include-book "{first}")']
    lines += list(prologue)
    lines += ['(include-book "books/outcome-class")',
              '(ld "host/store-host.lisp" :ld-error-action :error)']
    lines += list(world.EPILOGUE)
    if late_include:
        lines.append('(include-book "books/late")')
    lines += ['(defttag :fn-native-host)', '(defttag nil)', ':q']
    if tls:
        lines.append('(format t "~&FN_NATIVE_TLS ~d ~d~%" sb-vm::*free-tls-index* 0)')
    lines.append('(save-exec "build/fn-host" "x")')
    return "\n".join(lines) + "\n"


class TreeTests(unittest.TestCase):
    def test_the_tree_passes(self):
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(tls_check.static_check(), 0, out.getvalue())

    def test_every_saving_script_has_an_umbrella(self):
        self.assertEqual(sorted(tls_check.build_scripts()), sorted(world.UMBRELLAS))


class ShapeTests(unittest.TestCase):
    def problems(self, text):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "host/native").mkdir(parents=True)
            (root / BUILD).write_text(text, encoding="utf-8")
            return tls_check.structure_problems(BUILD, UMBRELLA, root)

    def test_the_shape_passes(self):
        self.assertEqual(self.problems(script()), [])

    def test_a_first_include_that_is_not_the_umbrella(self):
        found = self.problems(script(first="books/outcome-class"))
        self.assertTrue(any("not its umbrella" in p for p in found), found)

    def test_the_compiler_left_on(self):
        found = self.problems(script(prologue=world.PROLOGUE[:2]))
        self.assertTrue(any("PROLOGUE" in p for p in found), found)

    def test_an_include_after_the_closure_check(self):
        found = self.problems(script(late_include=True))
        self.assertTrue(any("follows the closure check" in p for p in found), found)

    def test_no_tls_figure(self):
        found = self.problems(script(tls=False))
        self.assertTrue(any("FN_NATIVE_TLS" in p for p in found), found)

    def test_a_saving_script_without_an_umbrella(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "host/native").mkdir(parents=True)
            (root / "books").mkdir()
            (root / BUILD).write_text(script(), encoding="utf-8")
            (root / "host/native/build-new.lisp").write_text(
                '(include-book "books/outcome-class")\n:q\n(save-exec "x" "y")\n', encoding="utf-8")
            (root / "books/image-world.lisp").write_text(
                '(in-package "ACL2")\n', encoding="utf-8")
            with mock.patch.dict(world.UMBRELLAS, {BUILD: UMBRELLA}, clear=True), \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(tls_check.static_check(root), 1)
            self.assertIn("host/native/build-new.lisp: saves an image", out.getvalue())


class UmbrellaCostTests(unittest.TestCase):
    """proof_cost leaves an include-only book to the image build's cost."""

    def test_include_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "books").mkdir()
            (root / "books/u.lisp").write_text(
                '(in-package "ACL2")\n(include-book "a")\n(include-book "b")\n', encoding="utf-8")
            (root / "books/p.lisp").write_text(
                '(in-package "ACL2")\n(include-book "a")\n(defthm x t)\n', encoding="utf-8")
            self.assertTrue(proof_cost.include_only(root, "books/u"))
            self.assertFalse(proof_cost.include_only(root, "books/p"))
            self.assertFalse(proof_cost.include_only(root, "books/absent"))


if __name__ == "__main__":
    unittest.main()
