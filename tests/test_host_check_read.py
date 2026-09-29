"""host_check --read: every host file reads as s-expressions, statically.

stx-model-2 (2026-09-29): the closing paren of an mv-let landed on
fn-owner-transit-decide's trailing COMMENT line in host/owner-host.lisp; the
file reached an image build before `host_check --load` refused it
("unterminated list").  obstructions-9 item 80 makes the reader pass a
`make check-fast` step that names the open form and where it should close.
"""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import host_check                                             # noqa: E402

GOOD = """(in-package "ACL2")
(defun fn-transit-decide (x)
  (mv-let (a b)
          (mv x x)
    (cons a b))) ; the decision (see "a string with ( in it")

#| a block comment ( |#
(defun fn-next (x) (list #\\( x))
"""
# The mv-let's closing paren went onto the trailing comment line.
BROKEN = GOOD.replace("(cons a b))) ; the decision", "(cons a b)) ; the decision)")


class ReadCheckTests(unittest.TestCase):
    def run_check(self, files):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "host" / "native").mkdir(parents=True)
            for name, text in files.items():
                (root / name).write_text(text)
            out = io.StringIO()
            with mock.patch.object(host_check, "ROOT", root), contextlib.redirect_stdout(out):
                code = host_check.main(["--read"])
        return code, out.getvalue()

    def test_a_tree_that_reads_passes(self):
        code, text = self.run_check({"host/a-host.lisp": GOOD, "host/native/b.lisp": GOOD})
        self.assertEqual(code, 0, text)
        self.assertIn("host_check --read: 0 host file(s) that do not read", text)

    def test_a_paren_in_a_comment_names_the_open_form_and_the_next_form(self):
        code, text = self.run_check({"host/a-host.lisp": GOOD, "host/owner-host.lisp": BROKEN})
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL host/owner-host.lisp: unterminated list; the form at line 2 is "
                      "still open where line 8 starts a form at column 0", text)
        self.assertNotIn("a-host", text)
        self.assertIn("1 host file(s) that do not read", text)

    def test_an_extra_close_paren_is_named(self):
        code, text = self.run_check({"host/a-host.lisp": GOOD + ")\n"})
        self.assertEqual(code, 1, text)
        self.assertIn("host/a-host.lisp: unbalanced close parenthesis at line 9", text)

    def test_the_real_host_tree_reads(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = host_check.main(["--read"])
        self.assertEqual(code, 0, out.getvalue())


if __name__ == "__main__":
    unittest.main()
