"""Teeth for tools/must_fail_check.py: the lint refuses a bare must-fail in
code (a top-level form and a defmacro template), ignores comments and
strings, honours a same-line declaration, and --convert is idempotent."""
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from tools import must_fail_check as mfc

BOOK = '''; a (must-fail (thm nil)) in a comment is not code
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(defconst *s* "(must-fail (thm nil))")
(must-fail (defthm a nil))
(defmacro t-mf (name) `(must-fail
  (defthm ,name nil)))
#| (must-fail (thm nil)) |#
(must-fail (defun 5)) ; must-fail-ok: a malformed defun is the claim
'''


class MustFailCheckTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "tests/acl2").mkdir(parents=True)
        self.book = self.root / "tests/acl2/x-tests.lisp"
        self.book.write_text(BOOK)

    def tearDown(self):
        self.tmp.cleanup()

    def test_bare_sites_in_code_only(self):
        sites = mfc.bare_sites(BOOK)
        self.assertEqual([(line, ok) for line, _, ok in sites],
                         [(5, False), (6, False), (9, True)])

    def test_lint_fails_then_convert_passes(self):
        self.assertEqual(mfc.main(["--root", str(self.root)]), 1)
        self.assertEqual(mfc.main(["--root", str(self.root), "--convert"]), 0)
        text = self.book.read_text()
        self.assertIn('(include-book "must-fail-checked")', text)
        self.assertNotIn("std/testing/must-fail", text)
        self.assertIn("(must-fail-checked (defthm a nil))", text)
        self.assertIn("`(must-fail-checked\n", text)
        # the declared site, the comment and the string are left alone
        self.assertIn("(must-fail (defun 5)) ; must-fail-ok:", text)
        self.assertIn('"(must-fail (thm nil))"', text)
        self.assertIn("#| (must-fail (thm nil)) |#", text)
        # idempotent
        self.assertEqual(mfc.convert_text(text), text)

    def test_checked_is_not_bare(self):
        self.assertEqual(mfc.bare_sites("(must-fail-checked (thm nil))"), [])
        self.assertEqual(len(mfc.bare_sites("(must-fail! (thm nil))")), 1)


if __name__ == "__main__":
    unittest.main()
