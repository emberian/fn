"""tools/protocol_rows.py: the tests pinning each protocol row's literal text (item 55)."""

from __future__ import annotations

import contextlib
import io
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import protocol_rows  # noqa: E402

TABLE = '''; a comment
(defconst *fn-nntp-served-command-table*
  '(("CAPABILITIES" "HELP")
    ("AUTHINFO" "COMPRESS")))

(defun fn-nntp-keyword-in-rowp (keyword row) row)
'''

BOOK = '''(defun fn-x-capability-lines (p)
  (list (fn-nntp-string-octets "VERSION 2")
        (fn-nntp-string-octets "COMPRESS DEFLATE")))
(defun fn-x-other ()
  (fn-nntp-string-octets "NOT A CAPABILITY"))
'''


class ParseTests(unittest.TestCase):
    def test_table_rows_read_from_the_defconst(self):
        self.assertEqual(protocol_rows.table_rows(TABLE),
                         [["CAPABILITIES", "HELP"], ["AUTHINFO", "COMPRESS"]])

    def test_capability_lines_come_only_from_capability_functions(self):
        self.assertEqual(protocol_rows.capability_lines({"books/x.lisp": BOOK}),
                         [("books/x.lisp", "VERSION 2"), ("books/x.lisp", "COMPRESS DEFLATE")])

    def test_runnable_names(self):
        self.assertEqual(protocol_rows.runnable("tests/acl2/nntp-help-tests.lisp"),
                         "tests/acl2/nntp-help-tests")
        self.assertEqual(protocol_rows.runnable("tests/test_native_outside_in.py"),
                         "tests.test_native_outside_in")
        self.assertEqual(protocol_rows.runnable("tests/fake_node.py"), "tests/fake_node.py")
        self.assertEqual(protocol_rows.runnable("books/nntp-auth.lisp"), "books/nntp-auth.lisp")


class ChangedTests(unittest.TestCase):
    def test_a_changed_row_is_named_both_ways(self):
        before = [{"kind": "help", "text": "AUTHINFO STARTTLS", "where": "b"},
                  {"kind": "keyword", "text": "HELP", "where": "b"}]
        after = [{"kind": "help", "text": "AUTHINFO STARTTLS COMPRESS", "where": "b"},
                 {"kind": "keyword", "text": "HELP", "where": "b"}]
        with mock.patch.object(protocol_rows, "rows",
                               side_effect=lambda base=None: before if base else after):
            found = protocol_rows.changed("origin/dev")
        self.assertEqual([(r["text"], r["change"]) for r in found],
                         [("AUTHINFO STARTTLS", "removed"),
                          ("AUTHINFO STARTTLS COMPRESS", "added")])


class RealTreeTests(unittest.TestCase):
    """The tree's own table: the row COMPRESS joined is pinned by nntp-help-tests
    (compress-7's merge red), and the dispatch term's book is named."""

    def test_the_compress_rows_and_their_pins(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(protocol_rows.main(["--keyword", "compress"]), 0)
        text = out.getvalue()
        self.assertIn("help       'AUTHINFO STARTTLS XREDEEM COMPRESS'", text)
        self.assertIn("tests/acl2/nntp-help-tests", text)
        self.assertIn("books/nntp-help.lisp", text)  # fn-nntp-served-keywordp-unfolds

    def test_roots_are_deduplicated_names(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            protocol_rows.main(["--keyword", "COMPRESS", "--roots"])
        names = out.getvalue().split()
        self.assertEqual(len(names), len(set(names)))
        self.assertIn("tests/acl2/nntp-help-tests", names)

    def test_no_change_against_the_head(self):
        err = io.StringIO()
        with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(protocol_rows.main(["--changed", "HEAD"]), 0)
        # the working tree may differ from HEAD only in files other than the table's
        self.assertTrue("no row changed" in err.getvalue() or err.getvalue() == "")


if __name__ == "__main__":
    unittest.main()
