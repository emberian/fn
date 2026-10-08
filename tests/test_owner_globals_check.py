"""tools/owner_globals_check.py: what it counts and what it leaves alone."""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
import owner_globals_check as ogc  # noqa: E402


class OwnerGlobalsCheckTests(unittest.TestCase):
    def test_accessor_names_are_counted_once(self):
        text = ("(f-put-global 'fn-owner-output x state)\n"
                "(f-get-global 'fn-owner-output state)\n"
                "(boundp-global 'fn-owner-log-line state)\n"
                "(fnn-owner-list-global 'fn-owner-feed-command)\n")
        self.assertEqual(ogc.globals_of(text),
                         ["fn-owner-feed-command", "fn-owner-log-line", "fn-owner-output"])

    def test_wrapper_quoted_symbols_in_any_argument(self):
        text = """(fn-owner-payload-view-global 'fn-owner-sco-inflight state)
          (FN-OWNER-PAYLOAD-VIEW-GLOBAL (QUOTE FN-OWNER-SCO-INFLIGHT) state)
          (custom-global state 'fn-owner-root)
          (custom-global state (quote fn-owner-later))
          (fnn-owner-core 'fn-owner-function)
          (custom-global '(fn-owner-list))
          (custom-global #'fn-owner-function)
          ; (custom-global 'fn-owner-comment)
          (f "(custom-global 'fn-owner-string)")"""
        self.assertEqual(ogc.globals_of(text),
                         ['fn-owner-later', 'fn-owner-root', 'fn-owner-sco-inflight'])

    def test_function_names_comments_and_strings_are_not_globals(self):
        text = ("(fnn-owner-core 'fn-owner-open-peer peer)\n"
                "(fnn-owner-action 'fn-owner-outcome cid word)\n"
                "; (f-put-global 'fn-owner-commented x state)\n"
                "(defun f () \"(f-get-global 'fn-owner-quoted state)\")\n"
                "(f-get-global 'fn-store-sco-open state)\n")
        self.assertEqual(ogc.globals_of(text), [])

    def test_books_funnels_remain_counted_until_state_moves(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "books").mkdir()
            (root / "books" / "owner-retain-state.lisp").write_text(
                "(f-get-global 'fn-owner-retain-carry state)\n"
                "(f-put-global 'fn-owner-retain-carry carry state)\n")
            self.assertEqual(ogc.scan(root), {
                "books/owner-retain-state.lisp": ["fn-owner-retain-carry"]})
            self.assertTrue(ogc.judge(ogc.scan(root), {}))

    def test_the_baseline_only_shrinks(self):
        found = {"host/a.lisp": ["fn-owner-a", "fn-owner-b"]}
        self.assertTrue(ogc.judge(found, {"host/a.lisp": 1}))
        self.assertTrue(ogc.judge(found, {"host/a.lisp": 3}))
        self.assertTrue(ogc.judge(found, {}))
        self.assertTrue(ogc.judge({}, {"host/a.lisp": 2}))
        self.assertEqual(ogc.judge(found, {"host/a.lisp": 2}), [])


class RaiseNeedsAReasonTests(unittest.TestCase):
    """--write-baseline refuses a raise (or a new file) without --reason and keeps one dated line with it."""

    def run_write(self, argv, baseline):
        import json, tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "host").mkdir()
            (root / "host" / "a-host.lisp").write_text(
                "(defun f (state) (f-put-global 'fn-owner-x 1 (f-put-global 'fn-owner-y 2 state)))\n")
            path = root / "base.json"
            path.write_text(json.dumps(baseline))
            code = ogc.main(["--root", str(root), "--baseline", str(path), "--write-baseline"] + argv)
            return code, json.loads(path.read_text())

    def test_targeted_shrink_keeps_existing_red(self):
        code, written = self.run_write(["--lower-to", "host/a-host.lisp=0", "--reason", "OWNER-CARRIER-GLOBALS: moved"],
                                       {"host/a-host.lisp": 1, "host/other.lisp": 3})
        self.assertEqual(code, 0)
        self.assertEqual(written["host/a-host.lisp"], 0)
        self.assertEqual(written["host/other.lisp"], 3)
        self.assertIn("OWNER-CARRIER-GLOBALS", written["_reasons"][0])
        code, written = self.run_write(["--lower-to", "host/a-host.lisp=2"],
                                       {"host/a-host.lisp": 1})
        self.assertEqual(code, 1)
        self.assertEqual(written["host/a-host.lisp"], 1)

    def test_a_raise_without_a_reason_is_refused(self):
        code, written = self.run_write([], {"host/a-host.lisp": 1})
        self.assertEqual(code, 1)
        self.assertEqual(written, {"host/a-host.lisp": 1})

    def test_a_raise_with_a_reason_keeps_one_dated_line_and_the_check_ignores_it(self):
        import tempfile
        from pathlib import Path
        from unittest import mock
        from tools import ratchet
        with tempfile.TemporaryDirectory() as d:
            acks = Path(d) / "ACKS.md"
            acks.write_text("ratchet:owner_globals_check:host/a-host.lisp \u2014 two arrived "
                            "\u2014 the test\n")
            with mock.patch.object(ratchet, "ACKS", acks):
                code, written = self.run_write(["--reason", "two arrived"], {"host/a-host.lisp": 1})
        self.assertEqual(code, 0)
        self.assertEqual(written["host/a-host.lisp"], 2)
        self.assertEqual(len(written["_reasons"]), 1)
        self.assertIn("two arrived", written["_reasons"][0])
        self.assertIn("host/a-host.lisp 1->2", written["_reasons"][0])


class NamedRaiseTests(unittest.TestCase):
    """--raise-to FILE=N --admit NAME raises one row by exactly the named globals."""

    LISP = ("(defun f (state) (f-put-global 'fn-owner-x 1 (f-put-global 'fn-owner-y 2 "
            "(f-put-global 'fn-owner-z 3 state))))\n")

    def run_raise(self, argv, baseline=None, acked=True):
        import json, tempfile
        from pathlib import Path
        from unittest import mock
        from tools import ratchet
        baseline = {"host/a-host.lisp": 1, "host/b-host.lisp": 4} if baseline is None else baseline
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "host").mkdir()
            (root / "host" / "a-host.lisp").write_text(self.LISP)
            path = root / "base.json"
            path.write_text(json.dumps(baseline))
            acks = root / "ACKS.md"
            acks.write_text("ratchet:owner_globals_check:host/a-host.lisp \u2014 named \u2014 the test\n"
                            if acked else "")
            with mock.patch.object(ratchet, "ACKS", acks):
                code = ogc.main(["--root", str(root), "--baseline", str(path), "--write-baseline"] + argv)
            return code, json.loads(path.read_text())

    ARGS = ["--reason", "y joins", "--raise-to", "host/a-host.lisp=2", "--admit", "fn-owner-y"]

    def test_one_named_global_raises_one_row_and_touches_nothing_else(self):
        code, written = self.run_raise(self.ARGS)
        self.assertEqual(code, 0)
        self.assertEqual(written["host/a-host.lisp"], 2)
        self.assertEqual(written["host/b-host.lisp"], 4)
        self.assertIn("admitting fn-owner-y", written["_reasons"][0])
        self.assertIn("host/a-host.lisp 1->2", written["_reasons"][0])

    def test_the_check_is_still_red_after_a_partial_raise(self):
        found = {"host/a-host.lisp": ["fn-owner-x", "fn-owner-y", "fn-owner-z"]}
        self.assertTrue(ogc.judge(found, {"host/a-host.lisp": 2}))

    def test_refusals(self):
        for argv, acked in (
                (["--reason", "r", "--raise-to", "host/a-host.lisp=3", "--admit", "fn-owner-y"], True),  # count != names
                (["--reason", "r", "--raise-to", "host/a-host.lisp=4", "--admit", "a", "--admit", "b", "--admit", "c"], True),  # beyond present
                (["--reason", "r", "--raise-to", "host/a-host.lisp=2", "--admit", "fn-owner-q"], True),  # not a global
                (["--raise-to", "host/a-host.lisp=2", "--admit", "fn-owner-y"], True),  # no reason
                (["--reason", "r", "--raise-to", "host/a-host.lisp=1", "--admit", "fn-owner-y"], True),  # not a raise
                (self.ARGS, False)):  # no ACKS line
            code, written = self.run_raise(argv, acked=acked)
            self.assertEqual(code, 1, argv)
            self.assertEqual(written["host/a-host.lisp"], 1, argv)
            self.assertNotIn("_reasons", written, argv)


class ParkedFilesTests(unittest.TestCase):
    """A parked host file (planning/host-parked.json: no build loads it) is not
    the running owner's, so its globals are not counted; one that is not
    parked is (2026-10-03, check-lane green)."""

    def test_included_parked_wrapper_is_counted_transitively(self):
        import json, tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'host').mkdir(); (root / 'planning').mkdir()
            (root / 'host/live.lisp').write_text('(include-book "middle")')
            (root / 'host/middle.lisp').write_text('(include-book "payload-view-host")')
            (root / 'host/payload-view-host.lisp').write_text(
                "(fn-owner-payload-view-global 'fn-owner-sco-inflight state)")
            (root / 'planning/host-parked.json').write_text(json.dumps({'parked': {
                'host/middle.lisp': 'old ld inventory',
                'host/payload-view-host.lisp': 'LIVE, NOT PARKED'}}))
            self.assertEqual(ogc.scan(root), {
                'host/payload-view-host.lisp': ['fn-owner-sco-inflight']})

    def test_parked_is_skipped_and_the_rest_counted(self):
        import json, tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "host").mkdir()
            (root / "planning").mkdir()
            text = "(defun f (state) (f-put-global 'fn-owner-x 1 state))\n"
            (root / "host" / "parked-host.lisp").write_text(text)
            (root / "host" / "live-host.lisp").write_text(text)
            (root / "planning" / "host-parked.json").write_text(
                json.dumps({"parked": {"host/parked-host.lisp": "test"}}))
            found = ogc.scan(root)
        self.assertEqual(sorted(found), ["host/live-host.lisp"])


if __name__ == "__main__":
    unittest.main()
