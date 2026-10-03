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

    def test_function_names_comments_and_strings_are_not_globals(self):
        text = ("(fnn-owner-core 'fn-owner-open-peer peer)\n"
                "(fnn-owner-action 'fn-owner-outcome cid word)\n"
                "; (f-put-global 'fn-owner-commented x state)\n"
                "(defun f () \"(f-get-global 'fn-owner-quoted state)\")\n"
                "(f-get-global 'fn-store-sco-open state)\n")
        self.assertEqual(ogc.globals_of(text), [])

    def test_the_baseline_only_shrinks(self):
        found = {"host/a.lisp": ["fn-owner-a", "fn-owner-b"]}
        self.assertTrue(ogc.judge(found, {"host/a.lisp": 1}))
        self.assertTrue(ogc.judge(found, {"host/a.lisp": 3}))
        self.assertTrue(ogc.judge(found, {}))
        self.assertTrue(ogc.judge({}, {"host/a.lisp": 2}))
        self.assertEqual(ogc.judge(found, {"host/a.lisp": 2}), [])


class ParkedFilesTests(unittest.TestCase):
    """A parked host file (planning/host-parked.json: no build loads it) is not
    the running owner's, so its globals are not counted; one that is not
    parked is (2026-10-03, check-lane green)."""

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
