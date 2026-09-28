"""Teeth for tools/launcher_exit_check.py (lane lane-tools-2, g4): the rule
refuses packaging/fn as it stood before fb12148f8 (the heap probe's SBCL
ENOMEM, exit 1, forwarded as ACL2's refusal) and accepts it as fixed; it
refuses each unclassified shell and raw-Lisp shape in
tests/fixtures/launcher-exit/ by file:line and accepts the classified twins
(so each refusal is for the named reason, never a parse accident); and it
passes the tree's own launchers and host/."""
from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import launcher_exit_check as rule  # noqa: E402

FIXTURES = ROOT / "tests" / "fixtures" / "launcher-exit"
PREFIX = "tests/fixtures/launcher-exit/"


def where(lines):
    return [line.split(": ", 1)[0] for line in lines]


class LauncherExitRuleTests(unittest.TestCase):
    def test_the_launcher_before_fb12148f8_is_refused(self):
        refused = rule.check([FIXTURES / "fn-before-fb12148f8.sh"])
        self.assertEqual(where(refused), [PREFIX + "fn-before-fb12148f8.sh:90"])
        self.assertIn("forwards the child's status $status unclassified", refused[0])

    def test_the_launcher_after_fb12148f8_is_accepted(self):
        self.assertEqual(rule.check([FIXTURES / "fn-after-fb12148f8.sh"]), [])

    def test_each_shell_shape_is_refused(self):
        refused = rule.check([FIXTURES / "refused.sh"])
        self.assertEqual(where(refused), [PREFIX + "refused.sh:%d" % n
                                          for n in (5, 6, 7, 10, 12, 14)])

    def test_the_classified_shell_twin_is_accepted(self):
        self.assertEqual(rule.check([FIXTURES / "accepted.sh"]), [])

    def test_each_lisp_shape_is_refused(self):
        refused = rule.check([FIXTURES / "refused.lisp"])
        self.assertEqual(where(refused), [PREFIX + "refused.lisp:%d" % n
                                          for n in (6, 12, 17, 20)])
        self.assertIn("its unknown arm refuses", refused[0])
        self.assertIn("no arm for an unknown nonzero status", refused[1])
        self.assertIn("used unclassified", refused[2])
        self.assertIn("its unknown arm refuses", refused[3])

    def test_the_classified_lisp_twin_is_accepted(self):
        self.assertEqual(rule.check([FIXTURES / "accepted.lisp"]), [])

    def test_the_status_wrapper_is_a_source_across_files(self):
        # fx-run lives in one file; its callers are judged in another.
        self.assertIn("fx-run", rule.status_functions(rule.definitions(
            __import__("ledger").Reader((FIXTURES / "accepted.lisp").read_text()).top_level())))

    def test_the_tree_passes(self):
        self.assertEqual(rule.check(), [])
        names = {p.name for p in rule.shell_launchers()}
        self.assertIn("fn", names)
        self.assertNotIn("fn-native", names)  # a link to fn, read once


if __name__ == "__main__":
    unittest.main()
