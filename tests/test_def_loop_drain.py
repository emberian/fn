"""tools/def_loop_drain.py: three conversions reproduced byte for byte and three
named refusals.  The fixtures are excerpts of real books at the pre-conversion
revision (feed-pause, peer-config, extent-retire; nntp-responses, bp-route,
arena-forget); the expected outputs are the tool's own, each REPL-checked in
its book on persvati when the lane converted it (REGEN=1 rewrites them)."""
import os
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import def_loop_drain as d  # noqa: E402

FIX = ROOT / "tests" / "fixtures" / "def_loop_drain"


def run(name):
    text = (FIX / f"{name}.in.lisp").read_text()
    return d.analyse(text, name, {}), text


class Conversions(unittest.TestCase):
    def check(self, name, count):
        (conv, resid), text = run(name)
        self.assertEqual(resid, [])
        self.assertEqual(len(conv), count)
        out = d.apply_text(text, conv)
        expected = FIX / f"{name}.out.lisp"
        if os.environ.get("REGEN"):
            expected.write_text(out)
        self.assertEqual(out, expected.read_text())
        # the twin, its bridge and its verify-guards are gone
        self.assertEqual(d.loop_count(out), 0)
        self.assertNotIn("-loop-is-", out)
        self.assertNotIn("verify-guards", out)
        # and the result is still readable, with one def-loop per conversion
        forms, _ = d.book_forms(out)
        self.assertEqual(sum(1 for f in forms if f.kind == "def-loop"), count)

    def test_feed_pause_two_maps(self):
        self.check("feed-pause", 2)

    def test_peer_config_filter_map(self):
        self.check("peer-config", 1)

    def test_extent_retire_take_and_stobj_map(self):
        self.check("extent-retire", 2)


class Refusals(unittest.TestCase):
    def refused(self, name, why):
        (conv, resid), _ = run(name)
        self.assertEqual(conv, [])
        self.assertEqual([r[1] for r in resid], [why])

    def test_late_guard(self):
        self.refused("refuse-late-guard", "late-guard")

    def test_step_by_other_than_cdr(self):
        self.refused("refuse-step", "step")

    def test_two_lists(self):
        self.refused("refuse-two-list", "two-list")


class Reader(unittest.TestCase):
    def test_char_literals_and_strings_do_not_unbalance(self):
        forms, comments = d.book_forms('(defun f (x) ; c\n  (if (equal x #\\() "a)b" (quote (1))))\n')
        self.assertEqual(len(forms), 1)
        self.assertEqual(forms[0].name, "f")
        self.assertEqual(len(comments), 1)


class Ledger(unittest.TestCase):
    def test_library_bridge_by_shape(self):
        self.assertEqual(d.library_bridge("(def-loop f (x) :shape :map :over x)"),
                         "fn-dl-map-loop-is-revappend")
        self.assertEqual(d.library_bridge("(def-loop f (x) :shape :sum :over x)"),
                         "fn-dl-sum-loop-is-plus")
        self.assertEqual(d.library_bridge("(def-loop f (x) :shape :concat :over x)"),
                         "fn-dl-concat-loop-is-revappend")

    def test_loopish_names_only(self):
        self.assertTrue(d.LOOPISH.search("fn-x-loop-is-rev-onto"))
        self.assertFalse(d.LOOPISH.search("fn-x-is-sorted"))


if __name__ == "__main__":
    unittest.main()
