"""tools/release_sequence.py: the release order is D37's sequence, not a number."""
from __future__ import annotations

import contextlib
import io
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import release_sequence as rs  # noqa: E402


class ParseTests(unittest.TestCase):
    def test_any_number_of_components(self):
        self.assertEqual(rs.parse("6.6.0"), (6, 6, 0))
        self.assertEqual(rs.parse("6.6.6.6.6"), (6, 6, 6, 6, 6))
        self.assertEqual(rs.parse("7"), (7,))

    def test_malformed(self):
        for bad in ["", "6..6", "6.6.", "6.06.0", "6.6.0-rc1", "v6.6.0", " 6.6.0", "6.6.0\n"]:
            with self.assertRaises(ValueError, msg=bad):
                rs.parse(bad)


class SequenceTests(unittest.TestCase):
    ORDER = ["6.6.0", "6.6.1", "6.6.2", "6.6.3", "6.6.4", "6.6.5",
             "6.7.0", "6.7.1", "6.7.2", "6.7.10", "6.7.41",
             "6.6.6", "6.6.6.6", "6.6.6.6.6"]

    def test_first_is_660(self):
        self.assertEqual(rs.first(), "6.6.0")
        self.assertTrue(rs.is_next(None, "6.6.0"))
        self.assertFalse(rs.is_next(None, "6.7.0"))

    def test_positions_follow_the_sequence_not_the_numbers(self):
        pos = [rs.position(v) for v in self.ORDER]
        self.assertEqual(pos, sorted(pos))
        self.assertEqual(len(set(pos)), len(pos))
        # The numeric order disagrees exactly where ember's sequence does.
        self.assertLess(rs.position("6.6.5"), rs.position("6.7.0"))
        self.assertLess(rs.position("6.7.41"), rs.position("6.6.6"))
        self.assertLess(rs.position("6.7.9"), rs.position("6.7.10"))

    def test_next(self):
        self.assertEqual(rs.next("6.6.0"), "6.6.1")
        self.assertEqual(rs.next("6.6.5"), "6.7.0")
        self.assertEqual(rs.next("6.7.0"), "6.7.1")
        self.assertEqual(rs.next("6.7.9"), "6.7.10")
        self.assertEqual(rs.next("6.7.3", final=True), "6.6.6")
        self.assertEqual(rs.next("6.6.6"), "6.6.6.6")
        self.assertEqual(rs.next("6.6.6.6"), "6.6.6.6.6")
        with self.assertRaises(ValueError):
            rs.next("6.6.2", final=True)

    def test_is_next(self):
        for a, b in zip(self.ORDER, self.ORDER[1:]):
            if a in ("6.7.2", "6.7.10"):
                continue  # the ORDER list skips counter entries there
            self.assertTrue(rs.is_next(a, b), (a, b))
        self.assertTrue(rs.is_next("6.7.2", "6.7.3"))
        for a, b in [("6.6.5", "6.6.6"),   # the 6.7.x series comes first
                     ("6.6.0", "6.6.2"), ("6.7.0", "6.7.2"), ("6.6.6", "6.7.0"),
                     ("6.6.6", "6.6.6.6.6"), ("6.6.1", "6.6.1"), ("6.7.1", "6.7.01")]:
            self.assertFalse(rs.is_next(a, b), (a, b))

    def test_not_in_sequence(self):
        for v in ["6.6.7", "6.8.0", "6.6.6.7", "6.7", "6.6.6.66", "0.1.0", "5.0.1", "6.7.01"]:
            with self.assertRaises(ValueError, msg=v):
                rs.position(v)

    def test_newest_by_position(self):
        self.assertEqual(rs.newest(["6.7.12", "6.6.6", "6.7.3"]), "6.6.6")
        self.assertEqual(rs.newest(["6.6.5", "6.7.0"]), "6.7.0")
        self.assertIsNone(rs.newest([]))


class PrehistoryTests(unittest.TestCase):
    PRE = ["v1.0.0", "v2.0.0", "v3.0.0", "v4.0.0", "v5.0.0"]

    def test_prehistory_sorts_first_but_is_not_a_release(self):
        self.assertLess(rs.position("5.0.0"), rs.position("6.6.0"))
        self.assertTrue(rs.is_prehistory("3.0.0"))
        self.assertFalse(rs.is_prehistory("6.6.0"))
        self.assertEqual(rs.first(), "6.6.0")

    def test_cut_check_ignores_prehistory_tags(self):
        self.assertTrue(rs.cut_check("6.6.0", self.PRE)[0])
        self.assertTrue(rs.cut_check("6.6.1", self.PRE + ["v6.6.0"])[0])
        self.assertFalse(rs.cut_check("6.6.1", self.PRE)[0])
        self.assertFalse(rs.cut_check("5.0.0", self.PRE[:4])[0])
        self.assertFalse(rs.cut_check("1.0.0", [])[0])


class CutCheckTests(unittest.TestCase):
    def test_first_cut(self):
        self.assertTrue(rs.cut_check("6.6.0", [])[0])
        ok, why = rs.cut_check("6.7.0", [])
        self.assertFalse(ok)
        self.assertIn("6.6.0", why)

    def test_follows_the_newest_tag(self):
        self.assertTrue(rs.cut_check("6.6.2", ["v6.6.0", "v6.6.1", "other"])[0])
        self.assertTrue(rs.cut_check("6.7.0", ["v6.6.5", "v6.6.4"])[0])
        self.assertTrue(rs.cut_check("6.6.6", ["v6.7.12"])[0])
        self.assertFalse(rs.cut_check("6.6.3", ["v6.6.1"])[0])
        self.assertFalse(rs.cut_check("6.6.1", ["v6.6.5"])[0])

    def test_own_tag_rerun_and_stale(self):
        self.assertTrue(rs.cut_check("6.6.1", ["v6.6.0", "v6.6.1"])[0])
        self.assertFalse(rs.cut_check("6.6.0", ["v6.6.0", "v6.6.1"])[0])

    def test_refusals(self):
        self.assertFalse(rs.cut_check("6.6.9", [])[0])
        self.assertFalse(rs.cut_check("6.6.1", ["v6.6.0", "v9.9.9"])[0])

    def test_cli(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(rs.main(["cut-check", "6.6.0"]), 0)
            self.assertEqual(rs.main(["cut-check", "6.6.1"]), 1)
            self.assertEqual(rs.main(["is-next", "6.6.5", "6.7.0"]), 0)
            self.assertEqual(rs.main(["next", "6.7.4", "--final"]), 0)
        self.assertEqual(out.getvalue().splitlines(),
                         ["6.6.0 is the first release",
                          "VERSION is 6.6.1, but no v* tag exists: VERSION must be 6.6.0",
                          "yes", "6.6.6"])


if __name__ == "__main__":
    unittest.main()
