"""tools/hazard_rules_check.py: rows come from the world's var_lhs, the
baseline only shrinks, and a dump without the field is refused by name."""
import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import hazard_rules_check as hz  # noqa: E402


def dump(*theorems):
    return {"theorems": [dict({"hyps": [], "concl": [], "classes": [], "hinted": []}, **t)
                         for t in theorems], "functions": []}


TREE = "/x/fn/books/"
HAZARD = {"name": "FN-OQW-BATCH-EFFECT-ORDER", "book": TREE + "owner-queued-work.lisp",
          "var_lhs": ["CAR"]}
TARGETED = {"name": "FN-FS-ACTOR-JOINED-IS-FINAL", "book": TREE + "failure-scope.lisp",
            "var_lhs": ["FN-FS-ACTOR-STEP"]}
SYSTEM = {"name": "DEFAULT-CAR", "book": None, "var_lhs": ["CAR"]}


class RowsTests(unittest.TestCase):
    def test_only_tree_books_and_hazard_heads(self):
        rows = hz.rows_of(dump(HAZARD, TARGETED, SYSTEM))
        self.assertEqual(sorted(rows), ["fn-oqw-batch-effect-order|car"])
        self.assertEqual(rows["fn-oqw-batch-effect-order|car"]["book"],
                         "books/owner-queued-work.lisp")

    def test_a_dump_without_var_lhs_is_refused_not_read_as_empty(self):
        old = {k: v for k, v in HAZARD.items() if k != "var_lhs"}
        with self.assertRaises(hz.DumpError):
            hz.rows_of(dump(old))

    def test_census_names_the_defining_line(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "books").mkdir()
            (root / "books" / "owner-queued-work.lisp").write_text(
                "; x\n(defun f (x) x)\n\n(defthm fn-oqw-batch-effect-order\n  t)\n")
            lines = hz.census(hz.rows_of(dump(HAZARD)), root)
        self.assertEqual(lines[1], "fn-oqw-batch-effect-order\t"
                                   "books/owner-queued-work.lisp:4\tcar")


class BaselineTests(unittest.TestCase):
    def run_main(self, world, baseline, *args):
        out = io.StringIO()
        with patch.object(hz, "BASELINE", baseline), patch.object(hz, "ROOT", baseline.parent), \
                redirect_stdout(out):
            code = hz.main(["--world", str(world), *args])
        return code, out.getvalue()

    def test_new_row_fails_and_stale_row_is_named(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            world = temp / "world.json"
            world.write_text(json.dumps(dump(HAZARD)))
            baseline = temp / "baseline.json"
            baseline.write_text(json.dumps({"rows": {"gone|consp": 1}}))
            code, out = self.run_main(world, baseline)
        self.assertEqual(code, 1)
        self.assertIn("NEW fn-oqw-batch-effect-order|car", out)
        self.assertIn("stale gone|consp", out)

    def test_write_refuses_to_add_a_row(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            world = temp / "world.json"
            world.write_text(json.dumps(dump(HAZARD)))
            baseline = temp / "baseline.json"
            baseline.write_text(json.dumps({"rows": {}}))
            with patch.object(hz.ratchet, "acked", lambda acks=None: set()):
                code, out = self.run_main(world, baseline, "--write")
            self.assertEqual(code, 1)
            self.assertIn("refusing to raise", out)
            self.assertEqual(json.loads(baseline.read_text())["rows"], {})

    def test_write_lowers_a_stale_row(self):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            world = temp / "world.json"
            world.write_text(json.dumps(dump(HAZARD)))
            baseline = temp / "baseline.json"
            baseline.write_text(json.dumps({"rows": {"fn-oqw-batch-effect-order|car": 1,
                                                     "gone|consp": 1}}))
            code, _ = self.run_main(world, baseline, "--write")
            self.assertEqual(code, 0)
            self.assertEqual(json.loads(baseline.read_text())["rows"],
                             {"fn-oqw-batch-effect-order|car": 1})


if __name__ == "__main__":
    unittest.main()
