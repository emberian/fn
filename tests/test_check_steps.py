"""tools/check_steps.py: every step of `make check` runs, and the table names the red ones."""
from __future__ import annotations

import io
import pathlib
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_steps  # noqa: E402

PY = sys.executable


class CheckStepsTests(unittest.TestCase):
    def test_a_red_step_does_not_stop_the_next_and_the_summary_fails(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = pathlib.Path(temporary) / "steps"
            out = io.StringIO()
            with redirect_stdout(out):
                self.assertEqual(check_steps.main(["begin", str(directory)]), 0)
                self.assertEqual(check_steps.main(
                    ["run", str(directory), "--", PY, "-c",
                     "print('checked 3 files'); print('harness_check: arity mismatch at x:1');"
                     " raise SystemExit(2)"]), 0)
                self.assertEqual(check_steps.main(
                    ["run", str(directory), "--", PY, "-c", "print('all green')"]), 0)
                verdict = check_steps.main(["summary", str(directory)])
            self.assertEqual(verdict, 1)
            text = out.getvalue()
            self.assertIn("all green", text)
            self.assertIn("== check: 2 steps, 1 failed", text)
            self.assertIn("exit 2", text)
            self.assertIn("harness_check: arity mismatch at x:1", text)
            rows = check_steps.read_results(directory)
            self.assertEqual([row["exit"] for row in rows], [2, 0])
            self.assertEqual(rows[1]["finding"], "")

    def test_all_green_passes_and_nothing_recorded_fails(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = pathlib.Path(temporary)
            with redirect_stdout(io.StringIO()):
                self.assertEqual(check_steps.summary(directory), 1)
                check_steps.run(directory, [PY, "-c", "pass"])
                self.assertEqual(check_steps.summary(directory), 0)

    def test_names_and_findings(self):
        self.assertEqual(check_steps.step_name(["python3", "tools/cite_check.py", "--summary"]),
                         "cite_check")
        self.assertEqual(check_steps.step_name(
            ["python3", "-m", "unittest", "-q", "tests.test_x.Y"]), "tests.test_x.Y")
        self.assertEqual(check_steps.first_finding(["ok", "3 stale citations", "tail"]),
                         "3 stale citations")
        self.assertEqual(check_steps.first_finding(["ok", "", "last words", ""]), "last words")
        # harness_check: the counted finding, not a waiver line that says "not"
        self.assertEqual(check_steps.first_finding(
            ["harness_check acl2-arity: 2 findings (11769 definitions)",
             "  waiver-ok x.py:1: environment -- it reads a command, not its exit"]),
            "harness_check acl2-arity: 2 findings (11769 definitions)")
        self.assertEqual(check_steps.first_finding(
            ["spec-cite: 5721 citations; 323 known stale",
             "  UNDEFINED fn-x: specs/host.md:596"]), "UNDEFINED fn-x: specs/host.md:596")


if __name__ == "__main__":
    unittest.main()
