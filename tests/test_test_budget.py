"""tools/test_budget.py: per-module wall time, and the three outcomes kept apart."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import test_budget  # noqa: E402


class TestBudgetRunner(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-test-budget-")
        self.directory = Path(self.temp.name)
        # A package of throwaway modules the child imports by dotted name.
        package = self.directory / "budgetcases"
        package.mkdir()
        (package / "__init__.py").write_text("")
        (package / "passing.py").write_text(textwrap.dedent("""
            import unittest
            class Passing(unittest.TestCase):
                def test_quick(self):
                    self.assertTrue(True)
        """))
        (package / "failing.py").write_text(textwrap.dedent("""
            import unittest
            class Failing(unittest.TestCase):
                def test_wrong(self):
                    self.assertEqual(1, 2)
        """))
        (package / "slow.py").write_text(textwrap.dedent("""
            import time, unittest
            class Slow(unittest.TestCase):
                def test_sleeps(self):
                    time.sleep(60)
        """))
        # Order-dependent: the second test reads what the first one left in a
        # shared world (a module global standing in for a class fixture or a
        # process-wide session).
        (package / "leaky.py").write_text(textwrap.dedent("""
            import unittest
            WORLD = {}
            class Leaky(unittest.TestCase):
                def test_a_writes(self):
                    WORLD["authority"] = "granted"
                def test_b_relies(self):
                    self.assertEqual(WORLD.get("authority"), "granted")
        """))
        # Every test skipped, one by a decorator and a class by setUpClass
        # (counted in testsRun and not, respectively): nothing executed.
        (package / "skipping.py").write_text(textwrap.dedent("""
            import unittest
            class Skipped(unittest.TestCase):
                @unittest.skip("no image")
                def test_needs_image(self):
                    pass
            class ClassSkipped(unittest.TestCase):
                @classmethod
                def setUpClass(cls):
                    raise unittest.SkipTest("no production image")
                def test_needs_production(self):
                    pass
        """))
        (package / "partial.py").write_text(textwrap.dedent("""
            import unittest
            class Partial(unittest.TestCase):
                def test_runs(self):
                    pass
                @unittest.skip("opt-in unset")
                def test_gated(self):
                    pass
        """))
        self.environment = mock.patch.dict(
            os.environ, {"PYTHONPATH": str(self.directory)
                         + os.pathsep + os.environ.get("PYTHONPATH", "")})
        self.environment.start()

    def tearDown(self):
        self.environment.stop()
        self.temp.cleanup()

    def run_module(self, name, budget):
        return test_budget.run_module(f"budgetcases.{name}", budget, None)

    def test_a_passing_module_reports_its_time_and_tests(self):
        record = self.run_module("passing", 60)
        self.assertTrue(record["passed"], record)
        self.assertFalse(record["over_budget"])
        self.assertEqual(record["tests"], 1)
        self.assertEqual(len(record["timings"]), 1)
        self.assertLess(record["seconds"], 60)

    def test_reverse_order_exposes_a_test_that_relies_on_an_earlier_one(self):
        forward = test_budget.run_module("budgetcases.leaky", 60, None)
        self.assertTrue(forward["passed"], forward)
        backward = test_budget.run_module("budgetcases.leaky", 60, None, "reverse")
        self.assertFalse(backward["passed"])
        self.assertFalse(backward["over_budget"])
        self.assertEqual((backward["tests"], backward["failures"]), (2, 1))
        self.assertEqual([name.rsplit(".", 1)[-1] for name, _ in backward["timings"]],
                         ["test_b_relies", "test_a_writes"])

    def test_a_test_over_its_own_budget_makes_the_module_over(self):
        with mock.patch.object(test_budget, "TEST_BUDGET_SECONDS", -1.0):
            record = self.run_module("passing", 60)
        self.assertTrue(record["over_budget"])
        self.assertFalse(record["terminated"])
        self.assertFalse(record["passed"])
        self.assertEqual(record["returncode"], 0)
        self.assertEqual([name.rsplit(".", 1)[-1] for name, _ in record["slow_tests"]],
                         ["test_quick"])
        self.assertIn("a test over", test_budget.summarize(record, 1))

    def test_a_failing_module_is_failed_not_over_budget(self):
        record = self.run_module("failing", 60)
        self.assertFalse(record["passed"])
        self.assertFalse(record["over_budget"])
        self.assertEqual(record["failures"], 1)

    def test_a_module_past_its_budget_is_terminated_and_reported_over(self):
        record = self.run_module("slow", 2)
        self.assertTrue(record["over_budget"])
        self.assertFalse(record["passed"])
        # Terminated near the budget, not after the test's 60 s.
        self.assertLess(record["seconds"], 2 + test_budget.GRACE_SECONDS + 5)

    def test_exit_codes_keep_failure_and_budget_apart(self):
        def invoke(*names, budget="30"):
            return subprocess.run(
                [sys.executable, str(ROOT / "tools" / "test_budget.py"), "--budget", budget,
                 *(f"budgetcases.{name}" for name in names)],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                env=os.environ.copy(), timeout=120).returncode
        self.assertEqual(invoke("passing"), 0)
        self.assertEqual(invoke("failing"), 1)
        self.assertEqual(invoke("slow", budget="2"), 2)
        self.assertEqual(invoke("failing", "slow", budget="2"), 3)

    def test_a_module_that_skipped_every_test_is_skipped_not_passed(self):
        record = self.run_module("skipping", 60)
        self.assertTrue(record["all_skipped"], record)
        self.assertFalse(record["passed"])
        self.assertEqual((record["executed"], record["skipped"]), (0, 2))
        line = test_budget.summarize(record, 1)
        self.assertIn("SKIPPED (2 of 2", line)
        self.assertIn("no production image", line)
        self.assertNotIn(" ok", line)

    def test_a_module_with_some_skips_passes_and_names_them(self):
        record = self.run_module("partial", 60)
        self.assertTrue(record["passed"], record)
        self.assertFalse(record["all_skipped"])
        self.assertEqual((record["executed"], record["skipped"]), (1, 1))
        line = test_budget.summarize(record, 1)
        self.assertIn("ok (1 skipped)", line)
        self.assertIn("opt-in unset", line)

    def test_all_skipped_has_its_own_exit_bit(self):
        def invoke(*arguments):
            return subprocess.run(
                [sys.executable, str(ROOT / "tools" / "test_budget.py"), "--budget", "30",
                 *arguments], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                env=os.environ.copy(), timeout=120)
        answer = invoke("budgetcases.skipping", "budgetcases.passing")
        self.assertEqual(answer.returncode, 4, answer.stdout)
        self.assertIn(b"1 SKIPPED (no test executed)", answer.stdout)
        self.assertEqual(invoke("budgetcases.skipping", "budgetcases.failing").returncode, 5)
        allowed = invoke("--allow-skipped", "budgetcases.skipping")
        self.assertEqual(allowed.returncode, 0)
        self.assertIn(b"SKIPPED (2 of 2", allowed.stdout)

    def test_verdict_of_a_one_log(self):
        for name, code, needle in (("skipping", 4, "SKIPPED (2 of 2"),
                                   ("partial", 0, "OK (1 ran, 1 skipped)"),
                                   ("failing", 1, "FAILED (1 failures")):
            log = self.directory / f"{name}.log"
            with open(log, "wb") as out:
                subprocess.run([sys.executable, str(ROOT / "tools" / "test_budget.py"),
                                "--one", f"budgetcases.{name}"], cwd=ROOT, stdout=out,
                               stderr=subprocess.STDOUT, env=os.environ.copy(), timeout=120)
            answer = subprocess.run(
                [sys.executable, str(ROOT / "tools" / "test_budget.py"), "--verdict", str(log)],
                cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(answer.returncode, code, answer.stdout)
            self.assertIn(needle, answer.stdout)

    def test_the_budget_can_be_lowered_never_raised(self):
        self.assertEqual(test_budget.budget_for("m", 300, {"m": 120}), 120)
        self.assertEqual(test_budget.budget_for("m", 300, {"m": 900}), 300)
        with self.assertRaises(SystemExit):
            test_budget.main(["--budget", "301", "tests.test_x"])


if __name__ == "__main__":
    unittest.main()
