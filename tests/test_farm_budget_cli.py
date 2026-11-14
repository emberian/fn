"""Budget selection reaches submit without any remote work in these controls."""
import contextlib
import io
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import farm


class FarmBudgetCLI(unittest.TestCase):
    def invoke(self, extra):
        with mock.patch.dict(farm.HOSTS, {"budget-fixture": {}}, clear=True), \
             mock.patch.object(farm, "submit_jobs", return_value=1), \
             mock.patch.object(farm, "honour_reservation"), \
             mock.patch.object(farm, "submit", return_value="fixture-run") as submit, \
             contextlib.redirect_stdout(io.StringIO()), \
             contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(farm.main(["submit", "budget-fixture", "tests/example",
                                        "--lane", "--affected-by", "tests/example",
                                        *extra]), 0)
            return submit.call_args

    def test_budget_and_lane_reach_submit(self):
        call = self.invoke(["--budget-seconds", "270", "--timeout-seconds", "180"])
        self.assertEqual(call.kwargs["budget_seconds"], 270)
        self.assertTrue(call.kwargs["lane"])
        self.assertEqual(call.args[4], 180)
        self.assertEqual(call.args[5], ["tests/example"])

    def test_omitted_budget_preserves_default(self):
        self.assertIsNone(self.invoke([]).kwargs["budget_seconds"])

    def test_invalid_budget_refused_before_host_selection(self):
        with mock.patch.object(farm, "choose_host") as choose, \
             mock.patch.object(farm, "submit") as submit, \
             contextlib.redirect_stderr(io.StringIO()):
            for args in (["submit", "auto", "tests/example", "--budget-seconds", "0"],
                         ["submit", "auto", "tests/example", "--budget-seconds", "-1"],
                         ["status", "auto", "--budget-seconds", "270"]):
                with self.subTest(args=args), self.assertRaises(SystemExit) as error:
                    farm.main(args)
                self.assertEqual(error.exception.code, 2)
            choose.assert_not_called()
            submit.assert_not_called()


if __name__ == "__main__":
    unittest.main()
