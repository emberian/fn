"""Live route control wiring; native activation still needs a matching image."""
from pathlib import Path
from types import SimpleNamespace
import unittest

from tools.resilience.adapters.bp_node import BpRun, HarnessFailure, control_path
from tools.resilience import schedule_points


class BpControlAdapterTests(unittest.TestCase):
    def fixture(self, variant):
        scenario = next(s for s in schedule_points.scenarios()
                        if s.id == "schedule-receipt-observed-" + variant)
        run = BpRun(scenario, Path("/image"), Path("/scratch"))
        run.relay = SimpleNamespace(port=24680)
        return run

    def test_only_reorder_receiver_requests_live_control_after_positional_args(self):
        run = self.fixture("reorder")
        argv = run.node_argv(True, False, 12345)
        self.assertEqual(argv[-2:], ["--control-config", str(run.configs[True])])
        self.assertEqual(argv[-8:-2], ["3600000", "2", "32", "1048576", "0", "0"])
        self.assertNotIn("--control-config", run.node_argv(False, False, 12345))
        for variant in ("duplicate", "lose-completion"):
            self.assertNotIn("--control-config", self.fixture(variant).node_argv(True, False, 12345))

    def test_control_announcement_must_name_the_actual_receiver_store(self):
        path = Path("/scratch/receiver-store/control.sock")
        self.assertEqual(control_path(b"BP NODE CONTROL " + bytes(path) + b"\n", path), str(path))
        for output in (b"BP NODE LISTENING 12345\n", b"BP NODE CONTROL /other/control.sock\n",
                       b"BP NODE CONTROL " + bytes(path) + b"\nBP NODE CONTROL /other\n"):
            with self.assertRaises(HarnessFailure):
                control_path(output, path)


if __name__ == "__main__":
    unittest.main()
