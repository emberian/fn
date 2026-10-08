"""Run the live wrapper with its actual ACL2 phase step, without an image."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class PhasedReconfigurationAdapterTests(unittest.TestCase):
    def test_capture_conversion_and_lock_placement(self):
        result = subprocess.run(
            ["sbcl", "--script", "tests/native_reconfig_phased_raw-mock.lisp"],
            cwd=ROOT, text=True, capture_output=True, timeout=60,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("10 cases passed", result.stdout)

    def test_history_cost_fixture_stays_admissible(self):
        from tests.test_native_live_reconfiguration import GENERATIONS, history_policy_requests

        requests = list(history_policy_requests(GENERATIONS))
        self.assertTrue(all(request[:2] == ("group", "policy") for request in requests))
        inputs = "".join(f"{name}\n{status}\n" for _, _, name, status in requests)
        result = subprocess.run(
            ["sbcl", "--script", "tests/native_reconfig_history_raw.lisp"],
            cwd=ROOT, input=inputs, text=True, capture_output=True, timeout=60,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("fn.depth.20 refused before authorization; projection 508 -> 520, ceiling 510", result.stdout)
        self.assertIn("500 policy generations, 20 deep creates, occupied-name candidate admitted", result.stdout)
        self.assertIn("occupied empty 00000542.cfg, limit 2048: ACL2 (:fault :decode nil), host namespace fault", result.stdout)


if __name__ == "__main__":
    unittest.main()
