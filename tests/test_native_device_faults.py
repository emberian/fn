"""Actual raw device-perform under deterministic persistent/volatile fault injection."""
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class DeviceFaultTests(unittest.TestCase):
    def run_control(self, mutant=None):
        env = dict(os.environ)
        env.pop("FN2_DEVICE_FAULT_MUTANT", None)
        if mutant:
            env["FN2_DEVICE_FAULT_MUTANT"] = mutant
        return subprocess.run(["sbcl", "--script", "tests/native-device-faults.lsp"],
                              cwd=ROOT, env=env, text=True, capture_output=True, timeout=20)

    def test_real_boundary_preserves_partial_effects(self):
        result = self.run_control()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("DEVICE FAULT CONTROLS PASS", result.stdout)

    def test_wrong_retry_rollback_and_errno_are_detected(self):
        for mutant, diagnostic in (("retry", "A logical operation retried its syscall"),
                                   ("rollback", "Unreported write prefix changed"),
                                   ("errno", "Device errno was not preserved")):
            with self.subTest(mutant=mutant):
                result = self.run_control(mutant)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(diagnostic, result.stderr)
                self.assertNotIn("DEVICE FAULT CONTROLS PASS", result.stdout)


if __name__ == "__main__":
    unittest.main()
