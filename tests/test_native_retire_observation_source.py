"""SCN-1095 actual-source retire observation fixture; no image qualification."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SBCL = os.environ.get("FN_SBCL") or shutil.which("sbcl")


@unittest.skipUnless(SBCL, "SBCL is required for the actual-source retire fixture")
class RetireObservationSourceTests(unittest.TestCase):
    def test_real_loop_expires_without_stopping_owner_or_printing_report(self):
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "retire-report.txt"
            report.write_text("fixture-retire-report\n")
            result = subprocess.run(
                [SBCL, "--script", str(ROOT / "tests/native_retire_observation_source-mock.lisp"), str(report)],
                cwd=ROOT, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("live-expiry elapsed=60", result.stdout)
        self.assertIn("held-expiry elapsed=60", result.stdout)
        self.assertIn("drain-plus-allowance-expiry elapsed=70", result.stdout)
        self.assertIn("SOURCE RETIRE OBSERVATION PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
