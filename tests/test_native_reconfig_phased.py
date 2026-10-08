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


if __name__ == "__main__":
    unittest.main()
