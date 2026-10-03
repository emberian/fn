"""Actual startup failed-open and final authority settlement composition."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class OwnerStartupCustodySourceTests(unittest.TestCase):
    def test_failed_open_debt_is_retained_through_final_settlement(self):
        result = subprocess.run(
            [shutil.which("sbcl"), "--script", str(ROOT / "tests/native_owner_startup_custody_source.lisp")],
            cwd=ROOT, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS composed startup close-debt authority", result.stdout)

if __name__ == "__main__":
    unittest.main()
