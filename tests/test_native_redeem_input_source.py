"""SCN-1132 actual-source redeem input fixture; no saved-image claim."""
import shutil
import subprocess
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class RedeemInputSourceTests(unittest.TestCase):
    def test_bounded_retention_and_wire_edges(self):
        result = subprocess.run([shutil.which("sbcl"), "--script", "tests/native_redeem_input_source.lisp"], cwd=ROOT, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("REDEEM INPUT SOURCE PASSED", result.stdout)
