"""Actual credit transitions and COMPLETE: controlled reservation/readmission trace."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class PostCreditSourceTests(unittest.TestCase):
    def test_settlement_releases_before_reply_and_readmits_after_saturation(self):
        result = subprocess.run([shutil.which("sbcl"), "--script", "tests/native_post_credit_source.lisp"],
                                cwd=ROOT, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("outcome=saturated slots=1 held=1 budget=100 total=100 free=0", result.stdout)
        self.assertIn("outcome=complete slots=1 held=0 budget=100 total=0 free=100 open=0 sealed=0", result.stdout)
        self.assertIn("PASS actual POST credit settlement and readmission", result.stdout)
        self.assertNotIn("must-not-print", result.stdout)
