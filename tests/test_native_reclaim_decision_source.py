"""Actual reclaim driver allocation and mutation ordering; no image claim."""
import shutil
import subprocess
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class ReclaimDecisionSourceTests(unittest.TestCase):
    def test_rewrite_only_after_reclaim_decision(self):
        result = subprocess.run([shutil.which("sbcl"), "--script", "tests/native_reclaim_decision_source-mock.lisp"], cwd=ROOT, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("RECLAIM DECISION SOURCE PASSED", result.stdout)
