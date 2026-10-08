"""Source-level held-statement driver; no native image or database required."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parent.parent


class HeldStatementTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_plan_and_driver_resume_only_after_off_owner_job(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_held_statement_raw.lisp"],
            cwd=ROOT, text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("fenced resume, five failed phases", result.stdout)
