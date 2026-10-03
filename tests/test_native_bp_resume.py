"""Budget-file failure cannot strand the already acquired BP service."""
import shutil
import subprocess
import unittest


class BpResumeTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_budget_failure_releases_service_preserving_primary(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_bp_resume_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("BP resume budget acquisition cleanup passed (3 paths)", result.stdout)
