"""Actual offline administrative consumers preserve primary cleanup failures."""
import shutil
import subprocess
import unittest


class AdministrativeCleanupTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_administrative_entry_cleanup(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_admin_cleanup_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Administrative cleanup passed (11 paths)", result.stdout)
