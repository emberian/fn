"""Actual BP constructor custody composes with retained physical release debt."""
import shutil
import subprocess
import unittest


class BpOpenCustodyTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_constructor_and_command_cleanup(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_bp_open_custody_raw-mock.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("constructor custody passed (12 paths)", result.stdout)
        self.assertIn("command cleanup passed (6 paths)", result.stdout)
