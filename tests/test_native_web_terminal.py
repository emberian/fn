"""Actual Web startup and terminal consumers retain physical return receipts."""
import shutil
import subprocess
import unittest


class WebTerminalTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_actual_web_startup_and_terminal_custody(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_web_terminal_raw-mock.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("custody passed (9 paths)", result.stdout)
