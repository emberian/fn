"""Actual receipt acquisition closes local custody on failed initialization."""
import shutil
import subprocess
import unittest


class BpAppAcquisitionTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_initialization_and_configuration_escapes_close_acquisition(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_bpapp_acquisition_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("BP application acquisition custody passed (8 paths)", result.stdout)
