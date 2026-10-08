"""Paged checkpoint I/O order and failure propagation, without an image."""
import shutil
import subprocess
import unittest


class CheckpointPagesTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_driver_io_boundaries(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_checkpoint_pages_raw-mock.lisp"],
            text=True, capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("native_checkpoint_pages_raw-mock passed", result.stdout)
