"""Exact non-Linux publication-lock branch distinguishes faults and contention."""
import shutil
import subprocess
import unittest


class PublicationLockTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_nonlinux_publication_lock_custody(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_publication_lock_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("publication lock custody passed (10 paths)", result.stdout)
