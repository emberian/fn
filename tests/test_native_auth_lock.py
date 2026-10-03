"""Only real flock contention refuses; failed auth acquisition releases custody."""
import shutil
import subprocess
import unittest


class AuthLockTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_physical_error_classification_and_custody(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_auth_lock_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("AUTHINFO physical lock classification and custody passed (13 paths)", result.stdout)
