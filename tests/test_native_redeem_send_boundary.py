"""Actual redeem adapter's possible-publication transition around physical send."""
import shutil
import subprocess
import unittest


class RedeemSendBoundaryTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_partial_or_complete_password_send_is_uncertain(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_redeem_send_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("native redeem send uncertainty boundary passed", result.stdout)
