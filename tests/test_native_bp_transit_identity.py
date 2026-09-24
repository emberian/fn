"""Identity octets must survive the actual native BP transit boundary."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class NativeBpTransitIdentityTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "no sbcl on PATH")
    def test_identity_match_and_both_mismatches(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script",
             "tests/native_bp_transit_identity_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, timeout=30, check=False)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("native BP transit identity regression passed", result.stdout)
