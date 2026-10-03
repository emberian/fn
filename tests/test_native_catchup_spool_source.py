"""Private spool executor physical custody, no funding or saved-image claim."""
import shutil
import subprocess
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[1]
@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class CatchupSpoolSourceTests(unittest.TestCase):
    def test_anonymous_spool_and_held_cancel(self):
        result = subprocess.run([shutil.which("sbcl"), "--script", "tests/native_catchup_spool_source.lisp"], cwd=ROOT, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("CATCHUP SPOOL SOURCE PASSED", result.stdout)
