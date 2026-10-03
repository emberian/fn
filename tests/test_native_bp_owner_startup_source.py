"""SCN1134 actual BP listener startup calls and physical custody gates."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class BpOwnerStartupSourceTests(unittest.TestCase):
    def test_actual_listener_preopen_and_teardown_custody(self):
        result = subprocess.run(
            [shutil.which("sbcl"), "--script", str(ROOT / "tests/native_bp_owner_startup_source.lisp")],
            cwd=ROOT, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS actual BP served owner pre-open and teardown custody", result.stdout)

if __name__ == "__main__":
    unittest.main()
