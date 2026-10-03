"""SCN-1130 actual owner-run source; complete resource/image claims separate."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class OwnerPoolStartupSourceTests(unittest.TestCase):
    def test_preopen_ordering_and_orphan_executor_cleanup(self):
        result = subprocess.run(
            [shutil.which("sbcl"), "--script", str(ROOT / "tests/native_owner_pool_startup_source.lisp")],
            cwd=ROOT, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS actual owner pool pre-open ordering and orphan cleanup", result.stdout)

if __name__ == "__main__":
    unittest.main()
