"""SCN1137 actual BP argv producer and launcher profile consumer."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class BpHeapSourceTests(unittest.TestCase):
    def test_actual_bp_projection_drives_heap_profile(self):
        result = subprocess.run(
            [shutil.which("sbcl"), "--script", str(ROOT / "tests/native_bp_heap_source.lisp")],
            cwd=ROOT, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS actual BP heap source root and connection propagation", result.stdout)

if __name__ == "__main__":
    unittest.main()
