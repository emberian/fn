"""Actual BP item readers preserve complete results with prefix-only probes."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class BpPrefixProbeSourceTests(unittest.TestCase):
    def test_complete_results_and_matched_suffix_cost(self):
        result = subprocess.run(
            [shutil.which("sbcl"), "--script", str(ROOT / "tests/native_bp_prefix_probe_source.lisp")],
            cwd=ROOT, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS actual BP prefix probes", result.stdout)

if __name__ == "__main__":
    unittest.main()
