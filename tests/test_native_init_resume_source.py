"""SCN-1100 actual host init bodies; exact config codec has ACL2 teeth."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
SBCL = os.environ.get("FN_SBCL") or shutil.which("sbcl")


@unittest.skipUnless(SBCL, "SBCL is required for the actual-source init fixture")
class InitResumeSourceTests(unittest.TestCase):
    def test_existing_intent_is_checked_before_resumed_effects(self):
        result = subprocess.run(
            [SBCL, "--script", str(ROOT / "tests/native_init_resume_source.lisp")],
            cwd=ROOT, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("profile-mismatch code=1 effects=NIL", result.stdout)
        self.assertIn("groups-mismatch code=1 effects=NIL", result.stdout)
        self.assertIn("SOURCE INIT RESUME PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
