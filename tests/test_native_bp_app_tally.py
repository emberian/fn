"""S052: the BP application receiver's tally keeps a deferral apart from a refusal."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class BpAppTallyTests(unittest.TestCase):
    def test_a_deferred_transfer_is_not_counted_refused(self):
        result = subprocess.run(
            [shutil.which("sbcl"), "--script", str(ROOT / "tests/native_bp_app_tally-mock.lisp")],
            cwd=ROOT, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS the BP application tally keeps a deferral apart from a refusal",
                      result.stdout)


if __name__ == "__main__":
    unittest.main()
