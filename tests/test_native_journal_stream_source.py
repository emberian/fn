"""Actual source lifecycle/stream-window fixture; full model tests are ACL2."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
SBCL = os.environ.get("FN_SBCL") or shutil.which("sbcl")


@unittest.skipUnless(SBCL, "SBCL is required for the actual source fixture")
class JournalStreamSourceTests(unittest.TestCase):
    def test_window_captured_prefix_and_unwind_cleanup(self):
        answer = subprocess.run(
            [SBCL, "--script", str(ROOT / "tests/native_journal_stream_source.lisp")],
            cwd=ROOT, text=True, capture_output=True, timeout=15)
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        self.assertIn("large-journal code=0 closed=1 windows=35 max=65536", answer.stdout)
        self.assertIn("nonregular-replacement code=4 closed=1 windows=0", answer.stdout)
        self.assertIn("read-error-close code=4 closed=1", answer.stdout)
        self.assertIn("SOURCE JOURNAL STREAM PASSED", answer.stdout)


if __name__ == "__main__":
    unittest.main()
