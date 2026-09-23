"""Run the shipped BP dispatcher against a controlled owner clock."""
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpAppClockTests(unittest.TestCase):
    def test_submit_observes_fresh_clock_and_replay_needs_none(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script", "tests/native_bp_app_clock_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=60, check=False)
        self.assertEqual(result.returncode, 0,
                         result.stdout.decode("utf-8", "replace"))
        self.assertIn("native BP application clock dispatch passed",
                      result.stdout.decode("utf-8", "replace"))
