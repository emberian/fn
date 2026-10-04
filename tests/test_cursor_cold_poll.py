"""Run actual native cursor/mux bodies against discriminating I/O doubles.

No ACL2 semantics, cache progress guarantee or qualified-image custody claim is
made here. The shared loop must suspend a cold response without awaiting its
page, retain its plan/action and resume that plan rather than the input step.
"""
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SBCL = shutil.which("sbcl")


@unittest.skipUnless(SBCL, "SBCL required for native host control-flow replay")
class CursorColdPollTests(unittest.TestCase):
    def test_actual_native_bodies_suspend_poll_resume_and_refuse(self):
        result = subprocess.run(
            [SBCL, "--noinform", "--dynamic-space-size", "256", "--script",
             "tests/cursor_cold_poll_recording-mock.lisp"],
            cwd=ROOT, capture_output=True, text=True, timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("warm/suspend/wait/retry/resume/refuse/line PASS", result.stdout)
