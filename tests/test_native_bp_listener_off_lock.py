"""The BP listener drive runs after the owner mutex; its failure is fenced by a settle quantum."""
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpListenerOffLockTests(unittest.TestCase):
    def test_drive_runs_after_release_and_failure_is_fenced_under_the_mutex(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_bp_listener_off_lock_raw-mock.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=30, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native BP listener off lock: PASS", output)

    def test_drive_stops_before_the_next_primitive_once_the_owner_is_stopping(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_bp_listener_stop_raw-mock.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=30, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native BP listener stop: PASS", output)
