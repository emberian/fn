"""Actual worker and kernel I/O with recorded session/journal leaves."""
from pathlib import Path
import shutil
import subprocess
import unittest
ROOT = Path(__file__).resolve().parents[1]
class PeerRoundDriverTests(unittest.TestCase):
    def schedule(self, mode, message=None):
        args = [shutil.which("sbcl") or "sbcl", "--noinform", "--script",
                "tests/native_peer_round_driver_raw.lisp", mode]
        result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=5)
        if message and "ROUND_DRIVER_ASSERTION:" + message in result.stdout:
            self.fail(message)
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, args, result.stdout, result.stderr)
        self.assertIn("PEER_ROUND_DRIVER_PASS", result.stdout)

    def test_trickling_pull_cannot_starve_healthy_pull_and_catchup(self):
        self.schedule("trickle", "healthy pull and catch-up must progress while slow pull retains partial state")

    def test_local_cold_commit_render_and_suffix_are_retained(self):
        self.schedule("local")

    def test_round_core_fault_survives_cleanup_failure(self):
        self.schedule("fault")

    def test_single_attempt_kernel_connect_read_and_write_preserve_custody(self):
        self.schedule("io")

    def test_failed_local_release_attempts_all_custody_cleanup(self):
        self.schedule("cleanup")
