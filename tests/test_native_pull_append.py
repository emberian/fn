"""Actual FNPL/FNCU append and ACL2 phase classification; no image claim."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class PullAppendBoundaryTests(unittest.TestCase):
    def schedule(self, mode, intended=None):
        for kind in ("pull", "catch-up"):
            with tempfile.TemporaryDirectory() as directory:
                args = [shutil.which("sbcl") or "sbcl", "--noinform", "--script",
                        "tests/native_pull_append_raw.lisp", str(Path(directory) / "journal"), mode, kind]
                result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=5)
                if intended and "APPEND_ASSERTION:" + intended in result.stdout:
                    self.fail(intended)
                if result.returncode:
                    raise subprocess.CalledProcessError(result.returncode, args, result.stdout, result.stderr)
                self.assertIn("PULL_APPEND_BOUNDARY_PASS", result.stdout)

    def test_prewrite_envelope_fault_retains_class(self):
        self.schedule("envelope", "pre-write envelope fault must retain its class")

    def test_prewrite_core_and_selector_faults_attempt_no_publication(self):
        self.schedule("core")
        self.schedule("selector")

    def test_write_and_fsync_failures_retain_uncertainty(self):
        self.schedule("write")
        self.schedule("fsync")

    def test_cleanup_error_cannot_erase_uncertain_publication(self):
        self.schedule("close", "attempted publication must remain uncertain after cleanup")

    def test_postbarrier_classification_fault_is_definite(self):
        self.schedule("durable-phase")

    def test_successful_append_returns_ready_after_kernel_barrier(self):
        self.schedule("good")
