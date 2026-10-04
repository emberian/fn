"""Actual BP send observation boundary; recorded transport, no image claim."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class BpSendBoundaryTests(unittest.TestCase):
    def schedule(self, mode, intended=None):
        args = [shutil.which("sbcl") or "sbcl", "--noinform", "--script",
                "tests/native_bp_send_boundary_raw-mock.lisp", mode]
        result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=5)
        if intended and "BP_SEND_ASSERTION:" + intended in result.stdout:
            self.fail(intended)
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, args, result.stdout, result.stderr)
        self.assertIn("BP_SEND_BOUNDARY_PASS", result.stdout)

    def test_indeterminate_keeps_exact_class(self):
        self.schedule("indeterminate", "ambiguous Store publication must retain its exact class")

    def test_later_fragment_named_refusal_retains_uncertain_prefix(self):
        self.schedule("later-refusal", "accepted fragment prefix cannot become definitely failed")

    def test_later_fragment_connect_failure_uses_acl2_normalization(self):
        self.schedule("later-connect")

    def test_indeterminate_survives_first_and_later_cleanup_failure(self):
        self.schedule("indeterminate-cleanup")
        self.schedule("later-indeterminate-cleanup")

    def test_unknown_subclass_and_core_fault_publish_no_transport_result(self):
        self.schedule("unknown")
        self.schedule("fault")

    def test_first_connect_failure_remains_definitely_failed(self):
        self.schedule("first-connect")

    def test_whole_and_all_fragments_accepted(self):
        self.schedule("whole")
        self.schedule("good")

    def test_later_indeterminate_publishes_no_transport_result(self):
        self.schedule("later-indeterminate")
