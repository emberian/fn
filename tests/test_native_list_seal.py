"""Admitted list payloads use the existing releasable arena stage adapter."""
import shutil
import subprocess
import unittest


class ListSealTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_list_seal_captures_handle_and_uses_buffer_stage(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_list_seal_raw.lisp"],
            text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("list seal uses releasable stage and ACL2-derived handle", result.stdout)
