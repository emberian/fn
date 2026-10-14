"""Actual developer heap projection and shared ACL2 growth classification."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
class DeveloperStoreHeapSourceTests(unittest.TestCase):
    def test_status_replay_and_offline_actions_keep_the_shared_decision(self):
        result = subprocess.run([shutil.which("sbcl"), "--script",
                                 "tests/native_developer_store_heap_source.lisp"],
                                cwd=ROOT, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS actual developer store heap projection", result.stdout)
