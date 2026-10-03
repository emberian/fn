"""Actual worker/tick custody over ACL2 plans; real fd close, no image claim."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class PullJournalRegistryTests(unittest.TestCase):
    def schedule(self, mode, intended=None):
        for kind in ("pull", "catch-up"):
            with tempfile.TemporaryDirectory() as directory:
                args = [shutil.which("sbcl") or "sbcl", "--noinform", "--script",
                        "tests/native_pull_journal_registry_raw.lisp",
                        str(Path(directory) / "journal"), mode, kind]
                result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=5)
                if intended and "JOURNAL_REGISTRY_ASSERTION:" + intended in result.stdout:
                    self.fail(intended)
                if result.returncode:
                    raise subprocess.CalledProcessError(result.returncode, args, result.stdout, result.stderr)
                self.assertIn("PULL_JOURNAL_REGISTRY_PASS", result.stdout)

    def test_removed_peer_releases_kernel_descriptor_and_cursor(self):
        self.schedule("remove", "removed peer must release journal descriptor custody")

    def test_returning_peer_reopens_through_replay_leaf(self):
        self.schedule("reappear")

    def test_close_fault_attempts_all_retired_descriptors(self):
        self.schedule("close-fault")

    def test_acl2_schedule_retires_removed_peers_and_preserves_live_state(self):
        self.schedule("schedule", "removed peer must no longer remain due in ACL2 schedule")
