"""Actual host execution failures and cleanup orchestration; no native fn verdict."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock

from tools.resilience.adapters.native_cuts import HarnessFailure, Run
from tools.resilience.journal import Journal
from tools.resilience.payload_boundary import scenario


class NativeFailureTests(unittest.TestCase):
    def recorder(self, work):
        # Bypass candidate preparation only for failure recorder unit scope.
        run = Run.__new__(Run)
        run.s = scenario("a" * 40)
        run.work = Path(work)
        run.image = Path(work) / "does-not-exist"
        run.store = Path(work) / "store"
        run.j = Journal(run.s.id)
        run.node = None
        run.finish = Mock(side_effect=AssertionError("failure cannot finish as a product history"))
        return run

    def test_real_missing_executable_seals_harness_failure_without_client_outcome(self):
        with tempfile.TemporaryDirectory() as work:
            run = self.recorder(work)
            run.run_post = lambda: run.invoke("init")
            journal, verdict = run.run()
            self.assertEqual(verdict.kind, "harness-failure")
            self.assertIn("FileNotFoundError", verdict.cause)
            self.assertFalse(any(r["kind"] == "client" for r in journal.records))
            self.assertEqual(Journal.read(Path(work) / "journal.jsonl").digest(), journal.digest())
            self.assertEqual(json.loads((Path(work) / "verdict.json").read_text())["kind"],
                             "harness-failure")
            run.finish.assert_not_called()

    def test_real_timeout_preserves_raw_invalid_utf8_diagnostic_without_outcome(self):
        with tempfile.TemporaryDirectory() as work:
            run = self.recorder(work)
            def operation():
                subprocess.run([sys.executable, "-c",
                                "import os,time;os.write(1,b'\\xff');time.sleep(10)"],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=0.5)
            run.run_post = operation
            journal, verdict = run.run()
            self.assertEqual(verdict.kind, "harness-failure")
            self.assertIn("TimeoutExpired", verdict.cause)
            self.assertEqual(journal.records[0]["stdout_hex"], "ff")
            self.assertFalse(any(r["kind"] == "client" for r in journal.records))

    def test_cleanup_failure_retains_primary_and_handle_before_sealing(self):
        with tempfile.TemporaryDirectory() as work:
            run = self.recorder(work)
            run.run_post = Mock(side_effect=HarnessFailure("primary-observation-missing"))
            node = SimpleNamespace(reap=Mock(side_effect=OSError("join unavailable")))
            run.node = node
            journal, verdict = run.run()
            self.assertIs(run.node, node)
            self.assertIn("primary-observation-missing", verdict.cause)
            self.assertIn("native-cleanup-failed", verdict.cause)
            self.assertEqual([r["event"] for r in journal.records],
                             ["native-execution-failed", "native-cleanup-failed"])
            node.reap.assert_called_once()
            run.finish.assert_not_called()

    def test_cleanup_failure_after_workload_never_reaches_successful_finish(self):
        with tempfile.TemporaryDirectory() as work:
            run = self.recorder(work)
            run.run_post = Mock()
            run.node = SimpleNamespace(reap=Mock(side_effect=OSError("join unavailable")))
            journal, verdict = run.run()
            self.assertEqual(verdict.kind, "harness-failure")
            self.assertIn("native-cleanup-failed", verdict.cause)
            self.assertEqual(journal.records[0]["event"], "native-cleanup-failed")
            run.finish.assert_not_called()
