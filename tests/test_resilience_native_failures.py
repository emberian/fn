"""Actual host execution failures and cleanup orchestration; no native fn verdict."""
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from tools.resilience.adapters.native_cuts import HarnessFailure, Nntp, Run, _served_outcome
from tools.resilience.adapters import native_cuts
from tools.resilience.journal import Journal
from tools.resilience.payload_boundary import scenario


class NativeWireBoundaryTests(unittest.TestCase):
    def test_selected_cut_constructs_only_its_checked_scenario(self):
        cuts = [SimpleNamespace(name="a"), SimpleNamespace(name="b")]
        build = Mock(side_effect=lambda cut: "checked-" + cut.name)
        with patch.dict(native_cuts.FAMILY_CUTS, {"served": (lambda: cuts, build)}):
            self.assertEqual(native_cuts.family_scenarios("served", "b"), ["checked-b"])
            build.assert_called_once_with(cuts[1])
            build.reset_mock()
            self.assertEqual(native_cuts.family_scenarios("served", "unavailable"), [])
            build.assert_not_called()

    def test_missing_cut_is_reported_before_a_workload_can_claim_success(self):
        with patch.object(native_cuts.Path, "is_file", return_value=True), \
             patch.object(native_cuts.os, "access", return_value=True), \
             patch.object(native_cuts, "family_scenarios", return_value=[]):
            self.assertEqual(native_cuts.main(["--image", "unused", "--family", "served", "--cut", "unavailable"]), 2)

    def test_eof_after_partial_multiline_reply_is_not_a_complete_block(self):
        client = Nntp.__new__(Nntp)
        client.f = io.BytesIO(b"a retained row\r\n")
        with self.assertRaisesRegex(EOFError, "dot terminator"):
            client.block()

    def test_empty_and_dot_stuffed_complete_blocks_remain_complete(self):
        client = Nntp.__new__(Nntp)
        client.f = io.BytesIO(b".\r\n")
        self.assertEqual(client.block(), [])
        client.f = io.BytesIO(b"..row\r\n.\r\n")
        self.assertEqual(client.block(), [b".row\r\n"])

    def test_literal_native_uncertainty_is_not_a_441_refusal(self):
        status = b"441 outcome uncertain; recover before retry\r\n"
        self.assertEqual(_served_outcome(b"340 send article\r\n", status), ("uncertain", status))
        self.assertEqual(_served_outcome(status, None), ("uncertain", status))
        self.assertEqual(_served_outcome(b"340 send article\r\n", b"441 article refused\r\n")[0], "refused")

    def test_lost_reply_remains_a_distinct_transport_observation(self):
        self.assertEqual(_served_outcome(b"340 send article\r\n", b"")[0], "lost")


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
