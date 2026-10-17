"""Run the consumer raw-mock harnesses and assert their boundary lines.

SCEN-CONSUMER-BOOTSTRAP-IDENTITY: tests/native_consumer_poll_cli_raw-mock.lisp
is the guard that a `consumer bootstrap' command is one request and that a
register crosses only an accepted bootstrap (native run2-d5b0b9100, fixed by
0f480d107).  The zmq-2 extraction moved that retry into
fnn-consumer-local-exchange (host/native/consumer-local.lisp); when the mock
does not extract it the derived stub faults and the guard silently stops
exercising the retry.  This unittest keeps the mock runnable from the Python
suite wherever SBCL exists.
"""
import os
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

POLL_CLI_BOUNDARIES = (
    "native consumer poll CLI boundary passed",
    "native consumer bootstrap outcome boundary passed",
    "native consumer bootstrap command boundary passed",
)


def run_mock(script):
    return subprocess.run(
        [shutil.which("sbcl"), "--noinform", "--disable-debugger",
         "--script", f"tests/{script}"],
        cwd=ROOT, text=True, capture_output=True, timeout=120)


class ConsumerRawMockTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_poll_cli_mock_exercises_the_bootstrap_retry(self):
        run = run_mock("native_consumer_poll_cli_raw-mock.lisp")
        passed = [line.strip() for line in run.stdout.splitlines()
                  if line.strip().endswith("boundary passed")]
        ok = run.returncode == 0 and all(b in passed for b in POLL_CLI_BOUNDARIES)
        self.assertTrue(
            ok,
            "consumer poll CLI raw mock no longer exercises the bootstrap "
            "retry: fnn-command-consumer-local reaches "
            "fnn-consumer-local-exchange, which the mock neither stubs nor "
            "extracts")

    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_owner_consumer_local_mock_boundaries(self):
        run = run_mock("native_owner_consumer_local_raw-mock.lisp")
        ok = (run.returncode == 0
              and "native owner consumer local boundary passed" in run.stdout)
        self.assertTrue(ok, "owner consumer local raw mock failed")
