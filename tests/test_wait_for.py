"""tools/wait_for.sh: the one background-safe wait (friction review section 8).

Local conditions only; the --host path is the same snippet run over ssh.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
WAIT = ROOT / "tools" / "wait_for.sh"


def wait_for(*words, timeout=30):
    return subprocess.run(["sh", str(WAIT), "--interval", "1", *words],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, timeout=timeout)


class WaitForTests(unittest.TestCase):
    def test_log_marker_that_appears_later_is_printed_and_met(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "run.log"
            writer = subprocess.Popen(
                ["sh", "-c", f"sleep 2; echo 'build done: FN_READY 7' > '{log}'"])
            try:
                done = wait_for("--deadline", "20", "--log", str(log), "FN_READY [0-9]+")
            finally:
                writer.wait()
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout.strip(), "build done: FN_READY 7")

    def test_deadline_is_124_not_success(self):
        with tempfile.TemporaryDirectory() as directory:
            done = wait_for("--deadline", "1", "--file", str(Path(directory) / "never"))
        self.assertEqual(done.returncode, 124)
        self.assertIn("deadline 1s passed", done.stderr)

    def test_pid_waits_for_exit_without_matching_patterns(self):
        child = subprocess.Popen(["sleep", "2"])
        started = time.monotonic()
        done = wait_for("--deadline", "20", "--pid", str(child.pid))
        child.wait()
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertGreaterEqual(time.monotonic() - started, 1)
        self.assertIn(f"pid {child.pid} exited", done.stdout)

    def test_farm_status_returns_the_runs_own_code(self):
        with tempfile.TemporaryDirectory() as directory:
            status = Path(directory) / "build/farm/run-a.status"
            status.parent.mkdir(parents=True)
            status.write_text("3\n")
            done = wait_for("--deadline", "5", "--farm", "run-a", directory)
        self.assertEqual(done.returncode, 3)
        self.assertIn("finished with exit code 3", done.stderr)

    def test_a_quote_in_a_path_is_one_word(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "it's here"
            path.write_text("x")
            done = wait_for("--deadline", "5", "--file", str(path))
        self.assertEqual(done.returncode, 0, done.stderr)

    def test_usage_errors_are_2(self):
        self.assertEqual(wait_for("--pid", "abc").returncode, 2)
        self.assertEqual(wait_for("--deadline", "x", "--file", "/").returncode, 2)
        self.assertEqual(wait_for().returncode, 2)


if __name__ == "__main__":
    unittest.main()
