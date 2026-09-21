"""Containment tests for the development command runner.

The fixture deliberately has a shell leader and a Python grandchild.  Tests
are externally bounded when run by hand; their own runner must nevertheless
remove both processes before reporting timeout or cancellation.
"""
from __future__ import annotations

import os
from pathlib import Path
import signal
import shlex
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent
RUNNER = ROOT / "tools" / "run_command.py"


CHILD = r"""
import os
from pathlib import Path
import sys
import time

pid_file = Path(sys.argv[1])
pid_file.write_text(str(os.getpid()))
while True:
    time.sleep(1)
"""


def gone(pid: int) -> bool:
    """Treat a zombie as gone: it has exited and cannot retain resources."""
    try:
        state = Path("/proc/{}/stat".format(pid)).read_text().split()[2]
        return state == "Z"
    except FileNotFoundError:
        return True


class ProcessSupervisorTests(unittest.TestCase):
    def start_tree(self, directory: Path, timeout: str = "30"):
        child_pid = directory / "grandchild.pid"
        shell_pid = directory / "shell.pid"
        shell = "echo $$ > {}; python3 -c {} {} & wait".format(
            shell_pid, shlex.quote(CHILD), child_pid)
        command = [sys.executable, str(RUNNER), "--timeout", timeout,
                   "--grace", "0.2", "--", "/bin/sh", "-c", shell]
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        try:
            self.wait_for(child_pid)
        except Exception:
            process.kill()
            process.wait(timeout=3)
            raise
        return process, shell_pid, child_pid

    def wait_for(self, pid_file: Path):
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            if pid_file.exists():
                return
            time.sleep(0.02)
        self.fail("fixture did not start")

    def assert_tree_gone(self, shell_pid: Path, child_pid: Path):
        for pid_file in (shell_pid, child_pid):
            pid = int(pid_file.read_text())
            deadline = time.monotonic() + 3
            while time.monotonic() < deadline and not gone(pid):
                time.sleep(0.02)
            self.assertTrue(gone(pid), "survived runner cleanup: {}".format(pid))

    def test_timeout_reaps_shell_and_grandchild(self):
        with tempfile.TemporaryDirectory() as directory:
            process, shell_pid, child_pid = self.start_tree(Path(directory), "0.2")
            stdout, stderr = process.communicate(timeout=8)
            self.assertEqual(process.returncode, 124, (stdout, stderr))
            self.assertIn(b"task process group reaped", stderr)
            self.assert_tree_gone(shell_pid, child_pid)

    def cancel_tree(self, signum: int, expected_returncode: int):
        with tempfile.TemporaryDirectory() as directory:
            process, shell_pid, child_pid = self.start_tree(Path(directory))
            os.kill(process.pid, signum)
            stdout, stderr = process.communicate(timeout=8)
            self.assertEqual(process.returncode, expected_returncode, (stdout, stderr))
            self.assertIn("cancelled by {}".format(signum).encode(), stderr)
            self.assert_tree_gone(shell_pid, child_pid)

    def test_term_cancels_shell_and_grandchild(self):
        self.cancel_tree(signal.SIGTERM, 143)

    def test_int_cancels_shell_and_grandchild(self):
        self.cancel_tree(signal.SIGINT, 130)


if __name__ == "__main__":
    unittest.main()
