"""Failure cleanup must reap its own launcher before draining output."""
import importlib.util
from pathlib import Path
import signal
import subprocess
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location("restart", Path(__file__).with_name("native-image-restart.py"))
restart = importlib.util.module_from_spec(spec)
spec.loader.exec_module(restart)


class Cleanup(unittest.TestCase):
    def node(self, directory, node_pid=None, timeout_first=False):
        node = restart.Node.__new__(restart.Node)
        node.node_pid = node_pid
        node.launcher_pidfile = Path(directory) / "launcher.pid"
        node.launcher_pidfile.write_text("12345\n")
        node.log = mock.Mock()
        node.selector = mock.Mock()
        proc = mock.Mock(pid=12345)
        proc.poll.return_value = None
        proc.stdout.fileno.return_value = 99
        waits = []
        def wait(timeout):
            waits.append(timeout)
            if timeout_first and len(waits) == 1:
                raise subprocess.TimeoutExpired("own launcher", timeout)
            proc.poll.return_value = -9
            return -9
        proc.wait.side_effect = wait
        def read():
            self.assertIsNotNone(proc.poll())
            return b"startup failure\n"
        proc.stdout.read.side_effect = read
        node.proc = proc
        return node

    @mock.patch.object(restart.os, "set_blocking")
    @mock.patch.object(restart.os, "killpg")
    @mock.patch.object(restart.os, "kill")
    def test_missing_runtime_pid_stops_recorded_launcher_before_read(self, kill, killpg, nonblocking):
        with tempfile.TemporaryDirectory() as directory:
            node = self.node(directory)
            node.close()
            kill.assert_not_called()
            killpg.assert_called_once_with(12345, signal.SIGKILL)
            nonblocking.assert_called_once_with(99, False)
            node.log.write.assert_called_once_with(b"startup failure\n")
            node.proc.wait.assert_called_once_with(timeout=10)

    @mock.patch.object(restart.os, "set_blocking")
    @mock.patch.object(restart.os, "killpg")
    @mock.patch.object(restart.os, "kill")
    def test_runtime_cleanup_falls_back_if_launcher_does_not_exit(self, kill, killpg, nonblocking):
        with tempfile.TemporaryDirectory() as directory:
            node = self.node(directory, node_pid=12346, timeout_first=True)
            node.close()
            kill.assert_called_once_with(12346, signal.SIGKILL)
            killpg.assert_called_once_with(12345, signal.SIGKILL)
            self.assertEqual(node.proc.wait.call_count, 2)

    @mock.patch.object(restart.os, "killpg")
    def test_wrong_recorded_launcher_is_not_signalled(self, killpg):
        with tempfile.TemporaryDirectory() as directory:
            node = self.node(directory)
            node.launcher_pidfile.write_text("999\n")
            with self.assertRaises(AssertionError):
                node.close()
            killpg.assert_not_called()


if __name__ == "__main__":
    unittest.main()
