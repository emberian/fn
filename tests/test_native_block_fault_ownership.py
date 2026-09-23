"""Identity checks for the opt-in private device-EIO campaign."""
from dataclasses import replace
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import unittest
from unittest import mock

from tests.campaign import native_block_fault as fault


class NativeBlockFaultOwnershipTests(unittest.TestCase):
    def setUp(self):
        self.core = "/scratch/fn-host-developer.core"
        self.tracee = fault.ProcIdentity(
            pid=202, group=101, session=101, start_time=9001, state="T",
            argv=(b"/usr/bin/sbcl", b"--core", self.core.encode()))

    def test_dm_dependency_requires_one_exact_owned_loop(self):
        self.assertTrue(fault.exact_dm_loop_dependency(
            "1 dependencies\t: (loop12)\n", "/dev/loop12"))
        for bad in ("1 dependencies : (loop120)", "1 dependencies : (loop1)",
                    "2 dependencies : (loop12) (loop13)",
                    "1 dependencies : (loop12) extra"):
            with self.subTest(bad=bad):
                self.assertFalse(fault.exact_dm_loop_dependency(bad, "/dev/loop12"))

    def test_same_core_from_other_session_is_not_owned(self):
        self.assertTrue(fault.owned_tracee(self.tracee, 101, self.core))
        self.assertFalse(fault.owned_tracee(replace(self.tracee, group=303), 101,
                                            self.core))
        self.assertFalse(fault.owned_tracee(replace(self.tracee, session=303), 101,
                                            self.core))
        self.assertFalse(fault.owned_tracee(replace(self.tracee, state="S"), 101,
                                            self.core))
        self.assertFalse(fault.owned_tracee(replace(
            self.tracee, argv=(b"sbcl", b"--core", b"/other.core",
                                self.core.encode())), 101, self.core))

    def test_signal_rechecks_start_time_and_session_before_pidfd_signal(self):
        for changed in (replace(self.tracee, start_time=9002),
                        replace(self.tracee, group=303),
                        replace(self.tracee, session=303),
                        replace(self.tracee, argv=(b"sbcl", b"--core", b"/other.core"))):
            with self.subTest(changed=changed):
                with (mock.patch.object(fault.os, "pidfd_open", return_value=77,
                                        create=True),
                      mock.patch.object(fault.os, "close") as close,
                      mock.patch.object(fault.signal, "pidfd_send_signal",
                                        create=True) as send,
                      mock.patch.object(fault, "read_proc_identity",
                                        return_value=changed)):
                    with self.assertRaisesRegex(RuntimeError, "identity changed"):
                        fault.signal_owned_process(self.tracee, signal.SIGKILL,
                                                   session_id=101, core=self.core)
                    send.assert_not_called()
                    close.assert_called_once_with(77)

        with (mock.patch.object(fault.os, "pidfd_open", return_value=78,
                                create=True) as open_fd,
              mock.patch.object(fault.signal, "pidfd_send_signal", create=True) as send):
            with self.assertRaisesRegex(RuntimeError, "outside the campaign"):
                fault.signal_owned_process(replace(self.tracee, session=404),
                                           signal.SIGKILL, session_id=101,
                                           core=self.core)
            open_fd.assert_not_called()
            send.assert_not_called()

    def test_owned_pidfd_signal_uses_rechecked_exact_identity(self):
        with (mock.patch.object(fault.os, "pidfd_open", return_value=79, create=True),
              mock.patch.object(fault.os, "close") as close,
              mock.patch.object(fault.signal, "pidfd_send_signal", create=True) as send,
              mock.patch.object(fault, "read_proc_identity", return_value=self.tracee)):
            self.assertTrue(fault.signal_owned_process(
                self.tracee, signal.SIGCONT, session_id=101, core=self.core))
            send.assert_called_once_with(79, signal.SIGCONT)
            close.assert_called_once_with(79)

    @unittest.skipUnless(Path("/proc").is_dir(), "Linux process inventory required")
    def test_live_same_core_in_another_session_is_excluded(self):
        command = [sys.executable, "-c", "import time; time.sleep(30)",
                   "--core", self.core]
        first = subprocess.Popen(command, start_new_session=True)
        second = subprocess.Popen(command, start_new_session=True)
        try:
            os.kill(first.pid, signal.SIGSTOP)
            os.kill(second.pid, signal.SIGSTOP)
            deadline = time.monotonic() + 3
            while time.monotonic() < deadline:
                matches = fault.stopped_core_processes(self.core, first.pid)
                if len(matches) == 1 and matches[0].pid == first.pid:
                    break
                time.sleep(.02)
            else:
                self.fail("owned stopped process was not selected exactly")
            self.assertEqual(first.pid, matches[0].group)
            self.assertEqual(first.pid, matches[0].session)
            self.assertNotEqual(first.pid, second.pid)
        finally:
            for child in (first, second):
                os.kill(child.pid, signal.SIGCONT)
                child.terminate()
                child.wait(timeout=5)


if __name__ == "__main__":
    unittest.main()
