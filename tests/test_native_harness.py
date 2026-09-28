"""tests/native_harness.py: a chatty child never blocks, and its tail survives.

No image: the child is a Python one-liner that writes far more than a pipe
buffer holds to BOTH streams before it announces, then sleeps.  Under the
old `stdout=PIPE, stderr=PIPE` start that read only the announcement, the
child blocks in its first stderr write past 64 KiB and never announces.
"""
import sys
import time
import unittest

from tests import native_harness

CHATTY = r"""
import sys, time
for i in range(40000):
    sys.stdout.write("out %06d %s\n" % (i, "x" * 60))
    sys.stderr.write("err %06d %s\n" % (i, "y" * 60))
sys.stdout.write("READY 1234\n")
sys.stdout.flush()
sys.stderr.write("last stderr line\n")
sys.stderr.flush()
time.sleep(600)
"""

REFUSES = r"""
import sys
sys.stderr.write("owner refused: connections-exceed-memory\n")
sys.exit(4)
"""


class DrainingStartTests(unittest.TestCase):
    def test_chatty_child_announces_and_keeps_its_tail(self):
        started = time.monotonic()
        node = native_harness.start([sys.executable, "-c", CHATTY],
                                    limit=256 * 1024)
        self.addCleanup(node.stop, 5)
        line = node.announcement(b"READY ", timeout=60)
        self.assertEqual(line, b"READY 1234\n")
        # ~2.8 MB per stream went through a 256 KiB buffer: trimmed, not blocked.
        deadline = time.monotonic() + 30
        while b"last stderr line" not in node.stderr.tail() and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertIn(b"last stderr line", node.stderr.tail())
        self.assertIn(b"err 039999", node.stderr.tail())
        self.assertGreater(node.stderr.dropped, 2_000_000)
        self.assertIsNone(node.poll(), "the child must still be alive, not blocked or dead")
        status = node.stop(grace=5)
        self.assertEqual(status, -15)  # SIGTERM by PID, reaped
        self.assertTrue(node.stdout.pipe.closed and node.stderr.pipe.closed)
        self.assertEqual(node.stop(), -15)  # idempotent
        self.assertLess(time.monotonic() - started, 60)

    def test_refusal_on_stderr_is_in_the_failure(self):
        node = native_harness.start([sys.executable, "-c", REFUSES])
        with self.assertRaises(AssertionError) as caught:
            node.announcement(b"LISTENING ", timeout=30)
        message = str(caught.exception)
        self.assertIn("connections-exceed-memory", message)
        self.assertIn("exit=4", message)
        self.assertTrue(node.stopped)

    def test_output_until_advances_a_cursor(self):
        node = native_harness.start([sys.executable, "-c",
                                     "import time\nprint('a 1', flush=True)\n"
                                     "print('b 2', flush=True)\ntime.sleep(600)"])
        self.addCleanup(node.stop, 5)
        self.assertEqual(node.output_until(b"a 1", timeout=30), b"a 1\n")
        self.assertEqual(node.output_until(b"b 2", timeout=30), b"b 2\n")
        with self.assertRaises(AssertionError):
            node.output_until(b"a 1", timeout=1)  # already consumed; node stopped

    def test_communicate_returns_what_the_cursor_has_not_passed(self):
        node = native_harness.start([sys.executable, "-c",
                                     "import sys\nprint('HELLO', flush=True)\n"
                                     "print('rest')\nsys.stderr.write('why\\n')"])
        self.assertEqual(node.announcement(b"HELLO", timeout=30), b"HELLO\n")
        out, err = node.communicate(timeout=30)
        self.assertEqual((out, err, node.returncode), (b"rest\n", b"why\n", 0))


if __name__ == "__main__":
    unittest.main()
