"""tests/native_harness.py: a chatty child never blocks, and its tail survives.

No image: the child is a Python one-liner that writes far more than a pipe
buffer holds to BOTH streams before it announces, then sleeps.  Under the
old `stdout=PIPE, stderr=PIPE` start that read only the announcement, the
child blocks in its first stderr write past 64 KiB and never announces.
"""
import subprocess
import sys
import time
import unittest

from tests import native_harness
from tests.native_harness import STDERR_TAIL, stderr_digest, wait_for_announcement

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


# The Popen-shaped start the older modules use (was tests/test_native_process.py):
# a start that fails says why, from stderr (feed-queue's ask, 2026-09-27),
# the refusal line first whatever the breakdown's length.
REFUSAL = "fn: refused machine-cannot-hold-profile reservation=35034 MB budget=24576 MB"


def stand_in(breakdown_lines: int, announce: bool = False) -> subprocess.Popen:
    script = (
        "import sys\n"
        "sys.stderr.write({refusal!r} + '\\n')\n"
        "for i in range({n}):\n"
        "    sys.stderr.write('part %d does not fit: ' % i + 'x' * 60 + '\\n')\n"
        "sys.stdout.write({out!r})\n"
        "sys.exit(1)\n").format(refusal=REFUSAL, n=breakdown_lines,
                                out="LISTENING 127.0.0.1:1\n" if announce else "starting\n")
    return subprocess.Popen([sys.executable, "-c", script], stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)


class StartupDiagnosticTests(unittest.TestCase):
    def failure(self, breakdown_lines: int) -> str:
        process = stand_in(breakdown_lines)
        with self.assertRaises(AssertionError) as caught:
            wait_for_announcement(process, b"LISTENING ", timeout=30)
        return str(caught.exception)

    def test_short_stderr_is_quoted_whole_before_stdout(self):
        text = self.failure(3)
        self.assertIn(REFUSAL, text)
        self.assertLess(text.index(REFUSAL), text.index("stdout="))
        self.assertIn("exit=1", text)

    def test_the_refusal_survives_a_breakdown_longer_than_the_tail(self):
        text = self.failure(1000)  # ~80 KB of breakdown after the refusal
        self.assertIn("refused lines (1): " + REFUSAL, text)
        self.assertIn("stderr (last {} of".format(STDERR_TAIL), text)

    def test_control_the_tail_alone_loses_the_refusal(self):
        # What the diagnostic used to keep: the refusal is not in the tail.
        process = stand_in(1000)
        _, err = process.communicate(timeout=30)
        self.assertNotIn(REFUSAL, err[-STDERR_TAIL:].decode())
        self.assertIn(REFUSAL, stderr_digest(err))

    def test_an_announcing_node_is_answered_normally(self):
        process = stand_in(0, announce=True)
        try:
            line = wait_for_announcement(process, b"LISTENING ", timeout=30)
            self.assertEqual(line, b"LISTENING 127.0.0.1:1\n")
        finally:
            process.communicate(timeout=30)



class OutcomeTableTests(unittest.TestCase):
    """EXIT is ACL2's table, read from the book, never a hand copy."""

    def test_the_codes_are_the_books(self):
        self.assertEqual(native_harness.outcome_codes(), {
            "accepted": 0, "refused": 1, "fenced": 3, "fault": 4, "usage": 5,
            "interrupted": 6, "not-connected": 7})
        self.assertEqual(native_harness.EXIT.UNCERTAIN, 3)

    def test_a_changed_table_is_refused_at_import(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as directory:
            book = Path(directory) / "outcome-class.lisp"
            book.write_text("(defconst *fn-outcome-codes*\n  '((:accepted . 0) (:refused . 0)))\n")
            with self.assertRaises(RuntimeError):
                native_harness.outcome_codes(book)

    def test_uncertain_is_never_taken_for_refused(self):
        done = subprocess.CompletedProcess([], 3, b"", b"uncertain operator post\n")
        native_harness.assert_outcome(self, done, native_harness.EXIT.UNCERTAIN)
        with self.assertRaises(AssertionError) as caught:
            native_harness.assert_outcome(self, done, native_harness.EXIT.REFUSED)
        self.assertIn("expected REFUSED (1), got UNCERTAIN (3)", str(caught.exception))
        self.assertIn("uncertain operator post", str(caught.exception))


class ClientTests(unittest.TestCase):
    """The NNTP client against a scripted loopback server (no image)."""

    def serve(self, script):
        import socket
        import threading
        listener = socket.socket()
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        received = []

        def run():
            connection, _ = listener.accept()
            with connection:
                stream = connection.makefile("rwb")
                for expect, reply in script:
                    if expect is not None:
                        received.append(stream.readline() if expect == "line" else
                                        b"".join(iter(stream.readline, b".\r\n")))
                    stream.write(reply)
                    stream.flush()
            listener.close()
        thread = threading.Thread(target=run, daemon=True)
        thread.start()
        self.addCleanup(thread.join, 5)
        return listener.getsockname()[1], received

    def test_post_dot_stuffs_and_article_unstuffs(self):
        port, received = self.serve([
            (None, b"200 ready\r\n"),
            ("line", b"340 send\r\n"),
            ("block", b"240 ok\r\n"),
            ("line", b"220 0 <a@b>\r\n..dot\r\nplain\r\n.\r\n"),
        ])
        with native_harness.Client(port, timeout=10) as client:
            first, final = client.post(b".dot\r\nplain\r\n")
            self.assertEqual((first, final), (b"340 send\r\n", b"240 ok\r\n"))
            self.assertEqual(client.article("<a@b>"), b".dot\r\nplain\r\n")
        self.assertEqual(received[1], b"..dot\r\nplain\r\n")

    def test_article_builds_crlf_octets(self):
        text = native_harness.article("<m@x>", subject="s", date=None, body=b"b\r\n")
        self.assertEqual(text, b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                               b"Subject: s\r\nMessage-ID: <m@x>\r\n\r\nb\r\n")



class FailedTestStderrTests(unittest.TestCase):
    """obstructions-3 item 15: a failed native test prints and keeps the
    stderr of every process it started; a passing test's are dropped."""

    def run_cases(self, keep):
        import io
        import os
        import tempfile
        from unittest import mock
        from tools import test_budget

        class Cases(unittest.TestCase):
            def test_refusal(self):
                process = native_harness.start(
                    [sys.executable, "-c",
                     "import sys; sys.stderr.write('owner refused: heap figure 802 GB\\n')"])
                process.wait(timeout=30)
                process.stop()
                self.fail("the owner did not start")

            def test_filed(self):
                with tempfile.TemporaryDirectory() as scratch:
                    log = os.path.join(scratch, "owner.stderr")
                    process = native_harness.start_filed(
                        [sys.executable, "-c",
                         "import sys; sys.stderr.write('filed refusal line\\n')"], log)
                    process.wait(timeout=30)
                    process.stdout.close()
                    process.stderr.close()
                # the directory, and the file, are gone here
                raise RuntimeError("after the temp dir went")

            def test_passes(self):
                native_harness.start([sys.executable, "-c", "pass"]).stop()

            def test_two_processes(self):
                # obstructions-5 item 43: the receiver's stdout line diagnosed
                # the sender's defect; the report keeps every process's.
                receiver = native_harness.start(
                    [sys.executable, "-c", "print('(:BUNDLE-RECEIVED 7)')"])
                receiver.wait(timeout=30)
                receiver.stop()
                native_harness.run([sys.executable, "-c",
                                    "import sys; print('sender out'); "
                                    "sys.stderr.write('sender err\\n'); sys.exit(6)"])
                self.fail("send exit 6")

        stream = io.StringIO()
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(Cases)
        with mock.patch.dict(os.environ, {"FN_NATIVE_STDERR_DIR": keep}):
            unittest.TextTestRunner(stream=stream, resultclass=test_budget._TimedResult,
                                    verbosity=0).run(suite)
        return stream.getvalue()

    def test_the_failed_tests_stderr_is_printed_and_kept(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as keep:
            out = self.run_cases(keep)
            self.assertIn("owner refused: heap figure 802 GB", out)
            self.assertIn("filed refusal line", out)
            self.assertNotIn("test_passes process", out)
            kept = sorted(path.name for path in Path(keep).iterdir())
            self.assertEqual(len([n for n in kept if n.endswith(".stderr")]), 4, kept)
            self.assertIn("(:BUNDLE-RECEIVED 7)", out)
            self.assertIn("sender out", out)
            self.assertIn("sender err", out)
            self.assertIn("exit=6", out)
            self.assertTrue(any(n.startswith("Cases.test_two_processes-1-") and
                                n.endswith(".stdout") for n in kept), kept)
            self.assertTrue(any(name.startswith("Cases.test_refusal-1-") for name in kept), kept)
            text = b"".join(path.read_bytes() for path in Path(keep).iterdir())
            self.assertIn(b"filed refusal line", text)
        self.assertEqual(native_harness._STARTED, {})


if __name__ == "__main__":
    unittest.main()
