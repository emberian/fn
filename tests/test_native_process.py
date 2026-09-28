"""A native start that fails says why, from stderr (feed-queue's ask, 2026-09-27).

tests/native_process.py `wait_for_announcement' is how 43 native modules
wait for LISTENING.  A node that refuses to start (`fn: refused
init-budget-cannot-hold-profile ...', `machine-cannot-hold-profile')
says so on stderr and then may print a long breakdown; the failure must
carry the refusal line whatever the breakdown's length, and stderr ahead of
stdout.  No image: the "node" is a stand-in that refuses the same way.
"""

from __future__ import annotations

import subprocess
import sys
import unittest

from tests.native_process import STDERR_TAIL, stderr_digest, wait_for_announcement

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


if __name__ == "__main__":
    unittest.main()
