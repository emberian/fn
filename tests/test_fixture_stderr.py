"""The shared native owner fixture never wedges its owner on stderr (PKT-505).

tests/test_native_operator_verbs.py `start_owner' is the fixture nine native
modules start the owner through.  It put the owner's stderr on a pipe nobody
read until the owner stopped; the owner logs one line per accepted POST under
its log mutex, so about 500 POSTs filled the pipe's 64 KiB and the owner
stopped answering (exposure-reply-size's record, section 4).

These cases need no image.  The "owner" is a stand-in executable that behaves
like one on the fixture's side of the interface: it logs 1 MiB to stderr
(about 2,000 POSTs' worth at the owner's line length) before it announces
LISTENING, logs 1 MiB more while serving, and only then marks that it
"answered"; it exits 0 on SIGTERM.  With the fixture's stderr the stand-in
must announce, answer and exit, and the caller must read back all 2 MiB.
The control runs the same stand-in with stderr on an unread pipe, as the
fixture did, and shows that it never announces: the trap is real and the
stand-in reproduces it.
"""

from __future__ import annotations

import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import time
import unittest

from tests import test_native_operator_verbs as verbs

MIB = 1024 * 1024
LINE = b"owner: accepted article <x@example.invalid> number=1 group=fn.test\n"

STAND_IN = r'''#!{python}
import os, signal, sys
answered = sys.argv[-2] + ".answered"
signal.signal(signal.SIGTERM, lambda *_: os._exit(0))
line = {line!r}
def log(total):
    written = 0
    while written < total:
        sys.stderr.buffer.write(line)
        sys.stderr.buffer.flush()
        written += len(line)
log({mib})
sys.stdout.buffer.write(b"LISTENING 127.0.0.1:1\n")
sys.stdout.buffer.flush()
log({mib})
open(answered, "wb").close()
signal.pause()
'''


class FixtureStderrTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-fixture-stderr-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        # start_owner runs IMAGE --fn operator CONFIG run: CONFIG is argv[-2].
        self.config = self.root / "fn.toml"
        self.image = self.root / "stand-in-owner"
        self.image.write_text(STAND_IN.format(python=sys.executable, line=LINE, mib=MIB),
                              encoding="ascii")
        os.chmod(self.image, 0o755)

    start_owner = verbs.NativeOperatorUncertainOutcomeTests.start_owner
    reap = verbs.NativeOperatorUncertainOutcomeTests.reap

    def wait_answered(self, seconds):
        marker = Path(str(self.config) + ".answered")
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            if marker.exists():
                return True
            time.sleep(0.05)
        return False

    def test_an_owner_logging_2_mib_announces_answers_and_stops(self):
        owner = self.start_owner(self.image)
        self.assertTrue(self.wait_answered(60),
                        "the stand-in owner blocked while logging")
        self.assertIsNone(owner.poll())
        owner.send_signal(signal.SIGTERM)
        self.assertEqual(owner.wait(timeout=30), 0)
        log = owner.stderr.read()
        self.assertEqual(len(log), 2 * ((MIB + len(LINE) - 1) // len(LINE)) * len(LINE))
        self.assertTrue(log.startswith(LINE) and log.endswith(LINE))
        self.assertEqual(owner.stderr_path.parent, self.root)

    def test_each_owner_a_test_starts_has_its_own_log(self):
        first = self.start_owner(self.image)
        self.assertTrue(self.wait_answered(60))
        first.send_signal(signal.SIGTERM)
        self.assertEqual(first.wait(timeout=30), 0)
        os.unlink(str(self.config) + ".answered")
        second = self.start_owner(self.image)
        self.assertTrue(self.wait_answered(60))
        self.assertNotEqual(first.stderr_path, second.stderr_path)

    def test_control_the_same_owner_on_an_unread_pipe_never_announces(self):
        process = subprocess.Popen(
            [str(self.image), "--fn", "operator", str(self.config), "run"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.addCleanup(self.reap, process)
        self.assertEqual(select.select([process.stdout], [], [], 3)[0], [],
                         "the stand-in announced with 1 MiB on an unread pipe")
        self.assertIsNone(process.poll())
        self.assertFalse(self.wait_answered(0.5))


if __name__ == "__main__":
    unittest.main()
