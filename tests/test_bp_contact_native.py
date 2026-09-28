"""Native FNBS contact-window gate over a durable interrupted job."""

import unittest

from tests.native_harness import (
    EXIT, AcceptThenClosePeer, native_image, requires, run, scratch)

IMAGE = native_image("FN_NATIVE_BP_HOST")


@requires(IMAGE)
class NativeBpContactTests(unittest.TestCase):
    def setUp(self):
        self.tmp = scratch(self, "fn-bp-contact-")
        self.journal = self.tmp / "journal"
        self.adu = self.tmp / "adu"
        self.adu.write_bytes(b"contact interruption witness")
        # The outage: the peer accepts and closes before the transfer
        # completes, so the job's transfers are :uncertain, never :failed.
        # specs/host.md "BP run classes" (books/bp-run-class.lisp, PRF-131):
        # a connection lost after it existed is EXIT.INTERRUPTED (the job
        # stays and is re-offered; no recovery); EXIT.UNCERTAIN stays the fence.
        self.peer = AcceptThenClosePeer()
        self.addCleanup(self.peer.close)

    def invoke(self, verb, *args):
        return run([IMAGE, "--fn", verb, *args], timeout=30)

    def records(self):
        return sorted((self.journal / "lifecycle").glob("*.fnb"))

    def tick(self, start, end, *rest):
        return self.invoke(
            "bp-contact", "tick", self.journal, "dtn://fn-a/",
            "dtn://fn-b/", start, end, *rest,
        )

    def test_closed_window_interruption_and_anchored_wall_jump(self):
        queued = self.invoke(
            "bp-service", "run", "127.0.0.1", self.peer.port, self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "contact-work", "contact-attempt", 0,
            3600000, 2, 32, 1048576, 0, 0,
        )
        self.assertEqual(queued.returncode, EXIT.INTERRUPTED, queued.stderr)
        self.assertIn(b"BP queue accepted", queued.stdout)
        before = len(self.records())

        closed = self.tick(1, 1, 3600000, 2, 32, 1048576, 0, 0)
        self.assertEqual(closed.returncode, EXIT.OK, closed.stderr)
        self.assertIn(b"BP contact closed", closed.stdout)
        self.assertEqual(len(self.records()), before)

        interrupted = self.tick(0, 60000, 3600000, 2, 32, 1048576, 0, 0)
        self.assertEqual(interrupted.returncode, EXIT.INTERRUPTED, interrupted.stderr)
        self.assertIn(b"BP contact open", interrupted.stdout)
        self.assertGreater(self.peer.accepted, 1, "each transfer must follow a connection")
        self.assertGreater(len(self.records()), before)
        after_interruption = len(self.records())

        later = self.tick(1, 1, 3600000, 2, 32, 1048576, 3600001, 0)
        self.assertEqual(later.returncode, EXIT.OK, later.stderr)
        self.assertIn(b"BP contact closed", later.stdout)
        self.assertNotIn(b"release", later.stdout.lower())
        self.assertEqual(len(self.records()), after_interruption)

    def test_bad_window_and_decimal_bound(self):
        malformed = self.tick(10, 9)
        self.assertEqual(malformed.returncode, EXIT.REFUSED, malformed.stderr)
        self.assertFalse(self.journal.exists())
        overlong = self.tick("9" * 21, 0)
        self.assertEqual(overlong.returncode, EXIT.USAGE, overlong.stderr)
        self.assertFalse(self.journal.exists())
        overflow = self.tick(0, 18446744073709551615)
        self.assertEqual(overflow.returncode, EXIT.REFUSED, overflow.stderr)
        self.assertFalse(self.journal.exists())


if __name__ == "__main__":
    unittest.main()
