"""Native FNBS contact-window gate over a durable interrupted job."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests.native_process import AcceptThenClosePeer

# specs/host.md "BP run classes" (books/bp-run-class.lisp, PRF-131): a
# connection lost after it existed is exit 6 (connection-local: the job stays
# and is re-offered; no recovery); exit 3 stays the fence.
LOST = 6



ROOT = Path(__file__).resolve().parent.parent


class NativeBpContactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.image = Path(os.environ.get(
            "FN_NATIVE_BP_HOST", ROOT / "build" / "fn-host-dtn"))
        if not os.access(cls.image, os.X_OK):
            raise unittest.SkipTest(f"DTN native image missing: {cls.image}")

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-bp-contact-"))
        self.journal = self.tmp / "journal"
        self.adu = self.tmp / "adu"
        self.adu.write_bytes(b"contact interruption witness")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        # The outage: the peer accepts and closes before the transfer
        # completes, so the job's transfers are :uncertain, never :failed.
        self.peer = AcceptThenClosePeer()
        self.addCleanup(self.peer.close)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def invoke(self, verb, *args):
        return subprocess.run(
            [str(self.image), "--fn", verb, *map(str, args)],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, timeout=30, check=False,
        )

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
        self.assertEqual(queued.returncode, LOST, queued.stderr)
        self.assertIn("BP queue accepted", queued.stdout)
        before = len(self.records())

        closed = self.tick(1, 1, 3600000, 2, 32, 1048576, 0, 0)
        self.assertEqual(closed.returncode, 0, closed.stderr)
        self.assertIn("BP contact closed", closed.stdout)
        self.assertEqual(len(self.records()), before)

        interrupted = self.tick(0, 60000, 3600000, 2, 32, 1048576, 0, 0)
        self.assertEqual(interrupted.returncode, LOST, interrupted.stderr)
        self.assertIn("BP contact open", interrupted.stdout)
        self.assertGreater(self.peer.accepted, 1, "each transfer must follow a connection")
        self.assertGreater(len(self.records()), before)
        after_interruption = len(self.records())

        later = self.tick(1, 1, 3600000, 2, 32, 1048576, 3600001, 0)
        self.assertEqual(later.returncode, 0, later.stderr)
        self.assertIn("BP contact closed", later.stdout)
        self.assertNotIn("release", later.stdout.lower())
        self.assertEqual(len(self.records()), after_interruption)

    def test_bad_window_and_decimal_bound(self):
        malformed = self.tick(10, 9)
        self.assertEqual(malformed.returncode, 1, malformed.stderr)
        self.assertFalse(self.journal.exists())
        overlong = self.tick("9" * 21, 0)
        self.assertEqual(overlong.returncode, 5, overlong.stderr)
        self.assertFalse(self.journal.exists())
        overflow = self.tick(0, 18446744073709551615)
        self.assertEqual(overflow.returncode, 1, overflow.stderr)
        self.assertFalse(self.journal.exists())


if __name__ == "__main__":
    unittest.main()
