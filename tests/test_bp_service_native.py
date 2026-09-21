"""Native outage/restart evidence for the durable BP lifecycle service."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpServiceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.image = ROOT / "build" / "fn-host-dtn"
        if not os.access(cls.image, os.X_OK):
            raise unittest.SkipTest(
                f"DTN native image missing: {cls.image} "
                "(FN_NATIVE_BUILD=host/native/build-dtn.lisp tools/build_native_host.sh)"
            )

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-bp-service-"))
        self.journal = self.tmp / "journal"
        self.adu = self.tmp / "adu"
        self.adu.write_bytes(b"hello lifecycle")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def invoke(self, *args):
        return subprocess.run(
            [str(self.image), "--fn", "bp-service", *map(str, args)],
            cwd=ROOT,
            env=self.env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
            text=True,
        )

    def run_outage(self, adu=None):
        return self.invoke(
            "run", "127.0.0.1", "1", adu or self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "work-1", "attempt-1", "0",
        )

    def records(self):
        return sorted((self.journal / "lifecycle").glob("*.fnb"))

    def test_outage_restart_duplicate_and_conflict(self):
        first = self.run_outage()
        self.assertEqual(first.returncode, 3, first.stderr)
        self.assertIn("BP queue accepted", first.stdout)
        self.assertIn("BP forwarding retained reason=uncertain", first.stdout)
        self.assertEqual(len(self.records()), 3)  # queued, attempting, requeued

        frontier = (self.journal / "sequence" / "frontier.fnb").read_bytes()
        resumed = self.invoke("resume", self.journal, "dtn://fn-a/")
        self.assertEqual(resumed.returncode, 3, resumed.stderr)
        self.assertIn("BP queue recovered jobs=1", resumed.stdout)
        self.assertEqual(len(self.records()), 5)

        duplicate = self.run_outage()
        self.assertEqual(duplicate.returncode, 3, duplicate.stderr)
        self.assertIn("status=duplicate", duplicate.stdout)
        self.assertEqual(
            (self.journal / "sequence" / "frontier.fnb").read_bytes(), frontier,
            "an idempotent enqueue must reuse its durable object binding",
        )

        contrary = self.tmp / "contrary"
        contrary.write_bytes(b"contrary bytes")
        conflict = self.run_outage(contrary)
        self.assertEqual(conflict.returncode, 3, conflict.stderr)
        self.assertIn("BP queue refused reason=enqueue-conflict", conflict.stdout)

    def test_shared_spool_owner_precedes_lifecycle_mutation(self):
        owner = subprocess.Popen(
            [str(self.image), "--fn", "tcpcl", "listen", "0", "1",
             str(self.journal), "dtn://fn-a/", "-", "4", "1024",
             "1048576", "-", "-"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True,
        )
        try:
            line = owner.stdout.readline()
            self.assertIn("TCPCL LISTENING", line)
            refused = self.run_outage()
            self.assertEqual(refused.returncode, 1, refused.stderr)
            self.assertIn("spool is already owned", refused.stderr)
            self.assertFalse((self.journal / "sequence").exists())
            self.assertFalse((self.journal / "lifecycle").exists())
            self.assertIsNone(owner.poll())
        finally:
            owner.kill()
            owner.wait(timeout=10)
            owner.stdout.close()


if __name__ == "__main__":
    unittest.main()
