"""Native shared-owner forwarding-obligation joins and refusal boundaries."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


class NativeBpObligationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(f"native host image missing: {IMAGE}")

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-native-bp-obligation-"))
        self.addCleanup(shutil.rmtree, self.tmp)
        self.store = self.tmp / "store"
        self.journal = self.tmp / "workflow"
        self.payload = self.tmp / "article"
        self.msgid = "<native-obligation@example.invalid>"
        self.payload.write_text(
            f"Message-ID: {self.msgid}\r\nNewsgroups: fn.test\r\n\r\nbody\r\n",
            encoding="ascii",
        )
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.assertEqual(self.invoke("store", self.store, "init", "fn.test").returncode, 0)
        posted = self.invoke(
            "store", self.store, "post", self.msgid, self.payload,
            "-", "-", "fn.test",
        )
        self.assertEqual(posted.returncode, 0, posted.stderr)
        initialized = self.invoke(
            "app-journal", "workflow-init", self.store, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "policy-a", "authority-a",
            "3600000", "incarnation-a", "authorization-a",
        )
        self.assertEqual(initialized.returncode, 0, initialized.stderr)
        enqueued = self.invoke(
            "app-journal", "workflow-enqueue", self.store, self.journal,
            "1", "0", "work-a", self.msgid, "forward-a",
            "dtn://fn-b/", "policy-a", "terms-a",
        )
        self.assertEqual(enqueued.returncode, 0, enqueued.stderr)

    def invoke(self, *args, env=None):
        return subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
            env=env or self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, timeout=60, check=False,
        )

    def records(self):
        return {p.name: p.read_bytes()
                for p in sorted((self.journal / "records").glob("*.wf"))}

    def test_shared_owner_admits_and_recovers_forward_pin(self):
        admitted = self.invoke(
            "bp-obligation", "undertake", self.store, self.journal,
            "work-a", "3",
        )
        self.assertEqual(admitted.returncode, 0, admitted.stderr)
        self.assertIn("owner durable undertaking", admitted.stdout)

        reopened = self.invoke(
            "bp-obligation", "status", self.store, self.journal, "work-a",
        )
        self.assertEqual(reopened.returncode, 0, reopened.stderr)
        self.assertIn("status=outstanding", reopened.stdout)

    def test_shared_owner_capacity_refusal_publishes_nothing(self):
        before = self.records()
        refused = self.invoke(
            "bp-obligation", "undertake", self.store, self.journal,
            "work-a", str(1 << 63),
        )
        self.assertEqual(refused.returncode, 1, refused.stderr)
        self.assertIn("obligation is not admissible", refused.stderr)
        self.assertEqual(before, self.records())

    def test_shared_owner_refuses_unsigned_receipt_profile(self):
        admitted = self.invoke(
            "bp-obligation", "undertake", self.store, self.journal,
            "work-a", "3",
        )
        self.assertEqual(admitted.returncode, 0, admitted.stderr)
        receipt = self.tmp / "receipt.adu"
        receipt.write_bytes(b"unsigned")
        before = self.records()
        refused = self.invoke(
            "bp-obligation", "receipt", self.store, self.journal,
            receipt, "2", "0", "unsigned-lab",
        )
        self.assertEqual(refused.returncode, 1, refused.stderr)
        self.assertIn("authentication profile is unsupported", refused.stderr)
        self.assertEqual(before, self.records())


if __name__ == "__main__":
    unittest.main()
