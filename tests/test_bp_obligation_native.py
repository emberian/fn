"""Native shared-owner forwarding-obligation joins and refusal boundaries."""

import os
from pathlib import Path
import shutil
import socket
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


class NativeBpObligationBoundaryTests(unittest.TestCase):
    def test_pinned_predicate_uses_value_caller(self):
        host = (ROOT / "host/native/bp-obligation.lisp").read_text()
        self.assertIn("(fnn-owner-core\n                       'fn-owner-workflow-forward-pinnedp work-id)", host)
        self.assertNotIn("(fnn-owner-action\n                       'fn-owner-workflow-forward-pinnedp", host)


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

    # `bp-obligation recover': a fenced attempt resolved through ACL2.

    def request(self, attempt, env=None):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as reservation:
            reservation.bind(("127.0.0.1", 0))
            dead_port = reservation.getsockname()[1]
        return [str(IMAGE), "--fn", "bp-obligation", "request", str(self.store),
                str(self.journal), "work-a", attempt, str(self.tmp / "fnbs"),
                "dtn://fn-a/", "127.0.0.1", str(dead_port)]

    def test_kill_between_attempt_and_outcome_then_recover_committed(self):
        undertaken = self.invoke("bp-obligation", "undertake", self.store,
                                 self.journal, "work-a", "3")
        self.assertEqual(undertaken.returncode, 0, undertaken.stderr)
        env = dict(self.env)
        env["FN_BP_OBLIGATION_TEST_PAUSE_AFTER_ATTEMPT"] = "1"
        cut = subprocess.Popen(self.request("attempt-a"), cwd=ROOT, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            deadline = time.monotonic() + 120
            seen = b""
            while b"BP OBLIGATION ATTEMPT DURABLE" not in seen:
                self.assertLess(time.monotonic(), deadline, seen)
                self.assertIsNone(cut.poll(), seen + cut.stderr.read())
                seen += cut.stdout.readline()
        finally:
            cut.kill()
            cut.wait(timeout=15)
            cut.stdout.close()
            cut.stderr.close()

        status = self.invoke("bp-obligation", "status", self.store,
                             self.journal, "work-a")
        self.assertEqual(status.returncode, 0, status.stderr)
        self.assertIn("status=outstanding pinned=yes", status.stdout)
        refused = subprocess.run(self.request("attempt-b"), cwd=ROOT,
                                 env=self.env, capture_output=True, text=True,
                                 timeout=120, check=False)
        self.assertEqual(refused.returncode, 1, refused.stdout + refused.stderr)
        self.assertIn("fenced", refused.stdout + refused.stderr)

        before = self.records()
        for work, attempt, outcome, reason in (
                ("work-a", "attempt-other", "committed", "attempt-unknown"),
                ("work-missing", "attempt-a", "committed", "attempt-unknown"),
                ("work-a", "attempt-a", "maybe", "outcome")):
            wrong = self.invoke("bp-obligation", "recover", self.store,
                                self.journal, work, attempt, outcome)
            self.assertEqual(wrong.returncode, 1, wrong.stdout + wrong.stderr)
            self.assertIn(f"reason={reason}", wrong.stdout + wrong.stderr)
        self.assertEqual(self.records(), before)

        recovered = self.invoke("bp-obligation", "recover", self.store,
                                self.journal, "work-a", "attempt-a", "committed")
        self.assertEqual(recovered.returncode, 0,
                         recovered.stdout + recovered.stderr)
        self.assertIn("recovery durable work=work-a attempt=attempt-a "
                      "outcome=committed", recovered.stdout)
        self.assertIn("status=unknown pinned=yes", recovered.stdout)
        self.assertEqual(len(self.records()), len(before) + 1)
        again = self.invoke("bp-obligation", "recover", self.store,
                            self.journal, "work-a", "attempt-a", "committed")
        self.assertEqual(again.returncode, 1, again.stdout + again.stderr)
        self.assertIn("reason=not-fenced", again.stdout + again.stderr)

        # The journal reopens and the next request is accepted: its attempt
        # and outcome are durable (the carrier then meets a dead contact).
        accepted = subprocess.run(self.request("attempt-b"), cwd=ROOT,
                                  env=self.env, capture_output=True, text=True,
                                  timeout=120, check=False)
        self.assertIn("BP obligation request durable attempt work=work-a "
                      "attempt=attempt-b", accepted.stdout,
                      accepted.stdout + accepted.stderr)
        self.assertIn(accepted.returncode, (0, 3), accepted.stderr)
        status = self.invoke("bp-obligation", "status", self.store,
                             self.journal, "work-a")
        self.assertEqual(status.returncode, 0, status.stderr)
        self.assertIn("status=intent pinned=yes", status.stdout)
