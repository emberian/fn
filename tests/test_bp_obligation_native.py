"""Native shared-owner forwarding-obligation joins and refusal boundaries."""

import time
import unittest

from tests.native_harness import (
    EXIT, ROOT, environment, free_port, native_image, requires, run, scratch, start)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


class NativeBpObligationBoundaryTests(unittest.TestCase):
    def test_pinned_predicate_uses_value_caller(self):
        host = (ROOT / "host/native/bp-obligation.lisp").read_text()
        self.assertIn("(fnn-owner-core\n                       'fn-owner-workflow-forward-pinnedp work-id)", host)
        self.assertNotIn("(fnn-owner-action\n                       'fn-owner-workflow-forward-pinnedp", host)


@requires(IMAGE)
class NativeBpObligationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = scratch(self, "fn-native-bp-obligation-")
        self.store = self.tmp / "store"
        self.journal = self.tmp / "workflow"
        self.payload = self.tmp / "article"
        self.msgid = "<native-obligation@example.invalid>"
        self.payload.write_text(
            f"Message-ID: {self.msgid}\r\nNewsgroups: fn.test\r\n\r\nbody\r\n",
            encoding="ascii",
        )
        self.assertEqual(self.invoke("store", self.store, "init", "fn.test").returncode, EXIT.OK)
        posted = self.invoke(
            "store", self.store, "post", self.msgid, self.payload,
            "-", "-", "fn.test",
        )
        self.assertEqual(posted.returncode, EXIT.OK, posted.stderr)
        initialized = self.invoke(
            "app-journal", "workflow-init", self.store, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "policy-a", "authority-a",
            "3600000", "incarnation-a", "authorization-a",
        )
        self.assertEqual(initialized.returncode, EXIT.OK, initialized.stderr)
        enqueued = self.invoke(
            "app-journal", "workflow-enqueue", self.store, self.journal,
            "1", "0", "work-a", self.msgid, "forward-a",
            "dtn://fn-b/", "policy-a", "terms-a",
        )
        self.assertEqual(enqueued.returncode, EXIT.OK, enqueued.stderr)

    def invoke(self, *args, env=None):
        return run([IMAGE, "--fn", *args], env=environment(env), timeout=60, text=True)

    def records(self):
        return {p.name: p.read_bytes()
                for p in sorted((self.journal / "records").glob("*.wf"))}

    def test_shared_owner_admits_and_recovers_forward_pin(self):
        admitted = self.invoke(
            "bp-obligation", "undertake", self.store, self.journal,
            "work-a", "3",
        )
        self.assertEqual(admitted.returncode, EXIT.OK, admitted.stderr)
        self.assertIn("owner durable undertaking", admitted.stdout)

        reopened = self.invoke(
            "bp-obligation", "status", self.store, self.journal, "work-a",
        )
        self.assertEqual(reopened.returncode, EXIT.OK, reopened.stderr)
        self.assertIn("status=outstanding", reopened.stdout)

    def test_shared_owner_capacity_refusal_publishes_nothing(self):
        before = self.records()
        refused = self.invoke(
            "bp-obligation", "undertake", self.store, self.journal,
            "work-a", str(1 << 63),
        )
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
        self.assertIn("obligation is not admissible", refused.stderr)
        self.assertEqual(before, self.records())

    def test_shared_owner_refuses_unsigned_receipt_profile(self):
        admitted = self.invoke(
            "bp-obligation", "undertake", self.store, self.journal,
            "work-a", "3",
        )
        self.assertEqual(admitted.returncode, EXIT.OK, admitted.stderr)
        receipt = self.tmp / "receipt.adu"
        receipt.write_bytes(b"unsigned")
        before = self.records()
        refused = self.invoke(
            "bp-obligation", "receipt", self.store, self.journal,
            receipt, "2", "0", "unsigned-lab",
        )
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
        self.assertIn("authentication profile is unsupported", refused.stderr)
        self.assertEqual(before, self.records())

    # `bp-obligation recover': a fenced attempt resolved through ACL2.

    def request(self, attempt, env=None):
        return [IMAGE, "--fn", "bp-obligation", "request", self.store, self.journal,
                "work-a", attempt, self.tmp / "fnbs", "dtn://fn-a/", "127.0.0.1",
                free_port()]

    def route_to_a_dead_contact(self):
        """The Store's route table names a boundary for dtn://fn-b/ whose
        contact nothing listens on.  Since PRF-103 (spec 4.6) the carrier
        queues a job only to a boundary the route table names: without one
        the request is refused by routing (`decision=no-route`, exit 1)
        after its durable attempt, and this test's carrier never meets the
        dead contact it is about."""
        dead_port, listen_port = free_port(), free_port()
        config = self.tmp / "fn.toml"
        config.write_text(f'[store]\npath = "{self.store}"\n', encoding="ascii")
        boundary = self.invoke("operator", config, "bp-boundary", "add",
                               "fn-b-boundary", "fn-b.bp.gate.invalid",
                               "dtn://fn-b/", listen_port, "contact", dead_port)
        self.assertEqual(boundary.returncode, EXIT.OK, boundary.stdout + boundary.stderr)
        routed = self.invoke("operator", config, "bp-route", "add",
                             "dtn://fn-b/*", "fn-b-boundary")
        self.assertEqual(routed.returncode, EXIT.OK, routed.stdout + routed.stderr)

    def test_kill_between_attempt_and_outcome_then_recover_committed(self):
        self.route_to_a_dead_contact()
        undertaken = self.invoke("bp-obligation", "undertake", self.store,
                                 self.journal, "work-a", "3")
        self.assertEqual(undertaken.returncode, EXIT.OK, undertaken.stderr)
        # The pause holds the process after the attempt record is durable;
        # watch the journal, not the pipe (the marker line is not flushed to
        # a pipe before the process ends).
        count = len(self.records())
        cut = start(self.request("attempt-a"), cwd=ROOT, env=environment(
            {"FN_BP_OBLIGATION_TEST_PAUSE_AFTER_ATTEMPT": "1"}))
        try:
            deadline = time.monotonic() + 120
            while len(self.records()) <= count:
                self.assertLess(time.monotonic(), deadline)
                self.assertIsNone(cut.poll())
                time.sleep(0.2)
            time.sleep(1)
            self.assertIsNone(cut.poll())
        finally:
            cut.kill()
            cut.wait(timeout=15)
            cut.finish()

        status = self.invoke("bp-obligation", "status", self.store,
                             self.journal, "work-a")
        self.assertEqual(status.returncode, EXIT.OK, status.stderr)
        self.assertIn("status=outstanding pinned=yes", status.stdout)
        refused = run(self.request("attempt-b"), timeout=120, text=True)
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stdout + refused.stderr)
        self.assertIn("fenced", refused.stdout + refused.stderr)

        before = self.records()
        for work, attempt, outcome, reason in (
                ("work-a", "attempt-other", "committed", "attempt-unknown"),
                ("work-missing", "attempt-a", "committed", "attempt-unknown"),
                ("work-a", "attempt-a", "maybe", "outcome")):
            wrong = self.invoke("bp-obligation", "recover", self.store,
                                self.journal, work, attempt, outcome)
            self.assertEqual(wrong.returncode, EXIT.REFUSED, wrong.stdout + wrong.stderr)
            self.assertIn(f"reason={reason}", wrong.stdout + wrong.stderr)
        self.assertEqual(self.records(), before)

        recovered = self.invoke("bp-obligation", "recover", self.store,
                                self.journal, "work-a", "attempt-a", "committed")
        self.assertEqual(recovered.returncode, EXIT.OK,
                         recovered.stdout + recovered.stderr)
        self.assertIn("recovery durable work=work-a attempt=attempt-a "
                      "outcome=committed", recovered.stdout)
        self.assertIn("status=unknown pinned=yes", recovered.stdout)
        self.assertEqual(len(self.records()), len(before) + 1)
        again = self.invoke("bp-obligation", "recover", self.store,
                            self.journal, "work-a", "attempt-a", "committed")
        self.assertEqual(again.returncode, EXIT.REFUSED, again.stdout + again.stderr)
        self.assertIn("reason=not-fenced", again.stdout + again.stderr)

        # The journal reopens and the next request is accepted: its attempt
        # and outcome are durable (the carrier then meets a dead contact).
        accepted = run(self.request("attempt-b"), timeout=120, text=True)
        self.assertIn("BP obligation request durable attempt work=work-a "
                      "attempt=attempt-b", accepted.stdout,
                      accepted.stdout + accepted.stderr)
        # By specification (specs/host.md "BP run classes", PRF-143): a
        # contact that never connected is the run class :not-connected, exit
        # 7 (before PRF-143 the test allowed 0 or 3); the job stays queued.
        self.assertEqual(accepted.returncode, EXIT.NOT_CONNECTED, accepted.stdout + accepted.stderr)
        self.assertIn("BP obligation request carrier durable work=work-a "
                      "attempt=attempt-b", accepted.stdout)
        self.assertIn("BP forwarding retained reason=failed", accepted.stdout)
        self.assertNotIn("decision=no-route", accepted.stdout)
        status = self.invoke("bp-obligation", "status", self.store,
                             self.journal, "work-a")
        self.assertEqual(status.returncode, EXIT.OK, status.stderr)
        self.assertIn("pinned=yes", status.stdout)
        self.assertNotIn("status=outstanding", status.stdout)


if __name__ == "__main__":
    unittest.main()
