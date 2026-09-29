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


@requires(IMAGE)
class NativeBpCarryVerbTests(unittest.TestCase):
    """PKT-869 (HST-035, SCN-201): the operator's verbs over BP carry.
    `operator CONFIG carry JOURNAL list|inspect|pause|resume|drop' over one
    enqueued, undertaken work: ACL2 decides each control record
    (books/bp-carry-control.lisp) and renders each report; a paused or
    dropped work's `bp-obligation request' is refused by name before any
    attempt is published; the records survive a reopen; a drop is final and
    keeps the Store pin (only the receipt releases it)."""

    def setUp(self):
        self.tmp = scratch(self, "fn-native-bp-carry-")
        self.store = self.tmp / "store"
        self.journal = self.tmp / "workflow"
        self.config = self.tmp / "fn.toml"
        self.config.write_text('[store]\npath = "{}"\n'.format(self.store), encoding="ascii")
        payload = self.tmp / "article"
        self.msgid = "<native-carry@example.invalid>"
        payload.write_text(
            f"Message-ID: {self.msgid}\r\nNewsgroups: fn.test\r\n\r\nbody\r\n",
            encoding="ascii")
        for args in (("store", self.store, "init", "fn.test"),
                     ("store", self.store, "post", self.msgid, payload, "-", "-", "fn.test"),
                     ("app-journal", "workflow-init", self.store, self.journal,
                      "dtn://fn-a/", "dtn://fn-b/", "policy-a", "authority-a",
                      "3600000", "incarnation-a", "authorization-a"),
                     ("app-journal", "workflow-enqueue", self.store, self.journal,
                      "1", "0", "work-a", self.msgid, "forward-a",
                      "dtn://fn-b/", "policy-a", "terms-a"),
                     ("bp-obligation", "undertake", self.store, self.journal, "work-a", "3")):
            done = self.invoke(*args)
            self.assertEqual(done.returncode, EXIT.OK, (args, done.stderr))

    def invoke(self, *args, env=None):
        return run([IMAGE, "--fn", *args], env=environment(env), timeout=60, text=True)

    def carry(self, *words):
        return self.invoke("operator", self.config, "carry", self.journal, *words)

    def records(self):
        return {p.name: p.read_bytes()
                for p in sorted((self.journal / "records").glob("*.wf"))}

    def request(self):
        return self.invoke("bp-obligation", "request", self.store, self.journal,
                           "work-a", "attempt-1", self.tmp / "fnbs", "dtn://fn-a/",
                           "127.0.0.1", str(free_port()))

    def test_list_pause_resume_drop_and_the_request_gate(self):
        listed = self.carry("list")
        self.assertEqual(listed.returncode, EXIT.OK, listed.stderr)
        self.assertIn("carry work-a message-id=" + self.msgid, listed.stdout)
        self.assertIn("pinned=yes hold=none", listed.stdout)
        inspect = self.carry("inspect", "work-a")
        self.assertEqual(inspect.returncode, EXIT.OK, inspect.stderr)
        self.assertEqual(inspect.stdout.strip(), listed.stdout.strip())
        missing = self.carry("inspect", "work-z")
        self.assertEqual(missing.returncode, EXIT.REFUSED, missing.stderr)
        self.assertIn("unknown-work", missing.stderr)

        paused = self.carry("pause", "work-a")
        self.assertEqual(paused.returncode, EXIT.OK, paused.stderr)
        again = self.carry("pause", "work-a")
        self.assertEqual(again.returncode, EXIT.REFUSED, again.stderr)
        self.assertIn("already-paused", again.stderr)
        self.assertIn("hold=paused", self.carry("list").stdout)
        before = self.records()
        refused = self.request()
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
        self.assertIn("reason=carry-paused", refused.stderr)
        self.assertEqual(before, self.records())

        resumed = self.carry("resume", "work-a")
        self.assertEqual(resumed.returncode, EXIT.OK, resumed.stderr)
        self.assertIn("hold=none", self.carry("list").stdout)
        self.assertEqual(self.carry("resume", "work-a").returncode, EXIT.REFUSED)

        everything = self.carry("pause", "*")
        self.assertEqual(everything.returncode, EXIT.OK, everything.stderr)
        self.assertIn("hold=paused", self.carry("list").stdout)
        self.assertEqual(self.carry("resume", "*").returncode, EXIT.OK)

        dropped = self.carry("drop", "work-a", "peer", "retired")
        self.assertEqual(dropped.returncode, EXIT.OK, dropped.stderr)
        listed = self.carry("list").stdout
        self.assertIn("hold=dropped", listed)
        self.assertIn("reason=peer retired", listed)
        # The Store pin stays: only the receipt's evidence releases it.
        self.assertIn("pinned=yes", listed)
        self.assertIn("already-dropped", self.carry("drop", "work-a", "x").stderr)
        self.assertIn("dropped", self.carry("resume", "work-a").stderr)
        before = self.records()
        refused = self.request()
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
        self.assertIn("reason=carry-dropped", refused.stderr)
        self.assertEqual(before, self.records())

    def test_usage_and_help(self):
        bad = self.invoke("operator", self.config, "carry", "relative", "list")
        self.assertEqual(bad.returncode, EXIT.USAGE, bad.stderr)
        helped = self.invoke("operator", self.config, "help", "carry")
        self.assertEqual(helped.returncode, EXIT.OK, helped.stderr)
        self.assertIn("carry JOURNAL", helped.stdout + helped.stderr)
