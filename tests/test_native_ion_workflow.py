"""Actual developer-image ION submission caller and durable reopen boundaries.

Helpers are executable transport fixtures; semantic observation validation and
attempt/route decisions still run inside the image's ACL2 core. No ION daemon
or live node is used by this fault suite.
"""
import unittest

from tests.native_harness import EXIT, environment, native_image, requires, run, scratch

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(IMAGE)
class NativeIonWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.tmp = scratch(self, "fn-native-ion-")
        self.store = self.tmp / "store"
        self.journal = self.tmp / "workflow"
        self.observations = self.tmp / "observations"
        self.observations.mkdir(mode=0o700)
        self.article = self.tmp / "article"
        self.msgid = "<ion-native@example.invalid>"
        self.article.write_bytes(
            b"Message-ID: <ion-native@example.invalid>\r\nNewsgroups: fn.test\r\n\r\nbody\r\n")
        for args in [
            ("store", self.store, "init", "fn.test"),
            ("store", self.store, "post", self.msgid, self.article, "-", "-", "fn.test"),
            ("app-journal", "workflow-init", self.store, self.journal,
             "dtn://fn-a/", "dtn://fn-b/", "policy-a", "authority-a",
             getattr(self, "lifetime", "3600000"), "incarnation-a", "authorization-a"),
            ("app-journal", "workflow-enqueue", self.store, self.journal,
             "1", "0", "work-a", self.msgid, "forward-a",
             "dtn://fn-b/", "policy-a", "terms-a"),
        ]:
            result = self.invoke(*args)
            self.assertEqual(result.returncode, EXIT.OK, result.stderr)

    def invoke(self, *args):
        return run([IMAGE, "--fn", *args], env=environment(), timeout=60, text=True)

    def submit(self, body):
        helper = self.tmp / "helper"
        helper.write_text("#!/bin/sh\nset -eu\n" + body)
        helper.chmod(0o700)
        return self.invoke(
            "app-journal", "workflow-ion-submit", self.store, self.journal,
            "2", "0", "work-a", "attempt-a", "ipn:2.1", "ipn:1.1",
            helper, self.observations)

    def status(self):
        return self.invoke("app-journal", "workflow-ion-status", self.store,
                           self.journal, "work-a", "attempt-a", "0")

    def assert_outstanding(self):
        result = self.invoke("app-journal", "workflow-status", self.store,
                             self.journal, "work-a")
        self.assertEqual(result.returncode, EXIT.OK, result.stderr)
        # The ACL2 status projection exposes the recovered attempt state for
        # outstanding attempted work. Receipted and absent are distinct.
        self.assertIn("status=restart-observed", result.stdout)

    def test_observation_binds_explicit_route_and_survives_reopen(self):
        result = self.submit(
            'test "$1" = ipn:1.1\ntest "$2" = ipn:2.1\n'
            'test "$3" = dtn://fn-b/\ntest -s "$4"\ntest "$5" = 3600\n'
            'printf "observed-v1|%s|%s|%s|42|7\\n" "$3" "$2" "$1" > "$6"\n')
        self.assertEqual(result.returncode, EXIT.OK, result.stderr)
        reopened = self.status()
        self.assertEqual(reopened.returncode, EXIT.OK, reopened.stderr)
        self.assertIn("source=ipn:1.1 msec=42 sequence=7", reopened.stdout)
        self.assert_outstanding()

    def test_entered_send_without_observation_remains_uncertain(self):
        result = self.submit("exit 3\n")
        self.assertEqual(result.returncode, EXIT.UNCERTAIN, result.stderr)
        reopened = self.status()
        self.assertEqual(reopened.returncode, EXIT.UNCERTAIN, reopened.stderr)
        self.assertIn("ION uncertain", reopened.stdout)
        self.assert_outstanding()

    def test_success_exit_with_missing_observation_remains_uncertain(self):
        result = self.submit("exit 0\n")
        self.assertEqual(result.returncode, EXIT.UNCERTAIN, result.stderr)
        self.assertEqual(self.status().returncode, EXIT.UNCERTAIN)
        self.assert_outstanding()

    def test_helper_process_death_remains_uncertain_after_reopen(self):
        result = self.submit('kill -KILL "$$"\n')
        self.assertEqual(result.returncode, EXIT.UNCERTAIN, result.stderr)
        self.assertEqual(self.status().returncode, EXIT.UNCERTAIN)
        self.assert_outstanding()

    def test_noncanonical_timestamp_cannot_bind_observation(self):
        result = self.submit(
            'printf "observed-v1|dtn://fn-b/|ipn:2.1|ipn:1.1|042|7\\n" > "$6"\n')
        self.assertEqual(result.returncode, EXIT.UNCERTAIN, result.stderr)
        self.assertEqual(self.status().returncode, EXIT.UNCERTAIN)
        self.assert_outstanding()

    def test_success_exit_with_wrong_application_peer_remains_uncertain(self):
        result = self.submit(
            'printf "observed-v1|dtn://wrong/|ipn:2.1|ipn:1.1|42|7\\n" > "$6"\n')
        self.assertEqual(result.returncode, EXIT.UNCERTAIN, result.stderr)
        self.assertEqual(self.status().returncode, EXIT.UNCERTAIN)
        self.assert_outstanding()

    def test_success_exit_with_wrong_bp_route_remains_uncertain(self):
        result = self.submit(
            'printf "observed-v1|dtn://fn-b/|ipn:9.1|ipn:1.1|42|7\\n" > "$6"\n')
        self.assertEqual(result.returncode, EXIT.UNCERTAIN, result.stderr)
        self.assertEqual(self.status().returncode, EXIT.UNCERTAIN)
        self.assert_outstanding()

    def test_pre_send_refusal_does_not_fabricate_observation(self):
        result = self.submit("exit 1\n")
        self.assertEqual(result.returncode, EXIT.REFUSED, result.stderr)
        # The durable route records a potential attempt, even when the helper
        # refuses. Reopen must preserve it without claiming transport success.
        self.assertEqual(self.status().returncode, EXIT.UNCERTAIN)
        self.assert_outstanding()

    def test_unrepresentable_lifetime_refuses_before_attempt_or_helper(self):
        self.journal = self.tmp / "unrepresentable-workflow"
        initialized = self.invoke(
            "app-journal", "workflow-init", self.store, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "policy-a", "authority-a",
            "60001", "incarnation-a", "authorization-a")
        self.assertEqual(initialized.returncode, EXIT.OK, initialized.stderr)
        enqueued = self.invoke(
            "app-journal", "workflow-enqueue", self.store, self.journal,
            "1", "0", "work-a", self.msgid, "forward-a",
            "dtn://fn-b/", "policy-a", "terms-a")
        self.assertEqual(enqueued.returncode, EXIT.OK, enqueued.stderr)
        before = {p.name: p.read_bytes() for p in (self.journal / "records").iterdir()}
        marker = self.tmp / "helper-entered"
        result = self.submit(f'touch "{marker}"\nexit 0\n')
        self.assertEqual(result.returncode, EXIT.REFUSED, result.stderr)
        self.assertIn("not exactly representable", result.stderr)
        self.assertFalse(marker.exists())
        self.assertEqual(before, {p.name: p.read_bytes()
                                 for p in (self.journal / "records").iterdir()})
