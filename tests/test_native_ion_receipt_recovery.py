"""Actual offline ION-workflow receipt publication and reopen boundaries.

No transport daemon is used. The submission helper copies only the ACL2-authored
request; native Store/FNRJ callers construct and authorize the receipt.
"""
import re
import shlex
import unittest

from tests.native_harness import EXIT, environment, native_image, requires, run
from tests.test_native_ion_workflow import NativeIonWorkflowTests

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(IMAGE)
class NativeIonReceiptRecoveryTests(unittest.TestCase):
    setUp = NativeIonWorkflowTests.setUp
    submit = NativeIonWorkflowTests.submit
    status = NativeIonWorkflowTests.status

    def invoke(self, *args, extra=None):
        return run([IMAGE, "--fn", *args], env=environment(extra),
                   timeout=60, text=True)

    def prepare_receipt(self, decision_fault=False):
        undertaken = self.invoke("app-journal", "workflow-undertake", self.store,
                                 self.journal, "work-a", "3")
        self.assertEqual(undertaken.returncode, EXIT.OK, undertaken.stderr)
        self.request = self.tmp / "request.adu"
        sent = self.submit(
            f'cp "$4" {shlex.quote(str(self.request))}\n'
            'printf "observed-v1|%s|%s|%s|42|7\\n" "$3" "$2" "$1" > "$6"\n')
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.receiver = self.tmp / "receiver"
        self.receipt_journal = self.tmp / "receipts"
        archive = self.tmp / "export"
        for args in [
            ("store", self.receiver, "init", "fn.test"),
            ("store", self.receiver, "post", self.msgid, self.article,
             "-", "-", "fn.test"),
            ("store", self.receiver, "export", archive),
            ("app-journal", "receipt-init", self.receiver, self.receipt_journal,
             "dtn://fn-b/", "policy-a", "authority-a"),
        ]:
            result = self.invoke(*args)
            self.assertEqual(result.returncode, EXIT.OK, result.stderr)
        records = list((archive / "records").glob("*.txn"))
        self.assertEqual(len(records), 1)
        completed = self.invoke(
            "app-journal", "receipt-complete", self.receiver,
            self.receipt_journal, "ipn:1.1|42|7", self.request, records[0],
            "work-a", "receipt-a", extra=(
                {"FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE": "1"}
                if decision_fault else None))
        self.assertEqual(completed.returncode,
                         EXIT.UNCERTAIN if decision_fault else EXIT.OK,
                         completed.stderr)
        first = self.replay()
        second = self.replay()
        self.assertEqual(first.returncode, EXIT.OK, first.stderr)
        self.assertEqual(second.returncode, EXIT.OK, second.stderr)
        self.assertEqual(first.stdout, second.stdout)
        encoded = re.search(r"hex=([0-9a-f]+)", first.stdout)
        self.assertIsNotNone(encoded, first.stdout)
        self.receipt = self.tmp / "receipt.adu"
        self.receipt.write_bytes(bytes.fromhex(encoded.group(1)))

    def replay(self):
        return self.invoke("app-journal", "receipt-replay", self.receiver,
                           self.receipt_journal, self.request)

    def accept(self, extra=None):
        return self.invoke("app-journal", "workflow-receipt", self.store,
                           self.journal, self.receipt, "3", "0",
                           "trusted-local-observation-v0", extra=extra)

    def snapshot(self):
        return {p.name: p.read_bytes()
                for p in (self.journal / "records").iterdir()}

    def test_receiver_uncertain_decision_recovers_exact_receipt_on_reopen(self):
        self.prepare_receipt(decision_fault=True)
        # Visibility alone did not change the failed call to accepted. A fresh
        # native open validates durable journal bytes before regeneration.
        accepted = self.accept()
        self.assertEqual(accepted.returncode, EXIT.OK, accepted.stderr)
        reopened = self.invoke("app-journal", "workflow-status", self.store,
                               self.journal, "work-a")
        self.assertEqual(reopened.returncode, EXIT.OK, reopened.stderr)
        self.assertIn("status=receipted", reopened.stdout)

    def test_sender_uncertain_release_reopens_and_duplicate_cannot_mutate(self):
        self.prepare_receipt()
        before = self.invoke("store", self.store, "retention")
        self.assertEqual(before.returncode, EXIT.OK, before.stderr)
        uncertain = self.accept({"FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE": "1"})
        self.assertEqual(uncertain.returncode, EXIT.UNCERTAIN, uncertain.stderr)
        self.assertIn("publication is uncertain", uncertain.stderr)
        reopened = self.invoke("app-journal", "workflow-status", self.store,
                               self.journal, "work-a")
        self.assertEqual(reopened.returncode, EXIT.OK, reopened.stderr)
        self.assertIn("status=receipted", reopened.stdout)
        records = self.snapshot()
        duplicate = self.accept()
        self.assertEqual(duplicate.returncode, EXIT.REFUSED, duplicate.stderr)
        self.assertEqual(records, self.snapshot())
        after = self.invoke("store", self.store, "retention")
        self.assertEqual(after.returncode, EXIT.OK, after.stderr)
        self.assertEqual(before.stdout, after.stdout)

    def test_committed_receipt_duplicate_is_refused_without_publication(self):
        self.prepare_receipt()
        accepted = self.accept()
        self.assertEqual(accepted.returncode, EXIT.OK, accepted.stderr)
        before = self.snapshot()
        duplicate = self.accept()
        self.assertEqual(duplicate.returncode, EXIT.REFUSED, duplicate.stderr)
        self.assertEqual(before, self.snapshot())
