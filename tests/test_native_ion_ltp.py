"""Opt-in real ION/LTP submission through the developer image's FNWF caller.

FN_ION_LAB_RUN names already-started, exclusive configs made by
prepare_isolated_lab.py. The external runner owns per-node start/stop; this test
owns its two staging processes. The application receipt join is explicitly
offline and trusted: native Store posting precedes exact ACL2 record/request
binding; complete-block bp-node ingress and BPSec are outside this fixture.
"""
import os
from pathlib import Path
import re
import shlex
import time
import unittest

from tests.native_harness import EXIT, environment, native_image, requires, run, start
# The module, not the class: a TestCase imported by name is collected again
# here and its tests run twice under this module's name.
from tests import test_native_ion_workflow as workflow

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(IMAGE)
@unittest.skipUnless(os.environ.get("FN_ION_LAB_RUN"), "exclusive running ION lab required")
class NativeIonLtpTests(unittest.TestCase):
    # RFC 9171 milliseconds; ACL2 projects exactly 60 helper seconds.
    lifetime = "60000"
    setUp = workflow.NativeIonWorkflowTests.setUp
    invoke = workflow.NativeIonWorkflowTests.invoke
    submit = workflow.NativeIonWorkflowTests.submit
    status = workflow.NativeIonWorkflowTests.status
    assert_outstanding = workflow.NativeIonWorkflowTests.assert_outstanding

    def test_real_send_binding_and_committed_application_receipt_return(self):
        lab = Path(os.environ["FN_ION_LAB_RUN"])
        sender = os.environ["FN_LTP_SEND_BIN"]
        stager = os.environ["FN_LTP_STAGE_BIN"]
        stage = self.tmp / "stage"
        stage.mkdir(mode=0o700)
        request_copy = self.tmp / "submitted-request.adu"
        archive_before = self.invoke("store", self.store, "retention")
        self.assertEqual(archive_before.returncode, EXIT.OK, archive_before.stderr)
        self.assertIn("pins=1 ", archive_before.stdout)
        process = start([stager, "ipn:2.1", stage, "35", "1"],
                        env=environment(), cwd=lab / "cfg2")
        self.addCleanup(process.stop)
        time.sleep(2)
        result = self.submit(
            f'cp "$4" {shlex.quote(str(request_copy))}\n'
            f'cd {shlex.quote(str(lab / "cfg1"))}\n'
            f'exec {shlex.quote(sender)} "$@"\n')
        (lab / "native-send.log").write_text(result.stdout + result.stderr)
        self.assertEqual(result.returncode, EXIT.OK, result.stderr)
        self.assertEqual(process.wait(timeout=45), EXIT.OK,
                         result.stdout + process.diagnostics())
        files = list(stage.iterdir())
        self.assertEqual(len(files), 1, process.diagnostics())
        self.assertEqual(request_copy.read_bytes(), files[0].read_bytes())
        source, msec, sequence = files[0].name.split("|")
        reopened = self.status()
        self.assertEqual(reopened.returncode, EXIT.OK, reopened.stderr)
        self.assertIn(f"source={source} msec={msec} sequence={sequence}", reopened.stdout)
        self.assert_outstanding()

        # Offline application join: the receiver commits its own Store record,
        # then ACL2 binds that exact committed record to the received request.
        # This does not substitute for the complete-block bp-node ingress.
        receiver_store = self.tmp / "receiver-store"
        receiver_journal = self.tmp / "receiver-receipts"
        archive = self.tmp / "receiver-export"
        for args in [
            ("store", receiver_store, "init", "fn.test"),
            ("store", receiver_store, "post", self.msgid, self.article,
             "-", "-", "fn.test"),
            ("store", receiver_store, "export", archive),
            ("app-journal", "receipt-init", receiver_store, receiver_journal,
             "dtn://fn-b/", "policy-a", "authority-a"),
        ]:
            completed = self.invoke(*args)
            self.assertEqual(completed.returncode, EXIT.OK, completed.stderr)
        records = list((archive / "records").glob("*.txn"))
        self.assertEqual(len(records), 1)
        completed = self.invoke(
            "app-journal", "receipt-complete", receiver_store, receiver_journal,
            files[0].name, files[0], records[0], "work-a", "receipt-a")
        self.assertEqual(completed.returncode, EXIT.OK, completed.stderr)
        first = self.invoke("app-journal", "receipt-replay", receiver_store,
                            receiver_journal, files[0])
        second = self.invoke("app-journal", "receipt-replay", receiver_store,
                             receiver_journal, files[0])
        self.assertEqual(first.returncode, EXIT.OK, first.stderr)
        self.assertEqual(second.returncode, EXIT.OK, second.stderr)
        self.assertEqual(first.stdout, second.stdout)
        encoded = re.search(r"hex=([0-9a-f]+)", first.stdout)
        self.assertIsNotNone(encoded, first.stdout)
        receipt = self.tmp / "committed-receipt.adu"
        receipt.write_bytes(bytes.fromhex(encoded.group(1)))
        returned = self.tmp / "returned-receipt"
        returned.mkdir(mode=0o700)
        return_process = start([stager, "ipn:1.1", returned, "35", "1"],
                               env=environment(), cwd=lab / "cfg1")
        self.addCleanup(return_process.stop)
        time.sleep(2)
        transport = run([sender, "ipn:2.1", "ipn:1.1", "dtn://fn-a/",
                         receipt, "60", self.observations / "receipt-observation"],
                        env=environment(), cwd=lab / "cfg2", timeout=90, text=True)
        self.assertEqual(transport.returncode, EXIT.OK, transport.stderr)
        self.assertEqual(return_process.wait(timeout=45), EXIT.OK,
                         return_process.diagnostics())
        received = list(returned.iterdir())
        self.assertEqual(len(received), 1)
        self.assertEqual(received[0].read_bytes(), receipt.read_bytes())
        self.assertEqual(
            (self.observations / "receipt-observation").read_text(),
            f"observed-v1|dtn://fn-a/|ipn:1.1|{received[0].name}\n")
        (lab / "returned-receipt-observation").write_bytes(
            (self.observations / "receipt-observation").read_bytes())
        (lab / "committed-receipt.adu").write_bytes(receipt.read_bytes())
        (lab / "receipt-replay.log").write_text(first.stdout)
        # The explicit trusted laboratory profile authorizes application
        # evidence; ION's send observation alone could not release this work.
        released = self.invoke(
            "app-journal", "workflow-receipt", self.store, self.journal,
            received[0], "3", "0", "trusted-local-observation-v0")
        self.assertEqual(released.returncode, EXIT.OK, released.stderr)
        status = self.invoke("app-journal", "workflow-status", self.store,
                             self.journal, "work-a")
        self.assertEqual(status.returncode, EXIT.OK, status.stderr)
        self.assertIn("status=receipted", status.stdout)
        archive_after = self.invoke("store", self.store, "retention")
        self.assertEqual(archive_after.returncode, EXIT.OK, archive_after.stderr)
        self.assertEqual(archive_before.stdout, archive_after.stdout)
        (lab / "application-receipt.log").write_text(first.stdout + released.stdout + status.stdout)
