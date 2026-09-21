"""Native FNWF handler: real Store binding, restart replay, and EIO cuts."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tools import run_store


ROOT = Path(__file__).resolve().parent.parent


class NativeApplicationJournalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.image = ROOT / "build" / "fn-host-dtn"
        if not os.access(cls.image, os.X_OK):
            raise unittest.SkipTest(
                f"DTN native image missing: {cls.image} "
                "(FN_NATIVE_BUILD=host/native/build-dtn.lisp "
                "tools/build_native_host.sh)"
            )

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-native-app-journal-"))
        self.store = self.tmp / "store"
        self.payload = self.tmp / "payload"
        self.msgid = "<native-workflow@example.invalid>"
        self.payload.write_bytes(
            (f"Message-ID: {self.msgid}\r\nNewsgroups: fn.test\r\n\r\n"
             "native workflow application payload\r\n").encode("ascii")
        )
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        initialized = self.invoke("store", self.store, "init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr)
        posted = self.invoke(
            "store", self.store, "post", self.msgid, self.payload,
            "-", "-", "fn.test",
        )
        self.assertEqual(posted.returncode, 0, posted.stderr)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def invoke(self, *args, env=None):
        return subprocess.run(
            [str(self.image), "--fn", *map(str, args)],
            cwd=ROOT,
            env=env or self.env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
            text=True,
        )

    def initialize_workflow(self, journal):
        result = self.invoke(
            "app-journal", "workflow-init", self.store, journal,
            "dtn://fn-a/", "dtn://fn-b/", "policy-a", "authority-a",
            "3600000", "incarnation-a", "authorization-a",
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def enqueue(self, journal, env=None):
        return self.invoke(
            "app-journal", "workflow-enqueue", self.store, journal,
            "1", "0", "work-a", self.msgid, "forward-a",
            "dtn://fn-b/", "policy-a", "terms-a", env=env,
        )

    def status(self, journal):
        return self.invoke(
            "app-journal", "workflow-status", self.store, journal, "work-a"
        )

    def records(self, journal):
        return sorted((journal / "records").glob("*.wf"))

    def test_bound_enqueue_survives_process_restart(self):
        journal = self.tmp / "workflow"
        self.initialize_workflow(journal)
        accepted = self.enqueue(journal)
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn("status=outstanding", accepted.stdout)
        self.assertEqual(len(self.records(journal)), 3)

        reopened = self.status(journal)
        self.assertEqual(reopened.returncode, 0, reopened.stderr)
        self.assertIn("status=outstanding", reopened.stdout)

    def test_stage_eio_is_refused_before_namespace_attempt(self):
        journal = self.tmp / "stage-eio"
        self.initialize_workflow(journal)
        injected = dict(self.env)
        injected["FN_APP_JOURNAL_TEST_FAIL"] = "stage"
        cut = self.enqueue(journal, env=injected)
        self.assertEqual(cut.returncode, 1, cut.stderr)
        self.assertEqual(len(self.records(journal)), 1)

        reopened = self.status(journal)
        self.assertEqual(reopened.returncode, 0, reopened.stderr)
        self.assertIn("status=absent", reopened.stdout)

    def test_locked_but_fenced_store_cannot_publish(self):
        journal = self.tmp / "store-fenced"
        self.initialize_workflow(journal)
        injected = dict(self.env)
        injected["FN_APP_JOURNAL_TEST_FENCE_STORE"] = "before-publish"
        cut = self.enqueue(journal, env=injected)
        self.assertEqual(cut.returncode, 3, cut.stderr)
        self.assertIn("Store is fenced", cut.stderr)
        self.assertEqual(
            len(self.records(journal)), 1,
            "the held Store lock must not authorize publication while fenced",
        )

        reopened = self.status(journal)
        self.assertEqual(reopened.returncode, 0, reopened.stderr)
        self.assertIn("status=absent", reopened.stdout)

    def test_publication_observer_sees_reported_acl2_state(self):
        journal = self.tmp / "observer-order"
        self.initialize_workflow(journal)
        injected = dict(self.env)
        injected["FN_APP_JOURNAL_TEST_OBSERVER"] = "assert-reported"
        accepted = self.enqueue(journal, env=injected)
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn("status=outstanding", accepted.stdout)
        self.assertEqual(len(self.records(journal)), 3)

    def test_namespace_eio_is_uncertain_despite_visible_final(self):
        journal = self.tmp / "namespace-eio"
        self.initialize_workflow(journal)
        injected = dict(self.env)
        injected["FN_APP_JOURNAL_TEST_FAIL"] = "namespace"
        cut = self.enqueue(journal, env=injected)
        self.assertEqual(cut.returncode, 3, cut.stderr)
        self.assertIn("publication is uncertain", cut.stderr)
        self.assertEqual(
            len(self.records(journal)), 2,
            "the intent link is visible but its failed barrier cannot authorize outcome",
        )

        reopened = self.status(journal)
        self.assertEqual(reopened.returncode, 0, reopened.stderr)
        self.assertIn("status=absent", reopened.stdout)
        retry = self.enqueue(journal)
        self.assertNotEqual(retry.returncode, 0)
        self.assertEqual(len(self.records(journal)), 2)

    @staticmethod
    def text_form(value):
        return "(fn-store-octets->string '(" + " ".join(map(str, value)) + "))"

    def test_receiver_request_receipt_intent_and_restart_regeneration(self):
        # Python is setup/oracle only: it asks ACL2 for a canonical request
        # ADU.  The operation under test and every durable record are native.
        article = self.payload.read_bytes()
        bridge = run_store.Acl2Store()
        try:
            msgid = self.msgid.encode("ascii")
            _archive, subject, _evidence = run_store.metadata(msgid, article, bridge)
            transaction = next((self.store / "transactions").glob("*.txn"))
            record = run_store.unframe(transaction.read_bytes(), bridge)
            bridge.call(
                '(ld "host/bp-receipt-journal-host.lisp" '
                ':ld-error-action :return :ld-error-triples t)'
            )
            fields = [
                b"work-a", subject, b"dtn://fn-a/", b"dtn://fn.lab/inbox",
                b"policy-a", b"incarnation-a", b"authorization-a", b"terms-a",
            ]
            form = "(fn-bpa-encode (fn-bpa-make-request "
            form += " ".join(self.text_form(field) for field in fields)
            form += " '(" + " ".join(map(str, article)) + ")))"
            request = run_store.acl2_octets(bridge.call(form))
        finally:
            bridge.close()

        request_path = self.tmp / "request.adu"
        record_path = self.tmp / "store.record"
        request_path.write_bytes(request)
        record_path.write_bytes(record)
        journal = self.tmp / "receipt"
        initialized = self.invoke(
            "app-journal", "receipt-init", self.store, journal,
            "dtn://fn.lab/inbox", "policy-a", "dtn://issuer/",
        )
        self.assertEqual(initialized.returncode, 0, initialized.stderr)
        completed = self.invoke(
            "app-journal", "receipt-complete", self.store, journal,
            "bid-a", request_path, record_path, "work-a", "receipt-a",
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("octets=", completed.stdout)
        self.assertEqual(len(list((journal / "records").glob("*.rj"))), 4)

        first = self.invoke(
            "app-journal", "receipt-replay", self.store, journal, request_path
        )
        second = self.invoke(
            "app-journal", "receipt-replay", self.store, journal, request_path
        )
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertEqual(first.stdout, second.stdout)
        self.assertRegex(first.stdout, r"octets=[1-9][0-9]* hex=[0-9a-f]+")


if __name__ == "__main__":
    unittest.main()
