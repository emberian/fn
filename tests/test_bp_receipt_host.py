"""Live ACL2 receiver decision around an actual temporary Store publication."""
import tempfile
import unittest
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_bp_ingress  # noqa: E402
import run_store  # noqa: E402


class BpReceiptHostTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-bpr-host-")
        self.store_root = Path(self.temp.name) / "store"
        run_store.Store(self.store_root, writable=True).initialize()
        self.article = (b"Message-ID: <receipt-host@fn.example>\r\n"
                        b"Newsgroups: fn.letters\r\n\r\nReceipt host body\r\n")
        self.destination = b"dtn://fn.lab/inbox"
        self.source = b"dtn://sender.lab"
        self.bid = b"receiver-local-bid"

    def tearDown(self):
        self.temp.cleanup()

    @staticmethod
    def text_form(value):
        return "(fn-store-octets->string '" + run_store.Acl2Store.literal(value) + ")"

    @staticmethod
    def symbol(bridge, form):
        return run_store.acl2_result(bridge.call(form)).decode("ascii").lower()[1:]

    def request_adu(self, bridge, subject):
        fields = [b"work-host-1", subject, self.source, self.destination,
                  b"bp-lab-policy-v0", b"sender-inc-1", b"wire-context", b"terms-1"]
        form = "(fn-bpa-encode (fn-bpa-make-request "
        form += " ".join(self.text_form(field) for field in fields)
        form += " '" + bridge.literal(self.article) + "))"
        return run_store.acl2_octets(bridge.call(form))

    def test_actual_store_acceptance_precedes_acl2_receipt_decision(self):
        store, bridge, records = run_bp_ingress.open_live_bp_store(self.store_root, writable=True)
        try:
            msgid = bridge.extract_message_id(self.article)
            archive, subject, evidence = run_store.metadata(msgid, self.article)
            store.advance_frontier(bridge, bridge.next_txid())
            self.assertEqual(bridge.ingress_prepare(
                self.destination, self.source, self.bid, 300, archive, subject,
                evidence, run_store.conservative_charge(self.article), self.article), "prepared")
            record = bridge.pending_record()
            self.assertEqual(store.publish(bridge, len(records), record), "durable")
            store.fenced = True
            self.assertEqual(store.finish(bridge), "durable")
            bridge.call('(ld "host/bp-receipt-host.lisp" :ld-error-action :return :ld-error-triples t)')
            config = "(fn-bpr-make-config {} {} {})".format(
                self.text_form(self.destination), self.text_form(b"bp-lab-policy-v0"),
                self.text_form(b"dtn://fn.lab/issuer"))
            self.assertEqual(self.symbol(bridge, "(fn-bpr-host-reset {} state)".format(config)), "ready")
            request = self.request_adu(bridge, subject)
            self.assertEqual(self.symbol(bridge, "(fn-bpr-host-accept '" + bridge.literal(request) + " t state)"), "accepted")
            self.assertEqual(self.symbol(bridge, "(fn-bpr-host-prepare-receipt \"work-host-1\" \"receipt-host-1\" nil state)"), "refused")
            self.assertEqual(self.symbol(bridge, "(fn-bpr-host-prepare-receipt \"work-host-1\" \"receipt-host-1\" t state)"), "pending")
            self.assertEqual(run_store.acl2_octets(
                bridge.call("(fn-bpr-host-receipt-adu '" + bridge.literal(request) + " state)")), b"")
            self.assertEqual(self.symbol(bridge, "(fn-bpr-host-commit-receipt \"work-host-1\" \"receipt-host-1\" :committed state)"), "committed")
            receipt = run_store.acl2_octets(
                bridge.call("(fn-bpr-host-receipt-adu '" + bridge.literal(request) + " state)"))
            decoded = bridge.call("(fn-bpa-decode-exact '" + bridge.literal(receipt) + ")")
            self.assertIn(b":OK", run_store.acl2_result(decoded).upper())
            self.assertEqual(bridge.article_count(), 1)
        finally:
            bridge.close()
            store.close()


if __name__ == "__main__":
    unittest.main()
