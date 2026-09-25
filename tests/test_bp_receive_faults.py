"""Receiver crash-cut tests over the real FNBI, Store, FNRJ, and ACL2 bridges."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

import zlib

from tests.test_bp_receive import lab_bundles
from tools import run_bp_ingress, run_bp_receive, run_store


class _Bundles(dict):
    """One distinct ACL2-built bundle per BID, built when first asked for.

    These tests are about crash cuts, not about identity, so each BID stands
    for its own bundle; the identity is still ACL2's and never the BID.
    """

    def __missing__(self, bid: str) -> bytes:
        value = lab_bundles([dict(sequence=zlib.crc32(bid.encode("ascii")) + 1)])[0]
        self[bid] = value
        return value


class ReceiveFaultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="fn-bp-receive-fault-")
        base = Path(self.temp.name)
        self.store = base / "store"
        self.inbox = base / "inbox"
        self.receipts = base / "receipts"
        run_store.Store(self.store, True).initialize()
        self.inventory: dict[str, bytes] = {}
        self.bundles = _Bundles()
        self.deleted: list[str] = []

    def tearDown(self) -> None:
        self.temp.cleanup()

    @staticmethod
    def article(name: str) -> bytes:
        return (f"Message-ID: <{name}@fn.example>\r\nNewsgroups: fn.letters\r\n\r\n"
                f"body for {name}\r\n").encode("ascii")

    def request(self, name: str, *, destination: bytes = b"dtn://fn.lab/inbox",
                policy: bytes = b"bp-lab-policy-v0", work_id: bytes | None = None) -> bytes:
        article = self.article(name)
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-adu")')
            msgid = bridge.extract_message_id(article)
            _, subject, _ = run_store.metadata(msgid, article)

            def text(value: bytes) -> str:
                return "(fn-store-octets->string '" + bridge.literal(value) + ")"

            fields = [f"work:{name}".encode() if work_id is None else work_id,
                      subject, b"dtn://sender.lab",
                      destination, policy, b"origin:1", b"wire-auth", b"terms:1"]
            form = "(fn-bpa-encode (fn-bpa-make-request " + " ".join(
                text(value) for value in fields) + " '" + bridge.literal(article) + "))"
            return run_store.acl2_octets(bridge.call(form))
        finally:
            bridge.close()

    def receive(self, bid: str, *, delete=None, **kwargs):
        def default_delete(found: str) -> None:
            self.deleted.append(found)
            self.inventory.pop(found)

        return run_bp_receive.receive_bpa_request(
            store_root=self.store, inbox_root=self.inbox, receipt_root=self.receipts,
            bid=bid, source_eid="dtn://sender.lab", inventory=lambda: list(self.inventory),
            download=lambda found: self.inventory[found],
            bundle=lambda found: self.bundles[found],
            delete=default_delete if delete is None else delete, **kwargs)

    def recovered_counts(self) -> tuple[int, int, int]:
        store, bridge, records = run_bp_ingress.open_live_bp_store(self.store, False)
        try:
            return len(records), bridge.article_count(), bridge.pin_count()
        finally:
            bridge.close()
            store.close()

    def test_fnbi_durable_cut_reopens_same_adu_once(self) -> None:
        self.inventory["bid-fnbi"] = self.request("fnbi")
        with mock.patch.object(run_bp_receive.run_bp_ingress, "open_live_bp_store",
                               side_effect=OSError("cut after FNBI")):
            with self.assertRaises(OSError):
                self.receive("bid-fnbi")
        self.assertIn("bid-fnbi", self.inventory)
        self.assertEqual(len(list((self.inbox / "inbound").glob("*.bp"))), 1)
        self.assertEqual(self.deleted, [])

        self.assertEqual(self.receive("bid-fnbi").outcome, "accepted")
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

    def test_article_commit_before_context_reopens_without_second_charge(self) -> None:
        self.inventory["bid-article"] = self.request("article")
        with mock.patch.object(run_bp_receive.ReceiptJournal, "accept_request",
                               side_effect=OSError("cut before context")):
            with self.assertRaises(OSError):
                self.receive("bid-article")
        self.assertIn("bid-article", self.inventory)
        self.assertEqual(self.deleted, [])
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

        self.assertEqual(self.receive("bid-article").outcome, "accepted")
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

    def test_context_before_intent_reopens_without_second_charge(self) -> None:
        self.inventory["bid-context"] = self.request("context")
        with mock.patch.object(run_bp_receive.ReceiptJournal, "prepare_receipt",
                               side_effect=OSError("cut before intent")):
            with self.assertRaises(OSError):
                self.receive("bid-context")
        self.assertIn("bid-context", self.inventory)
        self.assertEqual(self.deleted, [])
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

        self.assertEqual(self.receive("bid-context").outcome, "duplicate")
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

    def test_intent_before_decision_requires_recovery_without_second_charge(self) -> None:
        self.inventory["bid-intent"] = self.request("intent")
        with mock.patch.object(run_bp_receive.ReceiptJournal, "commit_receipt",
                               side_effect=OSError("cut before decision")):
            with self.assertRaises(OSError):
                self.receive("bid-intent")
        self.assertIn("bid-intent", self.inventory)
        self.assertEqual(self.deleted, [])
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

        with self.assertRaises(run_bp_receive.BpReceiveError):
            self.receive("bid-intent")
        recovered = self.receive("bid-intent", pending_outcome="committed")
        self.assertEqual(recovered.outcome, "duplicate")
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

    def test_decision_before_lost_delete_retries_same_adu_without_charge(self) -> None:
        self.inventory["bid-delete"] = self.request("delete")
        with self.assertRaises(run_bp_receive.BpReceiveDeletePending):
            self.receive("bid-delete", delete=lambda found: (_ for _ in ()).throw(
                OSError("BPA delete completion lost")))
        self.assertIn("bid-delete", self.inventory)
        self.assertEqual(self.deleted, [])
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

        self.assertEqual(self.receive("bid-delete").outcome, "duplicate")
        self.assertEqual(self.deleted, ["bid-delete"])
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

    def test_wrong_policy_or_destination_never_publishes_store_record(self) -> None:
        self.inventory["bid-destination"] = self.request(
            "destination", destination=b"dtn://wrong.lab/inbox")
        self.inventory["bid-policy"] = self.request("policy", policy=b"wrong-policy")
        for bid in ("bid-destination", "bid-policy"):
            with self.subTest(bid=bid), self.assertRaises(run_bp_receive.BpReceiveError):
                self.receive(bid)
        self.assertEqual(self.deleted, [])
        self.assertEqual(set(self.inventory), {"bid-destination", "bid-policy"})
        self.assertEqual(self.recovered_counts(), (0, 0, 0))

    def test_capacity_refusal_preserves_prior_article_and_pin(self) -> None:
        self.inventory["bid-prior"] = self.request("prior")
        self.assertEqual(self.receive("bid-prior").outcome, "accepted")
        self.inventory["bid-full"] = self.request("full")
        with mock.patch.object(run_bp_receive.run_store, "conservative_charge",
                               return_value=run_store.profile_config()["capacity"] + 1):
            with self.assertRaises(run_bp_receive.BpReceiveError):
                self.receive("bid-full")
        self.assertIn("bid-full", self.inventory)
        self.assertEqual(self.deleted, ["bid-prior"])
        self.assertEqual(self.recovered_counts(), (1, 1, 1))

    def test_store_at_its_transaction_bound_refuses_and_stays_openable(self) -> None:
        """D1: the 129th request must not publish a store that cannot reopen.

        The configured bound is reduced for the test; what the store's
        reopenability depends on is the guard, not the particular number.
        The refusal precedes any frontier advance or charge.
        """
        bounded = Path(self.temp.name) / "bounded"
        # ACL2's verdict (`fn-sbud-verdict`) is replaced by one that refuses
        # the second publication; the bound itself is certified in ACL2.
        with mock.patch.object(run_store, "publication_admissible",
                               side_effect=[True, False]):
            run_store.Store(bounded, True).initialize()
            self.store = bounded
            self.inventory["bid-at-bound"] = self.request("at-bound")
            self.assertEqual(self.receive("bid-at-bound").outcome, "accepted")
            frontier_before = (bounded / "allocation-frontier.json").read_bytes()

            self.inventory["bid-beyond"] = self.request("beyond")
            refused = self.receive("bid-beyond")
            self.assertEqual(refused.outcome, "refused-capacity")
            self.assertEqual(refused.receipt_adu, b"")
            # The BPA request and its staged frame are retained for an operator.
            self.assertIn("bid-beyond", self.inventory)
            self.assertEqual(self.deleted, ["bid-at-bound"])
            self.assertTrue(refused.staged_path.exists())
            # No transaction was allocated, charged, or published.
            self.assertEqual((bounded / "allocation-frontier.json").read_bytes(),
                             frontier_before)
            self.assertEqual(len(list((bounded / "transactions").iterdir())), 1)
            # The store still opens: that is what the 129th record would break.
            self.assertEqual(self.recovered_counts(), (1, 1, 1))

    def test_unreceiptable_work_id_refuses_before_any_store_mutation(self) -> None:
        """D11: the receipt-id bound is a preflight, not a post-charge error."""
        self.inventory["bid-long"] = self.request(
            "long", work_id=b"w" * (run_bp_receive.MAX_RECEIPT_ID_OCTETS - 7))
        refused = self.receive("bid-long")
        self.assertEqual(refused.outcome, "refused-receipt-id")
        self.assertEqual(refused.receipt_adu, b"")
        self.assertIn("bid-long", self.inventory)
        self.assertEqual(self.deleted, [])
        self.assertEqual(self.recovered_counts(), (0, 0, 0))
        # A retry reaches the same refusal instead of a stuck context.
        self.assertEqual(self.receive("bid-long").outcome, "refused-receipt-id")
        self.assertEqual(self.recovered_counts(), (0, 0, 0))
        # Only the receiver config exists: no context, intent or decision.
        self.assertEqual(len(list((self.receipts / "records").iterdir())), 1)

    def test_a_receiptable_work_id_at_the_bound_is_still_accepted(self) -> None:
        self.inventory["bid-edge"] = self.request(
            "edge", work_id=b"w" * (run_bp_receive.MAX_RECEIPT_ID_OCTETS - 8))
        self.assertEqual(self.receive("bid-edge").outcome, "accepted")
        self.assertEqual(self.recovered_counts(), (1, 1, 1))


if __name__ == "__main__":
    unittest.main()
