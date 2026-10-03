"""Application codec and immutable retry, not fn Store semantics."""
import unittest
from unittest import mock

from tests import test_fn_consumer_delivery as delivery
fn_consumer = delivery.fn_consumer


class OpaqueEnvelope(unittest.TestCase):
    setUp = delivery.DeliveryRecovery.setUp
    open_client = delivery.DeliveryRecovery.open_client
    close_client = delivery.DeliveryRecovery.close_client
    native = delivery.DeliveryRecovery.native
    def test_opaque_payload_has_one_metadata_region(self):
        self.client.config.update(group="fn.test", **{"from": "sender@example.invalid"})
        for payload in (b"", b"simple", b"\x00\xff\r\nkind: reply\r\noperation-id: attacker", "λ\nline".encode(), bytes(range(256)) * 3):
            with self.subTest(payload=payload):
                source = self.client.compose("<r1>", "report", [("application-id", "fn-e1"),
                    ("operation-id", "r1"), ("kind", "report-receipt"), ("payload", payload)])
                decoded = self.client.envelope(source)
                self.assertEqual((decoded["operation-id"], decoded["kind"], decoded["payload"]),
                    ("r1", "report-receipt", payload))
                self.assertIn(fn_consumer.APP_MAGIC_V2, source)
                self.assertTrue(all(len(line) <= 76 for line in source.split(b"\r\n\r\n", 2)[2].split(b"\r\n")))
                for corrupt in (source + b"kind: reply\r\n", source.replace(b"payload-length: " + str(len(payload)).encode(), b"payload-length: 999"),
                    source.replace(b"payload-encoding: base64", b"payload-encoding: unknown"),
                    source.replace(b"kind: report-receipt", b"kind: report-receipt\r\nkind: reply"),
                    source.replace(b"kind: report-receipt", b"kind: unsupported"),
                    source.replace(b"operation-id: r1", b"operation-id: "),
                    source.replace(b"operation-id: r1", b"operation-id: r1\x00")):
                    self.assertIsNone(self.client.envelope(corrupt))

    def test_legacy_saved_artifact_retry_never_reencodes_or_signs(self):
        self.client.config.update(application_id="fn-e1")
        legacy = b"From: sender\r\n\r\nfn-app: e1/1\r\napplication-id: fn-e1\r\noperation-id: r1\r\nkind: report-receipt\r\npayload: old payload\r\n"
        artifact = ("fn-e1", "r1", "<r1>", legacy, b"ed", b"ml", "sender", b"edpub", b"mlpub", "1", "{}")
        sid = self.client.insert_submission(artifact)
        self.client.db.execute("INSERT INTO operations VALUES (?,?,?,?,?,?,?)", ("fn-e1", "r1", fn_consumer.digest(legacy), "originated", "awaiting-reply", "sender", sid))
        with mock.patch.object(self.client, "artifact", side_effect=AssertionError("must not sign")):
            self.client.originate("r1", b"old payload")
            with self.assertRaises(fn_consumer.Stop) as stopped:
                self.client.originate("r1", b"changed")
            self.assertEqual(stopped.exception.code, 1)
        self.assertEqual(self.client.db.execute("SELECT source FROM submissions").fetchone()[0], legacy)

    def test_originated_payload_export_detects_missing_evidence(self):
        self.client.config.update(application_id="fn-e1", group="fn.test", **{"from": "sender@example.invalid"})
        source = self.client.compose("<r1>", "report", [("application-id", "fn-e1"), ("operation-id", "r1"), ("kind", "report-receipt"), ("payload", b"\x00\xff\nreceipt")])
        sid = self.client.insert_submission(("fn-e1", "r1", "<r1>", source, b"ed", b"ml", "sender", b"edpub", b"mlpub", "1", "{}"))
        self.client.db.execute("INSERT INTO operations VALUES (?,?,?,?,?,?,?)", ("fn-e1", "r1", fn_consumer.digest(source), "originated", "awaiting-reply", "sender", sid))
        self.assertEqual(self.client.payload("r1"), b"\x00\xff\nreceipt")
        with self.assertRaises(fn_consumer.Stop) as missing:
            self.client.payload("unrecorded")
        self.assertEqual(missing.exception.code, 1)
        self.client.db.execute("UPDATE operations SET source_sha256='corrupted' WHERE operation_id='r1'")
        with self.assertRaises(fn_consumer.Stop) as corrupt:
            self.client.payload("r1")
        self.assertEqual(corrupt.exception.code, 4)

    def test_received_payload_export_uses_committed_source_not_later_conflict(self):
        self.client.config.update(application_id="fn-e1", group="fn.test", principal_hex="sender", claims=[["fn-e1", "r", "sender"]], **{"from": "sender@example.invalid"})
        for sequence, payload in ((1, b"first\x00\xff"), (2, b"changed\r\nkind: reply")):
            source = self.client.compose("<r1>", "report", [("application-id", "fn-e1"), ("operation-id", "r1"), ("kind", "report-receipt"), ("payload", payload)])
            event = dict(history="history", incarnation="incarnation", source_id=str(sequence), message_id="<r1>", source=source, received=source, sequence=sequence, verdict_principal="sender", verdict="verified")
            outcome = self.client.transaction(event, self.client.envelope(source), str(sequence).encode(), {"own": "verified", "principal": "sender"})
            self.assertEqual(outcome, "applied" if sequence == 1 else "conflict")
        self.assertEqual(self.client.payload("r1"), b"first\x00\xff")
        self.assertEqual(self.client.summary()["transitions"], [["fn-e1", "r1"]])
        self.assertEqual([row["disposition"] for row in self.client.summary()["inbox"]], ["applied", "conflict"])

    def test_reply_preserves_opaque_payload_and_source_dependency(self):
        self.client.config.update(group="fn.test", **{"from": "sender@example.invalid"})
        with mock.patch.object(self.client, "artifact", side_effect=lambda a, o, m, s: s):
            source = self.client.reply_for({"application-id": "fn-e1", "operation-id": "r1", "payload": b"\x00\r\nkind: reply"}, {"source": b"exact signed report"})
        fields = self.client.envelope(source)
        self.assertEqual(fields["payload"], b"received \x00\r\nkind: reply")
        self.assertEqual(fields["dependency"], fn_consumer.digest(b"exact signed report"))


if __name__ == "__main__":
    unittest.main()
