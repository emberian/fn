"""Consumer-owned SQLite recovery; native answers are opaque fixture bytes.

These tests assert client custody and ACK ordering, not fn cursor semantics.
The matching-image consumer exchange covers the real native boundary.
"""
import json
import importlib.util
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
if os.environ.get("FN_CONSUMER_TEST_SOURCE"):
    spec = importlib.util.spec_from_file_location("fn_consumer", os.environ["FN_CONSUMER_TEST_SOURCE"])
    fn_consumer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fn_consumer)
else:
    import fn_consumer


class DeliveryRecovery(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.config = self.root / "config.json"
        self.config.write_text(json.dumps({
            "image": "unused", "control": "unused", "consumer": "worker",
            "work": str(self.root / "work"), "db": str(self.root / "db")}))
        self.calls = []
        self.code = 4
        self.article_code = 0
        self.article = b"fn-consumer-withdrawn-v1 3c783e\n"
        self.client = self.open_client()
        self.addCleanup(lambda: self.close_client())

    def open_client(self):
        client = fn_consumer.Consumer(self.config)
        client.native = self.native
        return client

    def close_client(self):
        if self.client is not None:
            self.client.db.close()
            os.close(self.client.lock)
            self.client = None

    def native(self, *words):
        self.calls.append(words)
        if words[:2] == ("consumer", "position"):
            Path(words[-1]).write_bytes(b"old-cursor")
        elif words[:2] == ("consumer", "poll"):
            Path(words[-2]).write_bytes(b"next-cursor")
            Path(words[-1]).write_bytes(b"exact-report")
        elif words[0] == "consumer-project":
            self.assertEqual(Path(words[1]).read_bytes(), b"next-cursor")
            self.assertEqual(Path(words[2]).read_bytes(), b"exact-report")
            return self.code, b"projection failed\n", b"native diagnostic\n"
        elif words[0] == "consumer-article":
            return self.article_code, self.article, b""
        return 0, b"", b""

    def test_fault_and_uncertainty_never_ack_or_become_unattributed(self):
        for code in (4, 3):
            with self.subTest(code=code):
                self.code = code
                self.calls.clear()
                with self.assertRaises(fn_consumer.Stop) as stopped:
                    self.client.wake(max_pages=1)
                self.assertEqual(stopped.exception.code, code)
                self.assertFalse(any(c[:2] == ("consumer", "ack") for c in self.calls))
                self.assertEqual(self.client.summary()["unattributed"], 0)

    def test_restart_reuses_exact_delivery_without_polling_then_handles_withdrawal(self):
        with self.assertRaises(fn_consumer.Stop):
            self.client.wake(max_pages=1)
        self.close_client()
        self.client = self.open_client()
        self.code = 1  # A signed projection can refuse an actual withdrawal.
        self.calls.clear()
        self.client.wake(max_pages=1)
        self.assertFalse(any(c[:2] == ("consumer", "poll") for c in self.calls))
        self.assertTrue(any(c[:2] == ("consumer", "ack") for c in self.calls))
        row = self.client.db.execute(
            "SELECT cursor, report, state FROM deliveries").fetchone()
        self.assertEqual(row, (b"next-cursor", b"exact-report", "handled"))

    def test_refused_report_decoder_preserves_delivery_and_refusal(self):
        self.code = 1
        self.article_code = 1
        with self.assertRaises(fn_consumer.Stop) as stopped:
            self.client.wake(max_pages=1)
        self.assertEqual(stopped.exception.code, 1)
        self.assertFalse(any(c[:2] == ("consumer", "ack") for c in self.calls))

    def test_successful_unknown_report_summary_is_fault_not_permission_to_ack(self):
        self.code = 1
        self.article = b"unexpected-output\n"
        with self.assertRaises(fn_consumer.Stop) as stopped:
            self.client.wake(max_pages=1)
        self.assertEqual(stopped.exception.code, 4)
        self.assertFalse(any(c[:2] == ("consumer", "ack") for c in self.calls))

    def test_repeated_committed_report_does_not_construct_another_signed_reply(self):
        self.client.config.update(principal_hex="receiver", claims=[["fn-e1", "r", "sender"]])
        event = dict(history="history", incarnation="incarnation", source_id="source",
                     message_id="<report>", source=b"authored-source", received=b"received",
                     sequence=1, verdict_principal="sender", verdict="verified")
        fields = {"application-id": "fn-e1", "operation-id": "r1", "kind": "report-receipt"}
        self.client.db.execute("INSERT INTO operations VALUES (?,?,?,?,?,?,?)",
                               ("fn-e1", "r1", fn_consumer.digest(event["source"]),
                                "report-receipt", "replied", "sender", None))
        def forbidden(*args):
            self.fail("a committed reply must not read new keys or sign again")
        self.client.reply_for = forbidden
        disposition = self.client.transaction(event, fields, b"next-cursor",
                                              {"own": "verified", "principal": "sender"})
        self.assertEqual(disposition, "repeat")
        self.assertEqual(self.client.summary()["transitions"], [])
        self.assertEqual(self.client.summary()["pending_ack"], "unsent")


if __name__ == "__main__":
    unittest.main()
