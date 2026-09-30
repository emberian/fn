"""PKT-392: recording evidence requires a complete actual NEWNEWS answer."""
import unittest

from tests.test_native_peer_pull import NewnewsRecorder


class NewnewsRecorderTests(unittest.TestCase):
    def test_fragmented_listing_is_published_only_after_dot(self):
        recorder = NewnewsRecorder()
        recorder.sent(b"NEWNE")
        recorder.sent(b"WS fn.* 20260929 000000 GMT\r\n")
        recorder.received(b"200 ready\r\n230 list follows\r\n<r@")
        recorder.received(b"example>\r\n")
        self.assertEqual(recorder.answers, [])
        recorder.received(b".\r")
        self.assertEqual(recorder.answers, [])
        recorder.received(b"\n")
        self.assertEqual(recorder.answers, [{
            "command": "NEWNEWS fn.* 20260929 000000 GMT",
            "status": "230 list follows", "message_ids": ["<r@example>"]}])

    def test_article_body_cannot_be_mistaken_for_a_listing(self):
        recorder = NewnewsRecorder()
        recorder.sent(b"ARTICLE <other@example>\r\nNEWNEWS fn.* 20260929 000000 GMT\r\n")
        recorder.received(b"220 article follows\r\n230 forged status\r\n"
                          b"<forged@example>\r\n.\r\n"
                          b"230 list follows\r\n<actual@example>\r\n.\r\n")
        self.assertEqual(len(recorder.answers), 1)
        self.assertEqual(recorder.answers[0]["message_ids"], ["<actual@example>"])

    def test_refusal_and_tls_octets_are_not_listing_evidence(self):
        recorder = NewnewsRecorder()
        recorder.sent(b"NEWNEWS fn.* 20260929 000000 GMT\r\n")
        recorder.received(b"502 denied\r\n")
        self.assertEqual(recorder.answers, [])
        recorder.sent(b"STARTTLS\r\nNEWNEWS fn.* 20260929 000000 GMT\r\n")
        recorder.received(b"382 continue\r\n230 ciphertext-like bytes\r\n<fake>\r\n.\r\n")
        self.assertEqual(recorder.answers, [])


if __name__ == "__main__":
    unittest.main()
