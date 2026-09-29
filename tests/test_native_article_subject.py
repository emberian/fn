"""PRF-1058: two real transit receptions share a relay-v1 subject while
retaining their distinct stored-byte commitments. The harness invokes the
runner's declared immutable image coordinate; changed protected bytes remain
observable outside-in as different served bodies."""
import re
import time
import unittest
from tests.native_harness import (EXIT, Client, Node, free_port, native_image, requires, scratch)

IMAGE = native_image("FN_NATIVE_HOST", "build/fn-host-developer")

@requires(IMAGE)
class NativeArticleSubjectTests(unittest.TestCase):
    def test_relay_variants_keep_one_article_subject_and_distinct_bytes(self):
        root = scratch(self, "fn-native-article-subject-")
        nodes = []
        msgid = "<one-article@relay.invalid>"
        protected = (b"From: a@example.invalid\r\nSubject: exact protected\r\n"
                     b" folded continuation\r\nNewsgroups: fn.test\r\n"
                     b"Message-ID: <one-article@relay.invalid>\r\n\r\n"
                     b"body\r\nPath: body text is protected\r\n")
        for name in ("a", "b"):
            node = Node(self, IMAGE, root=root / name, name=name)
            node.log = node.root / "service.log"
            node.write_config(extra='[log]\npath = "{}"\n'.format(node.log))
            node.store("init", "fn.test", expect=EXIT.OK)
            node.operator("peer", "add", "upstream", "upstream.invalid", "127.0.0.1",
                          str(free_port()), "fn.*", "-", "127.0.0.1", "true", expect=EXIT.OK)
            nodes.append(node)
        try:
            for node in nodes:
                node.start()
            variants = (b"Path: first!not-for-mail\r\nXref: first fn.test:3\r\n" + protected,
                        b"pAtH: second!not-for-mail\r\n"
                        b"XREF: second fn.test:9\r\n\tfolded-xref\r\n" + protected)
            for node, wire in zip(nodes, variants):
                with Client(node.port, timeout=30, greeting=(b"200",)) as client:
                    offer, reply = client.post(wire, verb="IHAVE " + msgid)
                    self.assertTrue(offer.startswith(b"335 "), offer)
                    self.assertTrue(reply.startswith(b"235 "), reply)
                    status, served = client.multiline("ARTICLE " + msgid)
                    self.assertTrue(status.startswith(b"220 "), status)
                    self.assertIn(b"body\r\nPath: body text is protected\r\n", served)
            lines = []
            for node in nodes:
                deadline = time.monotonic() + 15
                while True:
                    text = node.log.read_text() if node.log.exists() else ""
                    matches = [line for line in text.splitlines()
                               if " transit " in line and "message-id=" + msgid + " " in line]
                    if matches or time.monotonic() >= deadline:
                        break
                    time.sleep(0.05)
                self.assertEqual(len(matches), 1, text)
                self.assertIn(" code=235 ", matches[0])
                lines.append(matches[0])
            def field(line, name):
                match = re.search(r"(?:^| )" + name + r"=([0-9a-f]+)(?: |$)", line)
                self.assertIsNotNone(match, line)
                return match.group(1)
            subjects = [field(line, "article-subject") for line in lines]
            commitments = [field(line, "bytes-subject") for line in lines]
            self.assertEqual(subjects[0], subjects[1])
            self.assertNotEqual(commitments[0], commitments[1])
            self.assertTrue(subjects[0].startswith(b"fn/article-subject/v1".hex()))
            for commitment in commitments:
                self.assertTrue(commitment.startswith(b"fn/subject/v1".hex()))
            print("NATIVE-ARTICLE-SUBJECT-WITNESS", subjects, commitments, flush=True)
        finally:
            for node in nodes:
                node.stop()
