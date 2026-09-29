"""PKT-506: long header fields on a running node (RFC 5322 sections 2.1.1 and
2.2.3; RFC 3977 section 8.3; RFC 2980 section 2.8).

One node, one plain listener, the default profile.  A POST whose Subject is
900 octets and whose References carries 200 Message-IDs (about 9,000 octets)
folded one per line is accepted (240); OVER and XOVER carry both fields whole
(the References field is the unfolded value, section 8.3.2's transformation
and nothing else), HDR Subject and HDR References by Message-ID the same, and
ARTICLE returns the posted octets.  The same References on ONE line is
refused with the line bound's own 441 (a header line longer than 998
octets), and nothing is stored; a Subject line of exactly 998 octets is
accepted and one of 999 refused the same way.

Row I5: a References whose value begins on a continuation line
(`References:` CRLF ` <id>`, RFC 5322 section 2.2.3) is accepted, a bare
`References:` refused as unparsable (RFC 5536 section 2.2: no empty field);
a relayed article (IHAVE, TAKETHIS) with a 999-octet Subject line is refused
by the line bound's name (437 with the text; 439 echoes the Message-ID, RFC
4644 section 2.5), the 998-octet one relayed (books/peer-inbound.lisp
fn-peer-parse-limitp; keystone
fn-peer-decide-transfer-line-length-is-a-long-header-line).

The decisions are ACL2's: books/injection.lisp fn-inj-decide and
fn-inj-parse-refusal (keystone fn-inj-decide-line-length-is-a-long-header-line,
books/article-line-bound.lisp); books/nntp-post.lisp fn-post-refusal-line;
the OVER fields are books/nov-fields.lisp fn-nov-header-content's, served from
the catalog's overview column (books/catalog-record.lisp fn-hnov-of).

Run: FN_NATIVE_HOST=<production launcher> FN_NATIVE_DEVELOPER_HOST=<developer
launcher> python3 -m unittest -v tests.test_native_header_lines
"""

import unittest

from tests.native_harness import EXIT, Client, Node, article, dot_stuff, executable, native_image

IMAGES = [("production", native_image("FN_NATIVE_HOST")),
          ("developer", native_image("FN_NATIVE_DEVELOPER_HOST"))]
IMAGES = [(name, path) for name, path in IMAGES if executable(path)]

LINE_LENGTH = (b"441 posting failed; a header line is longer than 998 octets "
               b"(RFC 5322 section 2.1.1); fold it")
SUBJECT = "s" * 900
IDS = ["<ref{:03d}-{}@example.invalid>".format(i, "x" * 20) for i in range(200)]


def over_fields(line):
    return line.split(b"\t")


class HeaderLineSourceTests(unittest.TestCase):
    def test_the_reply_is_the_tables(self):
        from tests.native_harness import ROOT
        table = (ROOT / "books" / "protocol-table.lisp").read_text(encoding="utf-8")
        self.assertIn(LINE_LENGTH.decode("ascii"), " ".join(table.split()))


@unittest.skipUnless(IMAGES, "a native image (FN_NATIVE_HOST or FN_NATIVE_DEVELOPER_HOST)")
class NativeHeaderLineTests(unittest.TestCase):
    def post(self, client, payload):
        first, final = client.post(payload)
        return final if final is not None else first

    def scenario(self, image):
        node = Node(self, image)
        node.init("fn.test")
        node.start()
        folded = "References: " + "\r\n ".join(IDS)
        one_line = "References: " + " ".join(IDS)
        self.assertGreater(len(one_line), 8000)
        with Client(node.port, timeout=120) as client:
            reply = self.post(client, article("<long@example.invalid>", subject=SUBJECT,
                                              date=None, headers=(folded,)))
            self.assertTrue(reply.startswith(b"240"), reply)
            refused = self.post(client, article("<oneline@example.invalid>", date=None,
                                                headers=(one_line,)))
            self.assertEqual(refused.rstrip(b"\r\n"), LINE_LENGTH)
            self.assertTrue(client.command(b"STAT <oneline@example.invalid>").startswith(b"430"))
            # The boundary: "Subject: " + 989 octets is a 998-octet line.
            edge = self.post(client, article("<edge@example.invalid>", subject="e" * 989,
                                             date=None))
            self.assertTrue(edge.startswith(b"240"), edge)
            over = self.post(client, article("<over@example.invalid>", subject="e" * 990,
                                             date=None))
            self.assertEqual(over.rstrip(b"\r\n"), LINE_LENGTH)

            words = client.command(b"GROUP fn.test").split()
            self.assertEqual(words[0], b"211", words)
            for verb in (b"OVER", b"XOVER"):
                status, block = client.multiline(verb + b" " + words[2] + b"-" + words[3])
                self.assertTrue(status.startswith(b"224"), status)
                rows = [over_fields(row) for row in block.split(b"\r\n") if row]
                row = next(r for r in rows if r[4] == b"<long@example.invalid>")
                self.assertEqual(row[1], SUBJECT.encode("ascii"), verb)
                self.assertEqual(row[5], " ".join(IDS).encode("ascii"), verb)
                edge_row = next(r for r in rows if r[4] == b"<edge@example.invalid>")
                self.assertEqual(len(edge_row[1]), 989, verb)
            status, block = client.multiline(b"OVER <long@example.invalid>")
            self.assertTrue(status.startswith(b"224"), status)
            self.assertEqual(over_fields(block.split(b"\r\n")[0])[5],
                             " ".join(IDS).encode("ascii"))
            for field, value in ((b"Subject", SUBJECT), (b"References", " ".join(IDS))):
                status, block = client.multiline(b"HDR " + field + b" <long@example.invalid>")
                self.assertTrue(status.startswith(b"225"), status)
                self.assertEqual(block.split(b"\r\n")[0],
                                 b"0 " + value.encode("ascii"), field)
            status, block = client.multiline(b"ARTICLE <long@example.invalid>")
            self.assertTrue(status.startswith(b"220"), status)
            self.assertIn(folded.encode("ascii"), block)
            self.assertIn(b"Subject: " + SUBJECT.encode("ascii"), block)
        node.stop()

    def continuation_scenario(self, image):
        node = Node(self, image)
        node.init("fn.test")
        node.operator("peer", "add", "src", "src.example.invalid", "127.0.0.1", "1",
                      "fn.*", "-", "127.0.0.1", "true", expect=EXIT.OK)
        node.start()
        with Client(node.port, timeout=120) as client:
            reply = self.post(client, article("<cont@example.invalid>", date=None,
                                              headers=("References:\r\n <r1@example.invalid>",)))
            self.assertTrue(reply.startswith(b"240"), reply)
            status, block = client.multiline(b"ARTICLE <cont@example.invalid>")
            self.assertTrue(status.startswith(b"220"), status)
            self.assertIn(b"References:\r\n <r1@example.invalid>\r\n", block)
            bare = self.post(client, article("<bare@example.invalid>", date=None,
                                             headers=("References:",)))
            self.assertEqual(bare.rstrip(b"\r\n"),
                             b"441 posting failed; the article is not valid syntax")

            def relayed(message_id, subject, extra=b""):
                return (b"Path: src.example.invalid!not-for-mail\r\n"
                        b"Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
                        b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                        b"Subject: " + subject + b"\r\n" + extra
                        + b"Message-ID: " + message_id + b"\r\n\r\nbody\r\n")
            replies = {}
            for key, message_id, subject, extra, verb in (
                    ("edge", b"<t-edge@example.invalid>", b"e" * 989, b"", b"IHAVE"),
                    ("long", b"<t-long@example.invalid>", b"e" * 990, b"", b"IHAVE"),
                    ("long-stream", b"<t-longs@example.invalid>", b"e" * 990, b"", b"TAKETHIS"),
                    ("cont", b"<t-cont@example.invalid>", b"relayed",
                     b"References:\r\n <r1@example.invalid>\r\n", b"IHAVE")):
                octets = relayed(message_id, subject, extra)
                if verb == b"IHAVE":
                    offer, final = client.post(octets, verb=b"IHAVE " + message_id)
                    self.assertTrue(offer.startswith(b"335"), offer)
                else:
                    client.send(b"TAKETHIS " + message_id + b"\r\n" + dot_stuff(octets) + b".\r\n")
                    final = client.line()
                replies[key] = final.rstrip(b"\r\n")
            print("NATIVE-HEADER-LINES-TRANSIT " + repr(replies))
            self.assertTrue(replies["edge"].startswith(b"235"), replies)
            self.assertTrue(replies["cont"].startswith(b"235"), replies)
            self.assertEqual(replies["long"], b"437 transfer rejected; " + LINE_LENGTH[len(b"441 posting failed; "):],
                             replies)
            self.assertEqual(replies["long-stream"], b"439 <t-longs@example.invalid>", replies)
        node.stop()

    def test_a_field_body_may_begin_on_a_continuation_line_and_transit_names_the_bound(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.continuation_scenario(image)

    def test_long_fields_folded_are_served_whole_and_a_long_line_is_refused_by_name(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.scenario(image)


if __name__ == "__main__":
    unittest.main()
