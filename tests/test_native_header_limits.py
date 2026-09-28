"""The header limits are the store profile's (PRF-230, STO-030, SCN-156).

A store initialised with max-header-fields 1000 accepts a 900-field POST
(and serves it back) and a 1,000-field one, and refuses a 1,001-field one
with the 441 line naming the profile field; the default profile admits 64
fields and refuses the 65th, and 900, by the same name, and a header of 258
physical lines by the lines limit's name.  The ACL2 side is
books/article-header-limits.lisp (fn-article-census-refusal-is-the-parse)
and books/injection.lisp (fn-inj-decide); this is the measurement that the
image wires the opened profile's limits into the served POST.
"""
import os
import unittest

from tests.native_harness import EXIT, Node, dot_stuff, executable, native_image

# The image under test: FN_NATIVE_HOST, else the developer image.
IMAGE = (native_image("FN_NATIVE_HOST") if os.environ.get("FN_NATIVE_HOST")
         else native_image("FN_NATIVE_DEVELOPER_HOST"))
SKIP_REASON = ("no native image at {}: build one with tools/build_native_host.sh "
               "(FN_NATIVE_PROFILE=developer) or name one with FN_NATIVE_HOST or "
               "FN_NATIVE_DEVELOPER_HOST".format(IMAGE))


FIELDS_LINE = (b"441 posting failed; the header has more fields than the "
               b"profile's max-header-fields")


def article(total_fields, message_id):
    """An article of exactly TOTAL_FIELDS header fields (the four mandatory
    ones and TOTAL_FIELDS - 4 distinct X- fields)."""
    lines = [b"From: author@example.invalid", b"Newsgroups: fn.test",
             b"Subject: header limits",
             b"Message-ID: " + message_id.encode("ascii")]
    lines += [b"X-Field-%04d: value %d" % (i, i) for i in range(total_fields - 4)]
    return b"\r\n".join(lines) + b"\r\n\r\nbody\r\n"


@unittest.skipUnless(executable(IMAGE), SKIP_REASON)
class NativeHeaderLimitsTests(unittest.TestCase):
    """PRF-230, STO-030, SCN-156: the header limits are the profile's."""

    def setUp(self):
        self.node = Node(self, IMAGE)

    def init(self, *flags):
        self.node.store("init", *flags, "fn.test", expect=EXIT.OK)

    def start(self):
        self.node.start()

    def post(self, octets, message_id):
        """POST OCTETS; return the reply and, on 240, the ARTICLE text."""
        with self.node.session(timeout=120) as client:
            first, reply = client.post(octets)
            self.assertTrue(first.startswith(b"340"), first)
            reply = reply.rstrip(b"\r\n")
            served = b""
            if reply.startswith(b"240"):
                served = client.article(message_id)
                self.assertIsNotNone(served)
            return reply, served

    def test_a_raised_profile_accepts_900_fields_and_refuses_1001_by_name(self):
        self.init("--max-header-fields", "1000", "--max-header-lines", "2000",
                  "--max-header-octets", "1048576")
        self.start()
        reply, served = self.post(article(900, "<f900@example.invalid>"),
                                  "<f900@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        header = served.split(b"\r\n\r\n", 1)[0]
        self.assertEqual(sum(1 for line in header.split(b"\r\n")
                             if line.startswith(b"X-Field-")), 896)
        reply, _ = self.post(article(1000, "<f1000@example.invalid>"),
                             "<f1000@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        reply, _ = self.post(article(1001, "<f1001@example.invalid>"),
                             "<f1001@example.invalid>")
        self.assertEqual(reply, FIELDS_LINE)

    def test_the_default_profile_is_unchanged(self):
        self.init()
        self.start()
        reply, _ = self.post(article(64, "<f64@example.invalid>"),
                             "<f64@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        for total in (65, 900):
            reply, _ = self.post(article(total, "<f%d@example.invalid>" % total),
                                 "<f%d@example.invalid>" % total)
            self.assertEqual(reply, FIELDS_LINE, total)
        # 257 physical lines (one field folded 256 times): the line limit.
        folded = (b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                  b"Subject: folded\r\nMessage-ID: <folded@example.invalid>\r\n"
                  b"X-Folded: x\r\n" + b"\tx\r\n" * 253 + b"\r\nbody\r\n")
        reply, _ = self.post(folded, "<folded@example.invalid>")
        self.assertEqual(reply, b"441 posting failed; the header has more lines "
                                b"than the profile's max-header-lines")

    def transit_article(self, total_fields, message_id):
        """A relayed article of TOTAL_FIELDS header fields: Path, Date and
        the four of `article', and TOTAL_FIELDS - 6 X- fields."""
        return (b"Path: src.example.invalid!not-for-mail\r\n"
                b"Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n"
                + article(total_fields - 2, message_id))

    def test_peer_transit_is_refused_past_the_profile_limits_by_name(self):
        """PKT-660: IHAVE and TAKETHIS receive the profile's limits as POST
        does (books/transit-header-limits.lisp): the default profile's 64
        fields are relayed, the 65th is refused 437 (by name) / 439."""
        self.init()
        self.node.operator("peer", "add", "src", "src.example.invalid", "127.0.0.1", "1",
                           "fn.*", "-", "127.0.0.1", "true", expect=EXIT.OK)
        self.start()
        replies = {}
        with self.node.session(timeout=120) as client:
            for total, verb in ((64, "IHAVE"), (65, "IHAVE"), (65, "TAKETHIS")):
                message_id = "<t%d-%s@example.invalid>" % (total, verb.lower())
                octets = self.transit_article(total, message_id)
                if verb == "IHAVE":
                    offer, final = client.post(octets, verb=b"IHAVE " + message_id.encode("ascii"))
                    self.assertTrue(offer.startswith(b"335"), offer)
                else:
                    client.send(b"TAKETHIS " + message_id.encode("ascii") + b"\r\n"
                                + dot_stuff(octets) + b".\r\n")
                    final = client.line()
                replies[(total, verb)] = final.rstrip(b"\r\n")
        print("NATIVE-HEADER-LIMITS-TRANSIT " + repr(replies))
        self.assertTrue(replies[(64, "IHAVE")].startswith(b"235"), replies)
        # 437 carries the reason text; 439 echoes the Message-ID only
        # (RFC 4644 section 2.5).
        self.assertEqual(replies[(65, "IHAVE")],
                         b"437 transfer rejected; the header has more fields "
                         b"than the profile's max-header-fields", replies)
        self.assertEqual(replies[(65, "TAKETHIS")],
                         b"439 <t65-takethis@example.invalid>", replies)


if __name__ == "__main__":
    unittest.main()
