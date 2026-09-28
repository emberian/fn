"""Served articles of millions of lines at a constant control stack (lane
served-line-iterative, 2026-09-26; image-floor's packet 2).

Before this lane the served path took one control-stack frame per article
LINE twice over: books/nntp-post.lisp fn-post-body-octets reassembled a
POST's lines recursively (and a frame per octet of one line), and
books/nntp-session.lisp fn-nntp-stuff-lines built every multi-line reply
the same way.  image-floor measured 144 KiB + 32 octets per line of stack
(planning/evidence/image-floor-2026-09-26.md section 4): an article of
about two million lines exhausted the owner's 64 MiB stack and stopped the
node ("ACL2 error in fn-owner-chunk: Control stack exhausted"), on the POST
and again at every read of it.  Both are loops now
(fn-nntp-stuff-lines-iter-is-stuff-lines,
fn-post-body-octets-iter-is-body-octets).

Each image (production FN_NATIVE_HOST, developer FN_NATIVE_DEVELOPER_HOST)
on one store whose profile admits 8 MiB articles:

1. owner at 1 MiB of control stack per thread (SBCL_USER_ARGS): POST an
   article of 2,000,000 body lines (every sixteenth a lone dot, so the
   reply's dot-stuffing is exercised), ARTICLE and BODY it back; POST an
   article whose body is ONE line of 4 MiB (the article line limit is the
   article bound plus one), ARTICLE it back; stop cleanly;
2. owner at the image's own stack (64 MiB): reopen, ARTICLE both again,
   byte-identical to step 1's replies; POST a second 2,000,000-line article
   and ARTICLE it; stop;
3. owner at 1 MiB again: reopen, ARTICLE the second article, byte-identical
   to step 2's reply; stop.

Every served block is checked against the posted octets exactly: the reply
is the status line, the stored article dot-stuffed (RFC 3977 section
3.1.1), then ".\\r\\n", and the stored article ends with the posted body.
"""
import time
import unittest

from tests import test_native_bounds_join as join
from tests.native_harness import EXIT_OK, native_image, requires

IMAGE = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")

MIB = 1024 * 1024
PROFILE_OCTETS = 8 * MIB
LINES = 2000000
ONE_MIB_STACK = {"SBCL_USER_ARGS": "--control-stack-size 1MB"}


def many_lines(message_id, lines=LINES):
    head = ("From: stack@example.invalid\r\nNewsgroups: fn.test\r\n"
            "Subject: two million lines\r\nMessage-ID: {}\r\n\r\n").format(message_id)
    body = b"".join(b".\r\n" if i % 16 == 0 else b"\r\n" for i in range(lines))
    return head.encode("ascii") + body


def one_line(message_id, octets=4 * MIB):
    head = ("From: stack@example.invalid\r\nNewsgroups: fn.test\r\n"
            "Subject: one line\r\nMessage-ID: {}\r\n\r\n").format(message_id)
    return head.encode("ascii") + b"L" * octets + b"\r\n"


def stuffed(data):
    return b"".join((b"." + ln if ln.startswith(b".") else ln)
                    for ln in data.splitlines(keepends=True))


def raw(client, command):
    """The whole reply to COMMAND, octet for octet, terminator included."""
    status = client.command(command)
    if not status.startswith((b"220", b"222")):
        return status
    out = [status]
    while True:
        ln = client.line()
        out.append(ln)
        if ln == b".\r\n":
            return b"".join(out)


def post(client, data):
    first, final = client.post(data)
    assert first.startswith(b"340"), first
    return final.rstrip(b"\r\n").decode("ascii", "replace")


@requires(IMAGE, DEVELOPER)
class ServedLineStackTests(join.JoinFixture):

    def check_block(self, reply, code, posted_body):
        """REPLY is CODE's status line, a dot-stuffed block and the
        terminator; the block unstuffed ends with POSTED_BODY."""
        status, _, rest = reply.partition(b"\r\n")
        self.assertTrue(status.startswith(code), status[:80])
        self.assertTrue(rest.endswith(b"\r\n.\r\n") or rest == b".\r\n", rest[-16:])
        block = rest[:-3]
        unstuffed = b"".join((ln[1:] if ln.startswith(b".") else ln)
                             for ln in block.splitlines(keepends=True))
        self.assertEqual(block, stuffed(unstuffed), "the block is not exactly dot-stuffed")
        self.assertTrue(unstuffed.endswith(posted_body), "the served article lost octets")
        return unstuffed

    def serve(self, image, env, step):
        started = time.monotonic()
        owner = self.node.start(image=image, env=env)
        with self.node.session(timeout=900) as client:
            out = step(client)
        self.assertIsNone(owner.poll(), "the owner stopped: {}".format(
            owner.stderr.tail(4000).decode("utf-8", "replace")))
        self.node.stop(process=owner)
        print("step", image.name, env, round(time.monotonic() - started, 1), "s", flush=True)
        return out

    def run_image(self, image):
        self.image = image
        created = self.op("init", "--max-article-octets", str(PROFILE_OCTETS), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        a_id, b_id, c_id = ("<lines-a@example.invalid>", "<line-b@example.invalid>",
                            "<lines-c@example.invalid>")
        a, b, c = many_lines(a_id), one_line(b_id), many_lines(c_id)
        body = lambda data: data.split(b"\r\n\r\n", 1)[1]

        def first(client):
            self.assertTrue(post(client, a).startswith("240"))
            art_a = raw(client, "ARTICLE " + a_id)
            self.check_block(art_a, b"220", body(a))
            body_a = raw(client, "BODY " + a_id)
            self.assertEqual(self.check_block(body_a, b"222", body(a)), body(a))
            self.assertEqual(body_a.count(b"\r\n"), 1 + LINES + 1)
            self.assertTrue(post(client, b).startswith("240"))
            art_b = raw(client, "ARTICLE " + b_id)
            self.check_block(art_b, b"220", body(b))
            return art_a, art_b
        art_a, art_b = self.serve(image, ONE_MIB_STACK, first)

        def second(client):
            self.assertEqual(raw(client, "ARTICLE " + a_id), art_a)
            self.assertEqual(raw(client, "ARTICLE " + b_id), art_b)
            self.assertTrue(post(client, c).startswith("240"))
            art_c = raw(client, "ARTICLE " + c_id)
            self.check_block(art_c, b"220", body(c))
            return art_c
        art_c = self.serve(image, None, second)

        def third(client):
            self.assertEqual(raw(client, "ARTICLE " + c_id), art_c)
        self.serve(image, ONE_MIB_STACK, third)

    def test_production_serves_two_million_lines_at_one_mib_of_stack(self):
        self.run_image(IMAGE)

    def test_developer_serves_two_million_lines_at_one_mib_of_stack(self):
        self.run_image(DEVELOPER)


if __name__ == "__main__":
    unittest.main()
