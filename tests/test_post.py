"""Raw-socket POST transcripts against the owner (tools/run_owner.py).

Every reply asserted here is octets ACL2 produced: books/nntp.lisp for the
340, books/nntp-post.lisp for the 440/441, books/injection.lisp for the
article that ends up in the store, and books/owner.lisp (fn-own-outcome
through fn-served-post-outcome) for the 240.  Nothing in tools/ writes a
status line.  The owner is the one process that holds the store: it pins a
committed version per connection, serializes durable posts and serves
readers concurrently; the read-only reader answers POST with 440.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tests.test_owner import OwnerProcess, assert_bytes
from tests.test_reader import ROOT, ReaderProcess

GOOD = (b"From: poster@example.invalid\r\nSubject: hello\r\n"
        b"Newsgroups: fn.letters\r\n\r\nHello, news.\r\n")
NO_FROM = b"Subject: hello\r\nNewsgroups: fn.letters\r\n\r\nHello.\r\n"
PY312 = "/opt/homebrew/bin/python3.12"


def terminate(body):
    """Dot-terminate a proto-article for the POST body (RFC 3977 3.1.1)."""
    return body + b".\r\n"


class SeedPostTests(unittest.TestCase):
    """No store behind the reader: the offer and the refusals are still ACL2's."""

    def test_post_is_refused_without_a_configured_writer(self):
        with ReaderProcess() as reader:
            sock = reader.connect()
            self.addCleanup(sock.close)
            sock.sendall(b"POST\r\n")
            reader.assert_bytes(sock, b"440 posting not permitted\r\n")

    def test_post_argument_is_a_syntax_error(self):
        with ReaderProcess() as reader:
            sock = reader.connect()
            self.addCleanup(sock.close)
            sock.sendall(b"POST extra\r\n")
            reader.assert_bytes(sock, b"501 syntax error\r\n")


class StorePostTests(unittest.TestCase):
    """POST served by the owner over a store seeded with one article."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-post-store-")
        self.store = Path(self.temp.name) / "store"
        self.control = Path(self.temp.name) / "owner.sock"
        self.payload = Path(self.temp.name) / "article"
        self.store_command("init")
        seed = (b"Message-ID: <seed@example.invalid>\r\nSubject: seed\r\n"
                b"\r\nSeed body\r\n")
        self.payload.write_bytes(seed)
        self.store_command("post", "--message-id", "<seed@example.invalid>",
                           "--payload", str(self.payload), "--group", "fn.letters")
        self.owner = None

    def tearDown(self):
        if self.owner is not None:
            self.owner.stop()
        self.temp.cleanup()

    def start_owner(self, **kwargs):
        self.owner = OwnerProcess(self.store, self.control, **kwargs).start()
        return self.owner

    def post(self, sock, article, expected):
        sock.sendall(b"POST\r\n")
        assert_bytes(sock, b"340 send article to be posted\r\n")
        sock.sendall(terminate(article))
        assert_bytes(sock, expected)

    @staticmethod
    def read_article(sock):
        body = b""
        while not body.endswith(b"\r\n.\r\n"):
            chunk = sock.recv(4096)
            if not chunk:
                break
            body += chunk
        return body

    def store_command(self, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.store),
             command, *map(str, args)], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode != expected:
            self.fail("store {} returned {}\nstdout={}\nstderr={}".format(
                command, result.returncode, result.stdout, result.stderr))
        return result

    def test_post_reaches_240_and_the_article_can_be_read_back(self):
        owner = self.start_owner()
        sock = owner.connect()
        self.addCleanup(sock.close)
        self.post(sock, GOOD, b"240 article received OK\r\n")
        # Read-back: the 240 re-pinned the poster's own connection to the
        # version that contains its own article (fn-own-outcome's :durable
        # branch is one fn-own-advance on that connection;
        # fn-own-durable-outcome-repins-the-poster), so its next GROUP sees
        # two and its next ARTICLE serves the article it just posted.
        sock.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(sock, b"211 2 1 2 fn.letters\r\n")
        sock.sendall(b"STAT 2\r\n")
        assert_bytes(sock, b"223 2 ")
        sock.recv(4096)
        # A second connection opens at the same version and reads back
        # the article with the fields ACL2 generated.
        second = owner.connect()
        self.addCleanup(second.close)
        second.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(second, b"211 2 1 2 fn.letters\r\n")
        second.sendall(b"ARTICLE 2\r\n")
        body = self.read_article(second)
        self.assertIn(b"Injection-Info: fn.example.invalid\r\n", body)
        self.assertIn(b"Path: fn.example.invalid!not-for-mail\r\n", body)
        self.assertRegex(body, rb"Injection-Date: \w\w\w, \d\d \w\w\w \d{4} "
                               rb"\d\d:\d\d:\d\d \+0000\r\n")
        self.assertIn(b"\r\nHello, news.\r\n", body)
        # The supplied source is a verbatim suffix, as the theorem says.
        self.assertTrue(body.split(b"220 ", 1)[1].split(b"\r\n", 1)[1]
                        .endswith(GOOD + b".\r\n"), body)
        # The store agrees once the owner is gone: two transactions.
        owner.stop()
        self.owner = None
        status = self.store_command("status")
        self.assertIn(b"transactions=2 articles=2", status.stdout)

    def test_a_refused_proto_article_is_441_with_its_reason(self):
        owner = self.start_owner()
        sock = owner.connect()
        self.addCleanup(sock.close)
        self.post(sock, NO_FROM, b"441 posting failed; From is required\r\n")
        # The refusal made nothing durable: a fresh connection sees one.
        second = owner.connect()
        self.addCleanup(second.close)
        second.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(second, b"211 1 1 1 fn.letters\r\n")

    def test_a_group_this_store_does_not_carry_is_441(self):
        owner = self.start_owner()
        sock = owner.connect()
        self.addCleanup(sock.close)
        self.post(sock, b"From: p@e.invalid\r\nSubject: s\r\n"
                        b"Newsgroups: fn.absent\r\n\r\nBody\r\n",
                  b"441 posting failed; a named newsgroup is not carried here\r\n")

    def test_a_duplicate_supplied_message_id_is_the_refused_441(self):
        # The store refuses a Message-ID it already holds; that refusal is
        # the owner's :refused word, rendered by the book as the refusal
        # line, never as 240 and never as the uncertain line.
        owner = self.start_owner()
        sock = owner.connect()
        self.addCleanup(sock.close)
        self.post(sock, b"From: p@e.invalid\r\nSubject: s\r\n"
                        b"Message-ID: <seed@example.invalid>\r\n"
                        b"Newsgroups: fn.letters\r\n\r\nBody\r\n",
                  b"441 posting failed; the article was refused\r\n")

    def test_a_reader_pinned_before_a_post_keeps_its_view(self):
        # Concurrency through one owner: a reader open before the post keeps
        # the version it pinned while the poster gets 240 and a reader
        # opened afterwards sees the article; the pinned reader moves only
        # when the control channel advances it.
        owner = self.start_owner()
        early = owner.connect()
        self.addCleanup(early.close)
        early.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(early, b"211 1 1 1 fn.letters\r\n")
        poster = owner.connect()
        self.addCleanup(poster.close)
        self.post(poster, GOOD, b"240 article received OK\r\n")
        self.assertEqual(owner.control_line(b"VERSION"), b"version 2")
        # The poster's own pin moved with its 240; nobody else's did.
        poster.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(poster, b"211 2 1 2 fn.letters\r\n")
        early.sendall(b"GROUP fn.letters\r\nSTAT 2\r\n")
        assert_bytes(early, b"211 1 1 1 fn.letters\r\n")
        assert_bytes(early, b"423 ")
        early.recv(64)
        late = owner.connect()
        self.addCleanup(late.close)
        late.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(late, b"211 2 1 2 fn.letters\r\n")
        # A second post through the poster while both readers stay put.
        self.post(poster, GOOD.replace(b"hello", b"again"),
                  b"240 article received OK\r\n")
        poster.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(poster, b"211 3 1 3 fn.letters\r\n")
        late.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(late, b"211 2 1 2 fn.letters\r\n")
        self.assertTrue(owner.control_line(b"ADVANCE ALL").startswith(b"advanced "))
        early.sendall(b"GROUP fn.letters\r\n")
        assert_bytes(early, b"211 3 1 3 fn.letters\r\n")

    def test_a_read_only_reader_refuses_posting_with_440(self):
        with ReaderProcess(self.store) as reader:
            sock = reader.connect()
            self.addCleanup(sock.close)
            sock.sendall(b"POST\r\n")
            reader.assert_bytes(sock, b"440 posting not permitted\r\n")

    @unittest.skipUnless(os.path.exists(PY312), "python3.12 is not installed")
    def test_an_independent_nntplib_client_posts_and_reads_back(self):
        probe = Path(__file__).with_name("interop_post_nntplib.py")
        owner = self.start_owner()
        result = subprocess.run([PY312, str(probe), str(owner.port)],
                                cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(b"posted", result.stdout)


if __name__ == "__main__":
    unittest.main()
