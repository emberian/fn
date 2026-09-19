"""Raw-socket POST transcripts against the experimental ACL2 reader.

Every reply asserted here is octets ACL2 produced: books/nntp.lisp for the
340, books/nntp-post.lisp for the 440/441/240, and books/injection.lisp for
the article that ends up in the store.  Nothing in tools/ writes a status
line.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

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


class PostingReaderProcess(ReaderProcess):
    """A reader that also holds the writer path; see tools/run_reader.py."""

    def command(self):
        command = [sys.executable, "tools/run_reader.py", "--port", "0", "--post"]
        if self.store is not None:
            command.extend(["--store", str(self.store)])
        return command


class StorePostTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-post-store-")
        self.store = Path(self.temp.name) / "store"
        self.payload = Path(self.temp.name) / "article"
        self.store_command("init")
        seed = (b"Message-ID: <seed@example.invalid>\r\nSubject: seed\r\n"
                b"\r\nSeed body\r\n")
        self.payload.write_bytes(seed)
        self.store_command("post", "--message-id", "<seed@example.invalid>",
                           "--payload", str(self.payload), "--group", "fn.letters")

    def tearDown(self):
        self.temp.cleanup()

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
        with PostingReaderProcess(self.store) as reader:
            sock = reader.connect()
            self.addCleanup(sock.close)
            sock.sendall(b"POST\r\n")
            reader.assert_bytes(sock, b"340 send article to be posted\r\n")
            sock.sendall(terminate(GOOD))
            reader.assert_bytes(sock, b"240 article received OK\r\n")

            # The posted article is now in the served projection, and what
            # comes back carries the fields ACL2 generated.
            sock.sendall(b"GROUP fn.letters\r\n")
            reply = sock.recv(512)
            self.assertTrue(reply.startswith(b"211 2 1 2 fn.letters\r\n"), reply)
            sock.sendall(b"ARTICLE 2\r\n")
            body = b""
            while not body.endswith(b"\r\n.\r\n"):
                chunk = sock.recv(4096)
                if not chunk:
                    break
                body += chunk
            self.assertIn(b"Injection-Info: fn.example.invalid\r\n", body)
            self.assertIn(b"Path: fn.example.invalid!not-for-mail\r\n", body)
            self.assertRegex(body, rb"Injection-Date: \w\w\w, \d\d \w\w\w \d{4} "
                                   rb"\d\d:\d\d:\d\d \+0000\r\n")
            self.assertIn(b"\r\nHello, news.\r\n", body)
            # The supplied source is a verbatim suffix, as the theorem says.
            self.assertTrue(body.split(b"220 ", 1)[1].split(b"\r\n", 1)[1]
                            .endswith(GOOD + b".\r\n"), body)

    def test_a_refused_proto_article_is_441_with_its_reason(self):
        with PostingReaderProcess(self.store) as reader:
            sock = reader.connect()
            self.addCleanup(sock.close)
            sock.sendall(b"POST\r\n")
            reader.assert_bytes(sock, b"340 send article to be posted\r\n")
            sock.sendall(terminate(NO_FROM))
            reader.assert_bytes(
                sock, b"441 posting failed; From is required\r\n")

    def test_a_group_this_store_does_not_carry_is_441(self):
        with PostingReaderProcess(self.store) as reader:
            sock = reader.connect()
            self.addCleanup(sock.close)
            sock.sendall(b"POST\r\n")
            reader.assert_bytes(sock, b"340 send article to be posted\r\n")
            sock.sendall(terminate(
                b"From: p@e.invalid\r\nSubject: s\r\n"
                b"Newsgroups: fn.absent\r\n\r\nBody\r\n"))
            reader.assert_bytes(
                sock,
                b"441 posting failed; a named newsgroup is not carried here\r\n")

    def test_a_read_only_reader_refuses_posting_with_440(self):
        with ReaderProcess(self.store) as reader:
            sock = reader.connect()
            self.addCleanup(sock.close)
            sock.sendall(b"POST\r\n")
            reader.assert_bytes(sock, b"440 posting not permitted\r\n")

    @unittest.skipUnless(os.path.exists(PY312), "python3.12 is not installed")
    def test_an_independent_nntplib_client_posts_and_reads_back(self):
        probe = Path(__file__).with_name("interop_post_nntplib.py")
        with PostingReaderProcess(self.store) as reader:
            result = subprocess.run([PY312, str(probe), str(reader.port)],
                                    cwd=ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
            self.assertEqual(result.returncode, 0,
                             result.stdout + result.stderr)
            self.assertIn(b"posted", result.stdout)


if __name__ == "__main__":
    unittest.main()
