"""COMPRESS DEFLATE (RFC 8054) through the saved native owner.

The client's side is Python's zlib (raw DEFLATE, wbits -15, a sync flush
after each command, as RFC 8054 section 4 describes a client).  The server's
inbound stream is decoded by ACL2 (books/deflate-inflate.lisp fn-zin-feed,
host/native/deflate.lisp); its outbound one by the vendored zlib
(host/native/fn-deflate.c).  The conversations:

  * before a login COMPRESS is 480 and not advertised; after it the label is
    offered and COMPRESS DEFLATE is 206; from the octet after the 206's CRLF
    every octet both ways is DEFLATE, and the session reads, posts and quits
    through it; CAPABILITIES withdraws STARTTLS, AUTHINFO and COMPRESS, and
    AUTHINFO, STARTTLS and a second COMPRESS are 502 (section 2.2.2);
  * compressed octets pipelined behind the COMPRESS line in the same send
    are the stream's first octets, not NNTP;
  * a decompression bomb is refused by name (compress-bomb) and the
    connection closes; a malformed stream is refused by name
    (compress-malformed) and the connection closes;
  * an unknown algorithm is 503 and a malformed one 501.
"""
import subprocess
import sys
import threading
import unittest
import zlib

from tests.native_harness import EXIT_OK, ROOT, Client, Node, native_image, requires

IMAGE = native_image("FN_NATIVE_HOST")


class Compressed:
    """The client's two DEFLATE streams over a connection that answered 206."""

    def __init__(self, client):
        self.client = client
        self.out = zlib.compressobj(6, zlib.DEFLATED, -15)
        self.inflater = zlib.decompressobj(-15)
        # Octets the line reader already took past the 206 are compressed.
        self.plain = self.inflater.decompress(client.pending)

    def send(self, octets, flush=True):
        data = self.out.compress(octets)
        if flush:
            data += self.out.flush(zlib.Z_SYNC_FLUSH)
        self.client.sock.sendall(data)

    def fill(self):
        piece = self.client.sock.recv(65536)
        if not piece:
            raise EOFError("the server closed the compressed connection")
        self.plain += self.inflater.decompress(piece)

    def line(self):
        while b"\r\n" not in self.plain:
            self.fill()
        line, self.plain = self.plain.split(b"\r\n", 1)
        return line + b"\r\n"

    def block(self):
        lines = []
        while True:
            line = self.line()
            if line == b".\r\n":
                return lines
            lines.append(line[:-2])

    def command(self, octets):
        self.send(octets + b"\r\n")
        return self.line()


@requires(IMAGE)
class NativeCompressTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE, control=False)
        self.root, self.config = self.node.root, self.node.config
        self.port = self.node.port
        self.auth = self.root / "credentials.toml"
        initialized = self.node.store("init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.node.write_config(extra='\n[auth]\nrequired = true\nprotected_only = false\n'
                                     'path = "{}"\n'.format(self.auth))
        enrolled = subprocess.run(
            [sys.executable, "bin/fn", "--config", str(self.config),
             "principal", "set-password", "native-reader",
             "--password", "correct-horse", "--posting"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=self.node.environment(), timeout=600, check=False)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())

    def start(self):
        return self.node.start(verb=("run", "--once"))

    def client(self):
        return Client(self.port, timeout=30, greeting=(b"201",))

    def expect(self, client, octets, status):
        client.send(octets + b"\r\n")
        line = client.line()
        self.assertTrue(line.startswith(status), (octets, line))
        return line

    def capabilities(self, client):
        client.send(b"CAPABILITIES\r\n")
        self.assertTrue(client.line().startswith(b"101 "))
        lines = []
        while True:
            line = client.line()
            if line == b".\r\n":
                return lines
            lines.append(line[:-2])

    def login(self, client):
        self.expect(client, b"AUTHINFO USER native-reader", b"381 ")
        self.expect(client, b"AUTHINFO PASS correct-horse", b"281 ")

    def test_the_compressed_session(self):
        self.start()
        with self.client() as client:
            self.assertNotIn(b"COMPRESS DEFLATE", self.capabilities(client))
            self.expect(client, b"COMPRESS DEFLATE", b"480 ")
            self.login(client)
            self.assertIn(b"COMPRESS DEFLATE", self.capabilities(client))
            self.expect(client, b"COMPRESS SHRINK", b"503 ")
            self.expect(client, b"COMPRESS deflate", b"501 ")
            self.expect(client, b"COMPRESS DEFLATE", b"206 ")
            z = Compressed(client)
            self.assertTrue(z.command(b"CAPABILITIES").startswith(b"101 "))
            labels = z.block()
            self.assertIn(b"READER", labels)
            for withdrawn in (b"COMPRESS DEFLATE", b"STARTTLS", b"AUTHINFO USER"):
                self.assertNotIn(withdrawn, labels)
            for refused in (b"AUTHINFO USER native-reader", b"STARTTLS", b"COMPRESS DEFLATE"):
                self.assertTrue(z.command(refused).startswith(b"502 "), refused)
            self.assertTrue(z.command(b"GROUP fn.test").startswith(b"211 "))
            self.assertTrue(z.command(b"POST").startswith(b"340 "))
            body = b"line of the compressed article\r\n" * 400
            z.send(b"From: Native Reader <reader@example.invalid>\r\n"
                   b"Newsgroups: fn.test\r\nSubject: compressed\r\n"
                   b"Message-ID: <compressed@example.invalid>\r\n\r\n" + body + b".\r\n")
            self.assertTrue(z.line().startswith(b"240 "))
            self.assertTrue(z.command(b"ARTICLE <compressed@example.invalid>").startswith(b"220 "))
            article = z.block()
            self.assertEqual(article[-1], b"line of the compressed article")
            self.assertEqual(sum(1 for l in article if l == b"line of the compressed article"), 400)
            self.assertTrue(z.command(b"QUIT").startswith(b"205 "))
            client.close(quit=False)
        self.node.exited(EXIT_OK)

    def test_pipelined_behind_the_command(self):
        # A client that pipelines (RFC 8054 says it MUST NOT, but a read may
        # carry both): the octets after the COMPRESS line are the stream's.
        self.start()
        with self.client() as client:
            self.login(client)
            out = zlib.compressobj(6, zlib.DEFLATED, -15)
            first = out.compress(b"DATE\r\n") + out.flush(zlib.Z_SYNC_FLUSH)
            client.sock.sendall(b"COMPRESS DEFLATE\r\n" + first)
            self.assertTrue(client.line().startswith(b"206 "))
            z = Compressed(client)
            z.out = out
            self.assertTrue(z.line().startswith(b"111 "))
            self.assertTrue(z.command(b"QUIT").startswith(b"205 "))
            client.close(quit=False)
        self.node.exited(EXIT_OK)

    def test_the_bomb_is_refused_by_name(self):
        process = self.start()
        with self.client() as client:
            self.login(client)
            self.expect(client, b"COMPRESS DEFLATE", b"206 ")
            z = Compressed(client)
            # Read (and discard) whatever the server answers, so it is never
            # held on TCP backpressure while it reads.
            done = threading.Event()

            def drain():
                try:
                    while True:
                        z.fill()
                        z.plain = b""
                except (EOFError, OSError, zlib.error):
                    done.set()
            reader = threading.Thread(target=drain, daemon=True)
            reader.start()
            flood = zlib.compressobj(9, zlib.DEFLATED, -15)
            bomb = flood.compress(b"DATE\r\n" * 400000) + flood.flush(zlib.Z_SYNC_FLUSH)
            self.assertLess(len(bomb), 16384)
            try:
                client.sock.sendall(bomb)
            except OSError:
                pass
            self.assertTrue(done.wait(60), "the connection was not closed")
        process.output_until(b"compress-bomb", timeout=60)
        self.node.exited(EXIT_OK)

    def test_a_malformed_stream_is_refused_by_name(self):
        process = self.start()
        with self.client() as client:
            self.login(client)
            self.expect(client, b"COMPRESS DEFLATE", b"206 ")
            client.sock.sendall(b"\x06\x00\x00\x00")  # BTYPE 3
            client.sock.settimeout(30)
            self.assertEqual(client.sock.recv(65536), b"")
        process.output_until(b"compress-malformed", timeout=60)
        self.node.exited(EXIT_OK)


if __name__ == "__main__":
    unittest.main()
