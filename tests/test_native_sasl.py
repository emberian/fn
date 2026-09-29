"""SCN-205: AUTHINFO SASL (RFC 4643 section 2.4) on the native node --
PLAIN (RFC 4616) over TLS, SCRAM-SHA-256 (RFC 5802, RFC 7677) and
SCRAM-SHA-256-PLUS with the tls-exporter channel binding (RFC 9266).

One node on loopback: a plaintext reader listener that offers STARTTLS, an
implicit-TLS listener, `[auth] required = true, protected_only = false`, and
an auth.toml whose one credential `principal set-password` wrote (ACL2
derives the verifier; this test never computes one).  The client side of
every mechanism is tests/sasl_client.py, written from the RFCs.

The decisions are ACL2's: books/nntp-auth.lisp (the AUTHINFO SASL arms and
the (:sasl-context SEED BINDING) wire event), books/sasl.lisp and
books/scram.lisp.  The host sends the context at the open and after every
handshake (host/native/mux.lisp fnn-mux-admit, fnn-mux-handshake-step) and
reads the exporter (host/native/tls.lisp fnn-tls-exporter).

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_sasl
"""

import queue
import re
import shutil
import subprocess
import threading
import time
import unittest

from tests.native_harness import (
    EXIT_OK, Client, Node, article, client_context, native_image, requires)
from tests.sasl_client import b64, plain_response, scram_login, status_data

IMAGE = native_image("FN_NATIVE_HOST")
LOGIN, PASSWORD = "sasl-reader", "correct-horse"  # FAKE-SECRET: a test fixture's password
SASL_CLEAR = b"SASL SCRAM-SHA-256"
SASL_TLS12 = b"SASL SCRAM-SHA-256 PLAIN"
SASL_TLS13 = b"SASL SCRAM-SHA-256-PLUS SCRAM-SHA-256 PLAIN"


@requires(IMAGE)
class NativeSaslTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE, control=False)
        self.node.use_tls(alt_name=True, protected_only=False)
        self.root, self.port, self.tls_port = self.node.root, self.node.port, self.node.tls_port
        self.auth = self.root / "credentials.toml"
        self.node.write_config(extra=(
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n'
            '\n[auth]\nrequired = true\nprotected_only = false\npath = "{}"\n').format(
                self.tls_port, self.node.cert, self.root / "key.pem", self.auth))
        initialized = self.node.store("init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        # The native operator reads the password and its confirmation from
        # standard input when there is no tty; it stores verifier v2 (the
        # SCRAM keys), never the password.
        secret = PASSWORD if isinstance(PASSWORD, bytes) else PASSWORD.encode()
        self.node.operator("principal", "set-password", LOGIN, "--posting",
                           input=secret + b"\n" + secret + b"\n", expect=EXIT_OK)
        self.node.start()

    # -- sessions --------------------------------------------------------

    def clear(self):
        client = Client(self.port, timeout=30, greeting=None)
        self.addCleanup(client.close)
        return client

    def tls(self):
        client = Client(self.tls_port, timeout=30, implicit_tls=client_context(), greeting=None)
        self.addCleanup(client.close)
        return client

    def capabilities(self, client):
        first, body = client.multiline(b"CAPABILITIES")
        self.assertTrue(first.startswith(b"101"), first)
        return [line for line in body.split(b"\r\n") if line]

    def sasl_line(self, client):
        return SASL_TLS13 if client.sock.version() == "TLSv1.3" else SASL_TLS12

    def scram(self, client, login=LOGIN, password=PASSWORD, **options):
        return scram_login(client.command, client.command, login, password, **options)

    def assert_status(self, line, status):
        self.assertTrue(line.startswith(status), line)

    # -- CAPABILITIES ----------------------------------------------------

    def test_capabilities_offer_by_protection_and_login(self):
        clear = self.clear()
        listed = self.capabilities(clear)
        self.assertIn(b"AUTHINFO USER SASL", listed)
        self.assertIn(SASL_CLEAR, listed)
        self.assertIn(b"STARTTLS", listed)
        self.assert_status(clear.starttls(), b"382")
        listed = self.capabilities(clear)
        self.assertIn(self.sasl_line(clear), listed)
        self.assertNotIn(b"STARTTLS", listed)
        protected = self.tls()
        listed = self.capabilities(protected)
        self.assertIn(self.sasl_line(protected), listed)
        self.assert_status(protected.command(
            "AUTHINFO SASL PLAIN " + plain_response(LOGIN, PASSWORD)), b"281")
        listed = self.capabilities(protected)
        self.assertIn(self.sasl_line(protected), listed)
        self.assertFalse([line for line in listed if line.startswith(b"AUTHINFO")], listed)

    # -- PLAIN -----------------------------------------------------------

    def test_plain(self):
        clear = self.clear()
        self.assert_status(clear.command(
            "AUTHINFO SASL PLAIN " + plain_response(LOGIN, PASSWORD)), b"483")
        client = self.tls()
        self.assert_status(client.command(
            "AUTHINFO SASL PLAIN " + plain_response(LOGIN, "wrong")), b"481")
        self.assert_status(client.command("AUTHINFO SASL NOT-A-MECHANISM"), b"503")
        self.assert_status(client.command("AUTHINFO SASL PLAIN !!!not-base64"), b"504")
        # No initial response: the empty challenge, then the response line;
        # `*' cancels (RFC 4643 section 2.4.1).
        self.assertEqual(client.command("AUTHINFO SASL PLAIN").rstrip(b"\r\n"), b"383 =")
        self.assert_status(client.command("*"), b"481")
        self.assertEqual(client.command("AUTHINFO SASL PLAIN").rstrip(b"\r\n"), b"383 =")
        self.assert_status(client.command(plain_response(LOGIN, PASSWORD)), b"281")
        self.assert_status(client.command("GROUP fn.test"), b"211")
        other = self.tls()
        self.assert_status(other.command(
            "AUTHINFO SASL PLAIN " + plain_response(LOGIN, PASSWORD)), b"281")

    # -- SCRAM-SHA-256 ---------------------------------------------------

    def test_scram_over_implicit_tls_then_post(self):
        client = self.tls()
        final, scram, _ = self.scram(client)
        status, server_final = status_data(final)
        self.assertEqual(status, "283", final)
        self.assertTrue(scram.nonce.startswith(scram.cnonce))
        self.assertEqual(scram.iterations, 4096)
        self.assertTrue(scram.salt)
        self.assertTrue(scram.server_final_ok(server_final), server_final)
        first, done = client.post(article("<sasl-scram-1@example.invalid>"))
        self.assert_status(first, b"340")
        self.assert_status(done, b"240")

    def test_scram_in_clear_and_after_starttls(self):
        # In clear SCRAM is offered (no password crosses the wire); after
        # STARTTLS the host sent a fresh context (the 382 cleared the old).
        clear = self.clear()
        final, scram, _ = self.scram(clear)
        self.assertEqual(status_data(final)[0], "283", final)
        self.assertTrue(scram.server_final_ok(status_data(final)[1]))
        self.assert_status(clear.command("GROUP fn.test"), b"211")
        upgraded = self.clear()
        self.assert_status(upgraded.starttls(), b"382")
        final, scram, _ = self.scram(upgraded)
        self.assertEqual(status_data(final)[0], "283", final)
        self.assertTrue(scram.server_final_ok(status_data(final)[1]))

    def test_scram_wrong_password_is_481(self):
        client = self.tls()
        final, _, sent = self.scram(client, password="wrong")
        self.assertIsNotNone(sent)
        self.assert_status(final, b"481")
        self.assert_status(client.command("GROUP fn.test"), b"480")

    def test_scram_replayed_final_is_481(self):
        cnonce = b"fixed-client-nonce-for-replay"
        first = self.tls()
        final, scram, captured = self.scram(first, cnonce=cnonce)
        self.assertEqual(status_data(final)[0], "283", final)
        second = self.tls()
        opened = second.command("AUTHINFO SASL SCRAM-SHA-256 " + b64(scram.client_first()))
        status, server_first = status_data(opened)
        self.assertEqual(status, "383", opened)
        # The server nonce is fresh per connection (its seed).
        self.assertNotIn(scram.nonce, server_first)
        self.assert_status(second.command(captured), b"481")

    # -- SCRAM-SHA-256-PLUS (tls-exporter) --------------------------------

    def test_scram_plus_with_tls_exporter(self):
        session = OpensslSession.open(self, self.tls_port)
        final, scram, _ = scram_login(session.command, session.command, LOGIN, PASSWORD,
                                      binding=session.exporter)
        self.assertEqual(status_data(final)[0], "283", final)
        self.assertTrue(scram.server_final_ok(status_data(final)[1]))
        self.assert_status(session.command("GROUP fn.test"), b"211")
        # A binding other than this connection's exporter value.
        session = OpensslSession.open(self, self.tls_port)
        wrong = bytes(octet ^ 0xFF for octet in session.exporter)
        final, _, _ = scram_login(session.command, session.command, LOGIN, PASSWORD,
                                  binding=wrong)
        self.assert_status(final, b"481")


class OpensslSession:
    """An NNTP session through `openssl s_client -tls1_3` on the implicit-TLS
    listener, which prints the connection's RFC 9266 tls-exporter value
    (Python's ssl has no exporter API).  Not -quiet: that suppresses the
    keying-material print; -nocommands keeps QUIT from being s_client's."""

    LABEL = "EXPORTER-Channel-Binding"

    def __init__(self, process):
        self.process = process
        self.lines = queue.Queue()
        self.exporter = None
        threading.Thread(target=self._drain, daemon=True).start()

    def _drain(self):
        for line in self.process.stdout:
            self.lines.put(line)
        self.lines.put(None)

    @classmethod
    def open(cls, case, port):
        openssl = shutil.which("openssl")
        if openssl is None:
            raise unittest.SkipTest("SCRAM-SHA-256-PLUS: no openssl binary for s_client")
        process = subprocess.Popen(
            [openssl, "s_client", "-connect", "127.0.0.1:{}".format(port), "-tls1_3",
             "-keymatexport", cls.LABEL, "-keymatexportlen", "32", "-nocommands",
             "-ign_eof"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        session = cls(process)
        case.addCleanup(session.close)
        seen = []
        deadline = time.monotonic() + 30
        while session.exporter is None:
            line = session.next_line(deadline)
            seen.append(line)
            found = re.search(rb"Keying material:\s*([0-9A-Fa-f]+)", line)
            if found:
                session.exporter = bytes.fromhex(found.group(1).decode("ascii"))
            elif re.search(rb"Unknown option|Use -help", line):
                raise unittest.SkipTest("SCRAM-SHA-256-PLUS: openssl s_client cannot export "
                                        "keying material here: " + line.decode("ascii", "replace"))
        case.assertEqual(len(session.exporter), 32, b"".join(seen))
        session.status(deadline)  # the greeting
        return session

    def next_line(self, deadline):
        try:
            line = self.lines.get(timeout=max(0.1, deadline - time.monotonic()))
        except queue.Empty:
            raise AssertionError("openssl s_client: no line in time")
        if line is None:
            raise EOFError("openssl s_client ended")
        return line

    def status(self, deadline=None):
        """The next NNTP status line; s_client's own prints are skipped."""
        deadline = deadline or time.monotonic() + 30
        while True:
            line = self.next_line(deadline)
            if re.match(rb"^[1-5][0-9][0-9]( |\r?\n)", line):
                return line.rstrip(b"\r\n") + b"\r\n"

    def command(self, text):
        if isinstance(text, str):
            text = text.encode("utf-8")
        self.process.stdin.write(text + b"\r\n")
        self.process.stdin.flush()
        return self.status()

    def close(self):
        try:
            self.process.stdin.close()
        except OSError:
            pass
        self.process.terminate()
        try:
            self.process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait(timeout=10)


if __name__ == "__main__":
    unittest.main()
