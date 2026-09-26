#!/usr/bin/env python3
"""STARTTLS through the saved native owner, with OpenSSL 3+ or LibreSSL 3+ in the node."""

from __future__ import annotations

import os
from pathlib import Path
import select
import socket
import ssl
import subprocess
import tempfile
import time
import unittest


from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parents[1]
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def environment() -> dict[str, str]:
    result = dict(os.environ)
    result["ACL2_CUSTOMIZATION"] = "NONE"
    result.pop("ACL2_SYSTEM_BOOKS", None)
    result.pop("FN_HOST", None)
    return result


def free_loopback_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def recv_line(peer: socket.socket, prefix: bytes = b"") -> tuple[bytes, bytes]:
    buffered = prefix
    while b"\r\n" not in buffered:
        piece = peer.recv(65536)
        if not piece:
            raise EOFError("connection ended before an NNTP line")
        buffered += piece
    line, remainder = buffered.split(b"\r\n", 1)
    return line + b"\r\n", remainder


def client_context() -> ssl.SSLContext:
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    return context


def tls_1_1_client_hello() -> bytes:
    """A ClientHello that offers only TLS 1.1 (legacy_version 03 02, no
    supported_versions extension), built by hand so the refusal under test is
    the server's and never the client library's own protocol policy."""
    body = (b"\x03\x02" + bytes(range(32)) + b"\x00"
            + b"\x00\x04\xc0\x13\x00\x2f" + b"\x01\x00")
    handshake = b"\x01" + len(body).to_bytes(3, "big") + body
    return b"\x16\x03\x01" + len(handshake).to_bytes(2, "big") + handshake


def starttls_socket(port: int) -> socket.socket:
    """A plaintext connection that has received 200/201 and 382."""
    peer = socket.create_connection(("127.0.0.1", port), timeout=15)
    peer.settimeout(15)
    greeting, remainder = recv_line(peer)
    if not greeting[:3] in (b"200", b"201") or remainder:
        raise AssertionError(greeting)
    peer.sendall(b"STARTTLS\r\n")
    response, remainder = recv_line(peer)
    if not response.startswith(b"382 ") or remainder:
        raise AssertionError(response)
    return peer


class MemoryTlsClient:
    """A client that can place ClientHello behind STARTTLS in one send."""

    def __init__(self, peer: socket.socket):
        self.peer = peer
        self.incoming = ssl.MemoryBIO()
        self.outgoing = ssl.MemoryBIO()
        self.ssl = client_context().wrap_bio(
            self.incoming, self.outgoing, server_side=False,
            server_hostname="localhost")
        self.plaintext = b""

    def _send_pending(self) -> bytes:
        data = self.outgoing.read()
        if data:
            self.peer.sendall(data)
        return data

    def begin_pipelined(self) -> None:
        with self.assert_want_read():
            self.ssl.do_handshake()
        hello = self.outgoing.read()
        if not hello:
            raise AssertionError("client emitted no ClientHello")
        # One send is the concrete same-read candidate.  The server's
        # MSG_PEEK seam and ACL2 prefix count preserve the suffix even if the
        # kernel exposes this send in smaller observations.
        self.peer.sendall(b"STARTTLS\r\n" + hello)
        response, remainder = recv_line(self.peer)
        if not response.startswith(b"382 "):
            raise AssertionError("STARTTLS failed: {!r}".format(response))
        if remainder:
            self.incoming.write(remainder)
        self._complete_handshake()

    class assert_want_read:
        def __enter__(self):
            return self

        def __exit__(self, kind, value, traceback):
            if kind is ssl.SSLWantReadError:
                return True
            if kind is None:
                raise AssertionError("TLS operation unexpectedly completed")
            return False

    def _complete_handshake(self) -> None:
        deadline = time.monotonic() + 15
        while True:
            try:
                self.ssl.do_handshake()
                self._send_pending()
                return
            except ssl.SSLWantWriteError:
                self._send_pending()
                continue
            except ssl.SSLWantReadError:
                self._send_pending()
                if time.monotonic() >= deadline:
                    raise TimeoutError("pipelined TLS handshake timed out")
                piece = self.peer.recv(65536)
                if not piece:
                    raise EOFError("server ended the pipelined TLS handshake")
                self.incoming.write(piece)

    def sendall(self, plaintext: bytes) -> None:
        offset = 0
        while offset < len(plaintext):
            try:
                offset += self.ssl.write(plaintext[offset:])
            except (ssl.SSLWantReadError, ssl.SSLWantWriteError):
                pass
            self._send_pending()

    def readline(self) -> bytes:
        while b"\r\n" not in self.plaintext:
            try:
                piece = self.ssl.read(65536)
                if not piece:
                    raise EOFError("TLS connection ended before an NNTP line")
                self.plaintext += piece
                continue
            except ssl.SSLWantWriteError:
                self._send_pending()
                continue
            except ssl.SSLWantReadError:
                self._send_pending()
            encrypted = self.peer.recv(65536)
            if not encrypted:
                raise EOFError("TLS connection ended before an NNTP line")
            self.incoming.write(encrypted)
        line, self.plaintext = self.plaintext.split(b"\r\n", 1)
        return line + b"\r\n"


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeStartTlsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-starttls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.port = free_loopback_port()
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.certificate, self.private_key = self.make_certificate("server")

    def make_certificate(self, name: str) -> tuple[Path, Path]:
        certificate = self.root / (name + "-certificate.pem")
        private_key = self.root / (name + "-private-key.pem")
        subprocess.run(
            ["openssl", "req", "-x509", "-newkey", "rsa:2048",
             "-keyout", str(private_key), "-out", str(certificate),
             "-sha256", "-days", "1", "-nodes", "-subj", "/CN=localhost"],
            cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            timeout=60, check=True)
        return certificate, private_key

    def write_config(self, certificate: Path, private_key: Path) -> Path:
        config = self.root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\ntls_cert = "{}"\ntls_key = "{}"\n\n'
            '[auth]\nprotected_only = true\n'
            .format(self.store, self.port, certificate, private_key),
            encoding="ascii")
        return config

    def start(self, config: Path) -> subprocess.Popen[bytes]:
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(config), "run"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        assert process.stdout is not None
        line = wait_for_announcement(process, b"LISTENING ")
        if line != "LISTENING {}\n".format(self.port).encode():
            diagnostic = stop_and_diagnostics(process)
            self.fail("native TLS owner failed: {!r} {}".format(line, diagnostic))
        return process

    def stop(self, process: subprocess.Popen[bytes]) -> None:
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=10)
        assert process.stdout is not None and process.stderr is not None
        process.stdout.close()
        process.stderr.close()

    def test_context_mismatch_refuses_before_listener(self) -> None:
        _, wrong_key = self.make_certificate("wrong")
        config = self.write_config(self.certificate, wrong_key)
        result = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(config), "run", "--once"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)
        self.assertEqual(result.returncode, 4, result.stderr.decode())
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"mismatch", result.stderr.lower())

    def assertClosedAfterFailedHandshake(self, sock: socket.socket) -> None:
        """The server closes after a malformed ClientHello, sending at most one
        fatal TLS alert record first. OpenSSL 3 closes with no bytes; LibreSSL
        sends a fatal alert (e.g. 15 03 01 00 02 02 46, protocol_version) and
        then closes. Refuted: any plaintext NNTP reply, a handshake or other
        non-alert record, a warning-level alert, a second record, or a
        connection that stays open (timeout)."""
        received = b""
        while True:
            try:
                chunk = sock.recv(1024)
            except ConnectionResetError:
                # Linux may reset a close with unread malformed TLS bytes.
                break
            if not chunk:
                break
            received += chunk
            self.assertLessEqual(len(received), 7, received)
        if received == b"":
            return
        self.assertEqual(len(received), 7, received)
        self.assertEqual(received[0], 0x15, received)       # alert record
        self.assertEqual(received[1], 0x03, received)       # TLS major
        self.assertIn(received[2], (0x01, 0x02, 0x03, 0x04), received)
        self.assertEqual(received[3:5], b"\x00\x02", received)
        self.assertEqual(received[5], 0x02, received)       # fatal level

    def test_protocol_floor_refuses_tls_1_1(self) -> None:
        """The listener's TLS 1.2 floor (host/native/tls.lisp
        fnn-tls-open-context, SSL_CTX_ctrl 123) holds under whichever library
        the node loaded, OpenSSL 3+ or LibreSSL 3+ (HST-016). Refuted: a
        ServerHello (or any handshake record) answering a TLS 1.1-only
        ClientHello; a non-fatal alert or one other than protocol_version (70);
        a connection left open. The TLS 1.2 client afterwards shows the refusal
        is the floor, not a broken listener."""
        process = self.start(self.write_config(self.certificate, self.private_key))
        try:
            with starttls_socket(self.port) as old:
                old.sendall(tls_1_1_client_hello())
                received = b""
                while True:
                    try:
                        chunk = old.recv(1024)
                    except ConnectionResetError:
                        break
                    if not chunk:
                        break
                    received += chunk
                    self.assertLessEqual(len(received), 7, received)
                self.assertNotEqual(received[:1], b"\x16", received)
                if received:
                    self.assertEqual(len(received), 7, received)
                    self.assertEqual(received[0], 0x15, received)
                    self.assertEqual(received[3:5], b"\x00\x02", received)
                    self.assertEqual(received[5:7], b"\x02\x46", received)
            with starttls_socket(self.port) as current:
                context = client_context()
                context.maximum_version = ssl.TLSVersion.TLSv1_2
                with context.wrap_socket(current) as protected:
                    self.assertEqual(protected.version(), "TLSv1.2")
                    protected.sendall(b"DATE\r\n")
                    line, _ = recv_line(protected)
                    self.assertTrue(line.startswith(b"111 "), line)
            self.assertIsNone(process.poll(), "a refused handshake stopped the owner")
        finally:
            self.stop(process)

    def test_sni_answered_with_the_configured_certificate(self) -> None:
        """A client that sends server_name (RFC 6066 section 3) completes the
        handshake and is served with the one configured certificate, the same
        one a client without SNI gets, under OpenSSL or LibreSSL. Refuted: a
        handshake failure or unrecognized_name alert when SNI is present, a
        different certificate for the SNI client, a session that does not
        carry NNTP after the handshake."""
        process = self.start(self.write_config(self.certificate, self.private_key))
        try:
            served = []
            for name in ("sni-probe.fn.invalid", None):
                with starttls_socket(self.port) as peer:
                    with client_context().wrap_socket(peer, server_hostname=name) as protected:
                        served.append(protected.getpeercert(binary_form=True))
                        protected.sendall(b"DATE\r\n")
                        line, _ = recv_line(protected)
                        self.assertTrue(line.startswith(b"111 "), line)
            expected = ssl.PEM_cert_to_DER_cert(self.certificate.read_text())
            self.assertEqual(served, [expected, expected])
            self.assertIsNone(process.poll())
        finally:
            self.stop(process)

    def test_pipelined_clienthello_protection_and_failure_isolation(self) -> None:
        process = self.start(self.write_config(self.certificate, self.private_key))
        try:
            # A malformed handshake kills this connection after 382, but the
            # listener and the shared validated context remain usable.
            with socket.create_connection(("127.0.0.1", self.port), timeout=15) as bad:
                bad.settimeout(15)
                greeting, remainder = recv_line(bad)
                self.assertTrue(greeting.startswith(b"200 "), greeting)
                self.assertEqual(remainder, b"")
                bad.sendall(b"STARTTLS\r\n")
                response, remainder = recv_line(bad)
                self.assertTrue(response.startswith(b"382 "), response)
                self.assertEqual(remainder, b"")
                bad.sendall(b"not a TLS ClientHello\r\n")
                bad.shutdown(socket.SHUT_WR)
                self.assertClosedAfterFailedHandshake(bad)

            with socket.create_connection(("127.0.0.1", self.port), timeout=15) as peer:
                peer.settimeout(15)
                greeting, remainder = recv_line(peer)
                self.assertTrue(greeting.startswith(b"200 "), greeting)
                self.assertEqual(remainder, b"")

                peer.sendall(b"AUTHINFO USER hidden-until-protected\r\n")
                response, remainder = recv_line(peer)
                self.assertTrue(response.startswith(b"483 "), response)
                self.assertEqual(remainder, b"")

                protected = MemoryTlsClient(peer)
                protected.begin_pipelined()

                protected.sendall(b"AUTHINFO USER reader\r\n")
                self.assertTrue(protected.readline().startswith(b"381 "))
                protected.sendall(b"STARTTLS\r\n")
                self.assertTrue(protected.readline().startswith(b"502 "))
                protected.sendall(b"DATE\r\n")
                self.assertTrue(protected.readline().startswith(b"111 "))
                protected.sendall(b"QUIT\r\n")
                self.assertTrue(protected.readline().startswith(b"205 "))
            self.assertIsNone(process.poll(), "one peer failure stopped the owner")
        finally:
            self.stop(process)


if __name__ == "__main__":
    unittest.main()
