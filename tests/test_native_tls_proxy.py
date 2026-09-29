"""PRF-986 item 4 (row W2a): the PROXY header on an explicitly trusted path.

One owner on 127.0.0.1 with an implicit-TLS listener.  127.0.0.10 plays a TCP
proxy (`policy set tls-proxy-trusted-peers 127.0.0.10/32'); other loopback
addresses are public clients.

- A trusted proxy's header (v1 and v2) names the original source, which is
  then charged its own per-source budget: past 3 a minute the asserted source
  is refused by name while another asserted source through the same proxy is
  still served.
- A public client's octets are never read as a header: its "PROXY ..." line is
  just a broken TLS handshake, and the source it claimed is never named.
- A malformed header from the proxy is refused by name
  (`reason=proxy-malformed proxy=127.0.0.10'), and a silent one is closed at
  the handshake deadline (`reason=proxy-timeout').

Run on hbox: tools/hbox_native.sh . tests.test_native_tls_proxy
"""
from __future__ import annotations

import os
from pathlib import Path
import socket
import ssl
import struct
import time
import unittest

from tests.native_harness import EXIT, Node, executable, native_image

IMAGE = (Path(os.environ["FN_NATIVE_HOST"]) if os.environ.get("FN_NATIVE_HOST")
         else native_image("FN_NATIVE_DEVELOPER_HOST"))
READY = executable(IMAGE)
PROXY = "127.0.0.10"


def client_context() -> ssl.SSLContext:
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    return context


def v1(source: str) -> bytes:
    return "PROXY TCP4 {} 127.0.0.1 40000 563\r\n".format(source).encode()


def v2(source: str) -> bytes:
    body = socket.inet_aton(source) + socket.inet_aton("127.0.0.1") + struct.pack("!HH", 40000, 563)
    return (b"\r\n\r\n\x00\r\nQUIT\n" + bytes([0x21, 0x11]) + struct.pack("!H", len(body))
            + body)


@unittest.skipUnless(READY, "no native image (FN_NATIVE_HOST or build/fn-host-developer)")
class NativeTlsProxyTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE)
        self.addCleanup(self.stop)
        self.node.store("init", "fn.test", expect=EXIT.OK)
        self.node.use_tls()
        self.log = self.node.root / "fn.log"
        key = self.node.root / "key.pem"
        self.node.write_config(
            extra='tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[log]\npath = "{}"\n'.format(
                self.node.tls_port, self.node.cert, key, self.log),
            protected_only=True)
        self.policy("tls-proxy-trusted-peers", PROXY + "/32")
        # The proxy's own source is charged too: give it its own rate.
        self.policy("tls-handshake-source-overrides", PROXY + "=600")
        self.policy("tls-handshakes-per-source-per-minute", 3)

    def stop(self):
        if self.node.process is not None:
            self.node.stop(expect=None)

    def policy(self, slot, value):
        self.node.operator("policy", "set", slot, str(value), expect=EXIT.OK)

    def served(self, source, header, timeout=10):
        """True when, after HEADER, the TLS handshake from SOURCE completes
        and the node greets; False when the node closes it."""
        raw = socket.create_connection(("127.0.0.1", self.node.tls_port), timeout=timeout,
                                       source_address=(source, 0))
        try:
            if header:
                raw.sendall(header)
            sock = client_context().wrap_socket(raw, server_hostname="127.0.0.1")
        except (ssl.SSLError, ConnectionResetError, BrokenPipeError, OSError):
            raw.close()
            return False
        try:
            sock.settimeout(timeout)
            line = sock.recv(512)
            return line[:3] in (b"200", b"201", b"480")
        finally:
            sock.close()

    def log_text(self, needle, deadline=10):
        end = time.monotonic() + deadline
        while time.monotonic() < end:
            text = self.log.read_text(errors="replace") if self.log.exists() else ""
            if needle in text:
                return text
            time.sleep(0.2)
        self.fail("the service log never named {!r}".format(needle))

    def test_the_asserted_source_pays_its_own_budget(self):
        self.node.start()
        outcomes = [self.served(PROXY, v1("198.51.100.7")) for _ in range(5)]
        self.assertEqual(outcomes, [True, True, True, False, False], outcomes)
        self.log_text("tls refused reason=handshake-budget source=198.51.100.7")
        # Another original source through the same proxy, in version 2.
        self.assertTrue(self.served(PROXY, v2("198.51.100.8")))
        self.assertIsNone(self.node.process.poll(), "the owner exited")

    def test_a_public_client_is_never_read_for_a_header(self):
        self.node.start()
        self.assertFalse(self.served("127.0.0.2", v1("198.51.100.66")))
        # A public client without a header is served as itself.
        self.assertTrue(self.served("127.0.0.3", b""))
        time.sleep(0.5)
        text = self.log.read_text(errors="replace") if self.log.exists() else ""
        self.assertNotIn("198.51.100.66", text)
        self.assertIsNone(self.node.process.poll(), "the owner exited")

    def test_a_malformed_or_silent_header_from_the_proxy_is_refused_by_name(self):
        self.policy("tls-handshake-ms", 2000)
        self.node.start()
        self.assertFalse(self.served(PROXY, b"PROXY TCP4 198.51.100.300 127.0.0.1 1 2\r\n"))
        self.log_text("tls refused reason=proxy-malformed proxy=127.0.0.10")
        raw = socket.create_connection(("127.0.0.1", self.node.tls_port), timeout=10,
                                       source_address=(PROXY, 0))
        try:
            began = time.monotonic()
            self.assertEqual(raw.recv(16), b"")  # closed at the deadline
            self.assertGreater(time.monotonic() - began, 1.5)
        finally:
            raw.close()
        self.log_text("tls refused reason=proxy-timeout proxy=127.0.0.10")
        self.assertIsNone(self.node.process.poll(), "the owner exited")


if __name__ == "__main__":
    unittest.main()
