#!/usr/bin/env python3
"""SCN-092: the implicit-TLS listener and the operator's settling lookup.

`[listener] tls_port' opens a second listener whose connections begin TLS
at connect (what tin 2.6 speaks); ACL2 offers it only beside a certificate
and key (fn-native-operator-implicit-tls-listener-needs-its-certificate),
and the connection it accepts is the STARTTLS session after its handshake
(books/served-implicit-tls.lisp).  `store inspect MESSAGE-ID' answers the
operator accepted or absent from the stopped store
(fn-native-operator-inspect-report-is-the-lookup).
"""

from __future__ import annotations

import socket
import ssl
import unittest

from tests.native_harness import EXIT, Client, free_port, requires
import tests.test_native_starttls as starttls
from tests.test_native_starttls import IMAGE, MemoryTlsClient, recv_line


def verifying_context(certificate) -> ssl.SSLContext:
    """Verifies the node's certificate, issued for localhost (pass
    server_hostname="localhost" to Client)."""
    context = ssl.create_default_context(cafile=str(certificate))
    context.check_hostname = True
    return context


def lines_of(block: bytes) -> list[bytes]:
    return block.splitlines(keepends=True)


@requires(IMAGE)
class NativeImplicitTlsTests(unittest.TestCase):
    # The STARTTLS module's scratch node, store and certificate.
    setUp = starttls.NativeStartTlsTests.setUp
    make_certificate = starttls.NativeStartTlsTests.make_certificate
    stop = starttls.NativeStartTlsTests.stop

    def write_tls_config(self, tls_port: int | None, certificate=None,
                         private_key=None) -> None:
        extra = ""
        if certificate is not None:
            extra += 'tls_cert = "{}"\ntls_key = "{}"\n'.format(certificate, private_key)
        if tls_port is not None:
            extra += 'tls_port = {}\n'.format(tls_port)
        # protected_only needs the TLS pair (the run gate); without one the
        # node is a plain loopback node.
        extra += '\n[auth]\nprotected_only = {}\n'.format(
            'true' if certificate is not None else 'false')
        self.node.write_config(extra=extra)

    def start_tls(self, tls_port: int):
        process = self.node.start()
        line = process.announcement(b"LISTENING-TLS ")
        self.assertEqual(line, "LISTENING-TLS {}\n".format(tls_port).encode(),
                         "no implicit-TLS listener")
        return process

    def test_implicit_tls_is_the_starttls_session(self) -> None:
        tls_port = free_port()
        self.write_tls_config(tls_port, self.certificate, self.private_key)
        process = self.start_tls(tls_port)
        try:
            context = verifying_context(self.certificate)
            # A client that is not TLS on the TLS port ends only itself.
            with socket.create_connection(("127.0.0.1", tls_port), timeout=15) as bad:
                bad.settimeout(15)
                bad.sendall(b"CAPABILITIES\r\n")
                bad.shutdown(socket.SHUT_WR)
                try:
                    closed = bad.recv(1024)
                except ConnectionResetError:
                    closed = b""
                self.assertNotIn(b"101 ", closed)
            with Client(tls_port, timeout=15, implicit_tls=context,
                        server_hostname="localhost") as lines:
                self.assertTrue(lines.greeting.startswith((b"200 ", b"201 ")), lines.greeting)
                self.assertTrue(lines.command(b"CAPABILITIES").startswith(b"101 "))
                capabilities = lines_of(lines.block())
                self.assertNotIn(b"STARTTLS\r\n", capabilities)
                # protected_only: AUTHINFO is allowed at once, not 483.
                self.assertTrue(lines.command(b"AUTHINFO USER reader").startswith(b"381 "))
                self.assertTrue(lines.command(b"STARTTLS").startswith(b"502 "))
                self.assertTrue(lines.command(b"DATE").startswith(b"111 "))
                self.assertTrue(lines.command(b"QUIT").startswith(b"205 "))
            # The plaintext listener is unchanged: STARTTLS still upgrades.
            with socket.create_connection(("127.0.0.1", self.port), timeout=15) as peer:
                peer.settimeout(15)
                greeting, _ = recv_line(peer)
                self.assertTrue(greeting.startswith(b"200 "), greeting)
                upgraded = MemoryTlsClient(peer)
                upgraded.begin_pipelined()
                upgraded.sendall(b"STARTTLS\r\n")
                self.assertTrue(upgraded.readline().startswith(b"502 "))
            self.assertIsNone(process.poll(), "a client stopped the owner")
        finally:
            self.stop(process)

    def test_tls_port_without_certificate_is_refused(self) -> None:
        self.write_tls_config(free_port())
        result = self.node.operator("run")
        self.assertEqual(result.returncode, EXIT.USAGE, result.stdout + result.stderr)
        self.assertNotIn(b"LISTENING", result.stdout)

    def test_store_inspect_settles_accepted_and_absent(self) -> None:
        self.write_tls_config(None)
        process = self.node.start()
        msgid = "<sanding-inspect@fn.example.invalid>"
        try:
            with Client(self.port, timeout=15, greeting=None) as peer:
                article = ("From: reader@fn.example.invalid\r\nNewsgroups: fn.test\r\n"
                           "Subject: settle me\r\nMessage-ID: {}\r\n\r\nbody\r\n"
                           .format(msgid)).encode()
                response, final = peer.post(article)
                self.assertTrue(response.startswith(b"340 "), response)
                self.assertTrue(final.startswith(b"240 "), final)
            # With the owner running the store is held: refused, no verdict.
            held = self.node.operator("store", "inspect", msgid)
            self.assertNotEqual(held.returncode, 0)
            self.assertNotIn(b"accepted <", held.stdout)
            self.assertNotIn(b"absent <", held.stdout)
        finally:
            self.stop(process)
        found = self.node.operator("store", "inspect", msgid)
        self.assertEqual(found.returncode, 0, found.stdout + found.stderr)
        self.assertEqual(
            found.stdout.decode().splitlines()[0],
            "accepted {} an article is stored here under this Message-ID".format(msgid))
        missing = self.node.operator("store", "inspect", "<never-posted@fn.example.invalid>")
        self.assertEqual(missing.returncode, EXIT.REFUSED, missing.stdout + missing.stderr)
        self.assertEqual(
            missing.stdout.decode().splitlines()[0],
            "absent <never-posted@fn.example.invalid> nothing is stored here under this Message-ID")
        malformed = self.node.operator("store", "inspect", "not-a-message-id")
        self.assertEqual(malformed.returncode, EXIT.USAGE, malformed.stdout + malformed.stderr)


if __name__ == "__main__":
    unittest.main()
