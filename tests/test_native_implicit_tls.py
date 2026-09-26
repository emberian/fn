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
import subprocess
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement
import tests.test_native_starttls as starttls
from tests.test_native_starttls import (
    IMAGE, ROOT, MemoryTlsClient, environment, free_loopback_port, recv_line)


class TlsLines:
    def __init__(self, tls: ssl.SSLSocket):
        self.tls = tls
        self.buffered = b""

    def readline(self) -> bytes:
        while b"\r\n" not in self.buffered:
            piece = self.tls.recv(65536)
            if not piece:
                raise EOFError("TLS connection ended before an NNTP line")
            self.buffered += piece
        line, self.buffered = self.buffered.split(b"\r\n", 1)
        return line + b"\r\n"

    def block(self) -> list[bytes]:
        lines = []
        while True:
            line = self.readline()
            if line == b".\r\n":
                return lines
            lines.append(line)

    def ask(self, command: bytes) -> bytes:
        self.tls.sendall(command + b"\r\n")
        return self.readline()


@unittest.skipUnless(IMAGE.is_file(), "build/fn-host is required")
class NativeImplicitTlsTests(unittest.TestCase):
    # The STARTTLS module's scratch store, certificate and owner lifecycle.
    setUp = starttls.NativeStartTlsTests.setUp
    make_certificate = starttls.NativeStartTlsTests.make_certificate
    start = starttls.NativeStartTlsTests.start
    stop = starttls.NativeStartTlsTests.stop

    def write_tls_config(self, tls_port: int | None, certificate=None,
                         private_key=None) -> object:
        lines = ['[store]', 'path = "{}"'.format(self.store), '',
                 '[listener]', 'host = "127.0.0.1"', 'port = {}'.format(self.port)]
        if certificate is not None:
            lines += ['tls_cert = "{}"'.format(certificate),
                      'tls_key = "{}"'.format(private_key)]
        if tls_port is not None:
            lines.append('tls_port = {}'.format(tls_port))
        # protected_only needs the TLS pair (the run gate); without one the
        # node is a plain loopback node.
        lines += ['', '[auth]', 'protected_only = {}'.format(
            'true' if certificate is not None else 'false'), '']
        config = self.root / "fn.toml"
        config.write_text("\n".join(lines), encoding="ascii")
        return config

    def operator(self, config, *argv: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [str(IMAGE), "--fn", "operator", str(config), *argv],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)

    def start_tls(self, config, tls_port: int) -> subprocess.Popen[bytes]:
        process = self.start(config)
        line = wait_for_announcement(process, b"LISTENING-TLS ")
        if line != "LISTENING-TLS {}\n".format(tls_port).encode():
            diagnostic = stop_and_diagnostics(process)
            self.fail("no implicit-TLS listener: {!r} {}".format(line, diagnostic))
        return process

    def test_implicit_tls_is_the_starttls_session(self) -> None:
        tls_port = free_loopback_port()
        config = self.write_tls_config(tls_port, self.certificate, self.private_key)
        process = self.start_tls(config, tls_port)
        try:
            context = ssl.create_default_context(cafile=str(self.certificate))
            context.check_hostname = True
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
            with socket.create_connection(("127.0.0.1", tls_port), timeout=15) as raw:
                with context.wrap_socket(raw, server_hostname="localhost") as tls:
                    tls.settimeout(15)
                    lines = TlsLines(tls)
                    greeting = lines.readline()
                    self.assertTrue(greeting.startswith((b"200 ", b"201 ")), greeting)
                    self.assertTrue(lines.ask(b"CAPABILITIES").startswith(b"101 "))
                    capabilities = lines.block()
                    self.assertNotIn(b"STARTTLS\r\n", capabilities)
                    # protected_only: AUTHINFO is allowed at once, not 483.
                    self.assertTrue(lines.ask(b"AUTHINFO USER reader").startswith(b"381 "))
                    self.assertTrue(lines.ask(b"STARTTLS").startswith(b"502 "))
                    self.assertTrue(lines.ask(b"DATE").startswith(b"111 "))
                    self.assertTrue(lines.ask(b"QUIT").startswith(b"205 "))
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
        config = self.write_tls_config(free_loopback_port())
        result = self.operator(config, "run")
        self.assertEqual(result.returncode, 5, result.stdout + result.stderr)
        self.assertNotIn(b"LISTENING", result.stdout)

    def test_store_inspect_settles_accepted_and_absent(self) -> None:
        config = self.write_tls_config(None)
        process = self.start(config)
        msgid = "<sanding-inspect@fn.example.invalid>"
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=15) as peer:
                peer.settimeout(15)
                recv_line(peer)
                peer.sendall(b"POST\r\n")
                response, _ = recv_line(peer)
                self.assertTrue(response.startswith(b"340 "), response)
                article = ("From: reader@fn.example.invalid\r\nNewsgroups: fn.test\r\n"
                           "Subject: settle me\r\nMessage-ID: {}\r\n\r\nbody\r\n.\r\n"
                           .format(msgid)).encode()
                peer.sendall(article)
                response, _ = recv_line(peer)
                self.assertTrue(response.startswith(b"240 "), response)
            # With the owner running the store is held: refused, no verdict.
            held = self.operator(config, "store", "inspect", msgid)
            self.assertNotEqual(held.returncode, 0)
            self.assertNotIn(b"accepted <", held.stdout)
            self.assertNotIn(b"absent <", held.stdout)
        finally:
            self.stop(process)
        found = self.operator(config, "store", "inspect", msgid)
        self.assertEqual(found.returncode, 0, found.stdout + found.stderr)
        self.assertEqual(
            found.stdout.decode().splitlines()[0],
            "accepted {} an article is stored here under this Message-ID".format(msgid))
        missing = self.operator(config, "store", "inspect", "<never-posted@fn.example.invalid>")
        self.assertEqual(missing.returncode, 1, missing.stdout + missing.stderr)
        self.assertEqual(
            missing.stdout.decode().splitlines()[0],
            "absent <never-posted@fn.example.invalid> nothing is stored here under this Message-ID")
        malformed = self.operator(config, "store", "inspect", "not-a-message-id")
        self.assertEqual(malformed.returncode, 5, malformed.stdout + malformed.stderr)


if __name__ == "__main__":
    unittest.main()
