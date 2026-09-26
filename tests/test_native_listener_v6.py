#!/usr/bin/env python3
"""SCN-126: one node listening on an IPv6 and an IPv4 loopback address.

`[listener] host = "[::1], 127.0.0.1"' is admitted by ACL2
(books/native-config.lisp `fn-native-config-listener-addresses', keystone
`fn-native-config-listener-addresses-are-bindable-projections') and projected
to ((:inet6 ::1) (:inet 127.0.0.1)); the owner (host/native/owner.lisp
`fnn-owner-run-normalized') binds a plain and an implicit-TLS listener for
each.  A client reaches every one of the four and reads the greeting.  The
wildcards, an IPv4-mapped address and a duplicate are refused at start by
name, before any listener: `usage operator request (CONFIGURATION REASON)'
and exit 5 (NNT-041).
"""

from __future__ import annotations

import socket
import ssl
import subprocess
import unittest

from tests.native_process import next_log_number, start_filed, wait_for_announcement
import tests.test_native_starttls as starttls
from tests.test_native_implicit_tls import TlsLines
from tests.test_native_starttls import IMAGE, ROOT, environment, free_loopback_port, recv_line

USAGE = 5
ADDRESSES = (("::1", socket.AF_INET6), ("127.0.0.1", socket.AF_INET))


def free_port_on_both() -> int:
    """A port free on ::1 and on 127.0.0.1 at the time of the probe."""
    for _ in range(64):
        port = free_loopback_port()
        try:
            with socket.socket(socket.AF_INET6) as probe:
                probe.bind(("::1", port))
            return port
        except OSError:
            continue
    raise AssertionError("no port free on both loopback families")


@unittest.skipUnless(IMAGE.is_file(), "build/fn-host is required")
class NativeListenerV6Tests(unittest.TestCase):
    setUp = starttls.NativeStartTlsTests.setUp
    make_certificate = starttls.NativeStartTlsTests.make_certificate
    stop = starttls.NativeStartTlsTests.stop

    def write_config(self, host: str, port: int, tls_port: int) -> object:
        lines = ['[store]', 'path = "{}"'.format(self.store), '',
                 '[listener]', 'host = "{}"'.format(host), 'port = {}'.format(port),
                 'tls_cert = "{}"'.format(self.certificate),
                 'tls_key = "{}"'.format(self.private_key),
                 'tls_port = {}'.format(tls_port),
                 '', '[auth]', 'protected_only = true', '']
        config = self.root / "fn.toml"
        config.write_text("\n".join(lines), encoding="ascii")
        return config

    def start(self, config) -> subprocess.Popen[bytes]:
        log = self.root / "owner-{}.stderr".format(next_log_number(self))
        return start_filed([str(IMAGE), "--fn", "operator", str(config), "run"],
                           log, cwd=ROOT, env=environment())

    def test_every_address_serves_plain_and_implicit_tls(self) -> None:
        port = free_port_on_both()
        tls_port = free_port_on_both()
        config = self.write_config("[::1], 127.0.0.1", port, tls_port)
        process = self.start(config)
        try:
            # LISTENING PORT precedes it; both follow every bind.
            line = wait_for_announcement(process, b"LISTENING-TLS ")
            self.assertEqual(line, "LISTENING-TLS {}\n".format(tls_port).encode())
            context = ssl.create_default_context(cafile=str(self.certificate))
            context.check_hostname = True
            for address, family in ADDRESSES:
                with self.subTest(address=address, listener="plain"):
                    with socket.socket(family) as peer:
                        peer.settimeout(15)
                        peer.connect((address, port))
                        greeting, _ = recv_line(peer)
                        self.assertTrue(greeting.startswith(b"200 "), greeting)
                        peer.sendall(b"QUIT\r\n")
                        closing, _ = recv_line(peer)
                        self.assertTrue(closing.startswith(b"205 "), closing)
                with self.subTest(address=address, listener="implicit-tls"):
                    with socket.socket(family) as raw:
                        raw.settimeout(15)
                        raw.connect((address, tls_port))
                        with context.wrap_socket(raw, server_hostname="localhost") as tls:
                            lines = TlsLines(tls)
                            greeting = lines.readline()
                            self.assertTrue(greeting.startswith((b"200 ", b"201 ")), greeting)
                            self.assertTrue(lines.ask(b"CAPABILITIES").startswith(b"101 "))
                            self.assertEqual(lines.block()[0], b"VERSION 2\r\n")
                            self.assertTrue(lines.ask(b"QUIT").startswith(b"205 "))
            # Only the configured addresses are bound: no wildcard listener.
            with socket.socket(socket.AF_INET) as other:
                other.settimeout(5)
                reached = other.connect_ex(("127.0.0.2", port)) == 0
            self.assertFalse(reached, "a listener answered on 127.0.0.2")
            self.assertIsNone(process.poll(), "a client stopped the owner")
        finally:
            self.stop(process)

    def test_refusals_are_named_before_any_listener(self) -> None:
        cases = (("0.0.0.0", "LISTENER-UNSPECIFIED"),
                 ("::", "LISTENER-UNSPECIFIED"),
                 ("[::1], ::", "LISTENER-UNSPECIFIED"),
                 ("::ffff:1.2.3.4", "LISTENER-MAPPED"),
                 ("::ffff:127.0.0.1", "LISTENER-MAPPED"),
                 ("::1,[::1]", "LISTENER-DUPLICATE"),
                 ("127.0.0.1, [::1], 127.0.0.1", "LISTENER-DUPLICATE"),
                 ("::1, 0:0:0:0:0:0:0:1", "LISTENER-DUPLICATE"),
                 ("[::1]:119", "LISTENER-ADDRESS"))
        for host, reason in cases:
            with self.subTest(host=host):
                config = self.write_config(host, free_loopback_port(), free_loopback_port())
                process = self.start(config)
                try:
                    code = process.wait(timeout=180)
                    out = process.stdout.read()
                    err = process.stderr.read()
                finally:
                    self.stop(process)
                self.assertEqual(code, USAGE, (out, err))
                self.assertNotIn(b"LISTENING", out)
                named = "(CONFIGURATION {})".format(reason).encode()
                self.assertIn(named, out + err, (out, err))


if __name__ == "__main__":
    unittest.main()
