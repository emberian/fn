"""Real OpenSSL primitive over bounded BIOs; ephemeral local credentials only.

Build with host/build-tls.sh, then set FN2_TLS_LIBRARY to the resulting library.
These controls test transport, not the ACL2 STARTTLS machine or socket adapter.
"""
import ctypes as c
import os
from pathlib import Path
import ssl
import subprocess
import tempfile
import unittest


class TlsPrimitive(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="fn2-tls-")
        cls.addClassCleanup(cls.tmp.cleanup)
        directory = Path(cls.tmp.name)
        cert, key = directory / "cert.pem", directory / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "ec", "-pkeyopt",
                        "ec_paramgen_curve:prime256v1", "-nodes", "-days", "1",
                        "-subj", "/CN=localhost", "-keyout", str(key), "-out", str(cert)],
                       check=True, capture_output=True, timeout=15)
        cls.lib = c.CDLL(os.environ["FN2_TLS_LIBRARY"])
        declarations = {
            "config": ([c.c_char_p, c.c_char_p, c.c_int], c.c_void_p),
            "config_free": ([c.c_void_p], None),
            "new": ([c.c_void_p, c.c_size_t], c.c_void_p),
            "free": ([c.c_void_p], None),
            "handshake": ([c.c_void_p], c.c_int),
            "feed": ([c.c_void_p, c.c_void_p, c.c_size_t], c.c_int),
            "drain": ([c.c_void_p, c.c_void_p, c.c_size_t], c.c_int),
            "output_pending": ([c.c_void_p], c.c_size_t),
            "input_room": ([c.c_void_p], c.c_size_t),
            "read": ([c.c_void_p, c.c_void_p, c.c_size_t, c.POINTER(c.c_size_t)], c.c_int),
            "write": ([c.c_void_p, c.c_void_p, c.c_size_t, c.POINTER(c.c_size_t)], c.c_int),
        }
        for name, (arguments, result) in declarations.items():
            function = getattr(cls.lib, "fn2_tls_" + name)
            function.argtypes, function.restype = arguments, result
        cls.config = cls.lib.fn2_tls_config(os.fsencode(cert), os.fsencode(key), 0x0303)
        if not cls.config:
            raise AssertionError("ephemeral OpenSSL server configuration failed")
        cls.addClassCleanup(cls.lib.fn2_tls_config_free, cls.config)

    def setUp(self):
        self.capacity = 512
        self.server = self.lib.fn2_tls_new(self.config, self.capacity)
        self.assertTrue(self.server)
        self.addCleanup(self.lib.fn2_tls_free, self.server)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        context.check_hostname = False
        context.verify_mode = ssl.CERT_NONE
        context.minimum_version = ssl.TLSVersion.TLSv1_2
        self.incoming, self.outgoing = ssl.MemoryBIO(), ssl.MemoryBIO()
        self.client = context.wrap_bio(self.incoming, self.outgoing,
                                      server_side=False, server_hostname="localhost")
        self.pending = b""

    def transfer(self):
        self.pending += self.outgoing.read()
        if self.pending:
            n = self.lib.fn2_tls_feed(self.server, self.pending, min(73, len(self.pending)))
            self.assertGreaterEqual(n, 0)
            self.assertLessEqual(n, min(73, len(self.pending)))
            self.pending = self.pending[n:]
        buffer = c.create_string_buffer(61)
        n = self.lib.fn2_tls_drain(self.server, buffer, len(buffer))
        self.assertGreaterEqual(n, 0)
        self.assertLessEqual(n, len(buffer))
        if n:
            self.incoming.write(buffer.raw[:n])
        self.assertLessEqual(self.lib.fn2_tls_output_pending(self.server), self.capacity)
        self.assertLessEqual(self.lib.fn2_tls_input_room(self.server), self.capacity)

    def handshake(self):
        client_done = server_done = False
        for _ in range(10000):
            if not client_done:
                try:
                    self.client.do_handshake()
                    client_done = True
                except (ssl.SSLWantReadError, ssl.SSLWantWriteError):
                    pass
            self.transfer()
            if not server_done:
                code = self.lib.fn2_tls_handshake(self.server)
                self.assertIn(code, (0, 1, 2))
                server_done = code == 0
            self.transfer()
            if client_done and server_done and not self.pending and not self.lib.fn2_tls_output_pending(self.server):
                return
        self.fail("bounded fixture exhausted handshake steps")

    def test_fragmented_handshake_and_encrypted_application_roundtrip(self):
        self.handshake()
        request = b"CAPABILITIES\r\n"
        self.client.write(request)
        got = b""
        buffer, count = c.create_string_buffer(5), c.c_size_t()
        for _ in range(1000):
            self.transfer()
            code = self.lib.fn2_tls_read(self.server, buffer, len(buffer), c.byref(count))
            self.assertIn(code, (0, 1, 2))
            got += buffer.raw[:count.value]
            if got == request:
                break
        self.assertEqual(got, request)
        reply = b"101 Capabilities\r\nVERSION 2\r\n.\r\n"
        received = b""
        wrote = False
        for _ in range(1000):
            if not wrote:
                code = self.lib.fn2_tls_write(self.server, reply, len(reply), c.byref(count))
                self.assertIn(code, (0, 1, 2))
                if code == 0:
                    self.assertEqual(count.value, len(reply))
                    wrote = True
            self.transfer()
            try:
                received += self.client.read(7)
            except (ssl.SSLWantReadError, ssl.SSLWantWriteError):
                pass
            if received == reply:
                break
        self.assertEqual(received, reply)

    def test_input_backpressure_and_malformed_handshake(self):
        data = b"not TLS" * 200
        n = self.lib.fn2_tls_feed(self.server, data, len(data))
        self.assertEqual(n, self.capacity)
        self.assertEqual(self.lib.fn2_tls_input_room(self.server), 0)
        self.assertEqual(self.lib.fn2_tls_feed(self.server, data, len(data)), 0)
        self.assertEqual(self.lib.fn2_tls_handshake(self.server), 4)

    def test_invalid_config_and_empty_capacity_refuse(self):
        self.assertFalse(self.lib.fn2_tls_config(b"/missing/fn2-cert", b"/missing/fn2-key", 0x0303))
        self.assertFalse(self.lib.fn2_tls_new(self.config, 0))


if __name__ == "__main__":
    unittest.main()
