#!/usr/bin/env python3
"""Real OpenSSL native TLS facility test, including peer failure isolation."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import socket
import ssl
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class NativeTlsTransportTest(unittest.TestCase):
    def _certificate(self, directory: Path, name: str) -> tuple[Path, Path]:
        certificate = directory / f"{name}-certificate.pem"
        private_key = directory / f"{name}-private-key.pem"
        subprocess.run(
            [
                "openssl", "req", "-x509", "-newkey", "rsa:2048",
                "-keyout", str(private_key), "-out", str(certificate),
                "-sha256", "-days", "1", "-nodes", "-subj", "/CN=localhost",
            ],
            cwd=ROOT,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return certificate, private_key

    def test_context_handshake_failure_and_roundtrip(self) -> None:
        sbcl = shutil.which("sbcl")
        openssl = shutil.which("openssl")
        self.assertIsNotNone(sbcl, "SBCL is required for the native TLS test")
        self.assertIsNotNone(openssl, "OpenSSL CLI is required for test certificates")
        with tempfile.TemporaryDirectory(prefix="fn-native-tls-") as raw:
            directory = Path(raw)
            certificate, private_key = self._certificate(directory, "server")
            _, wrong_key = self._certificate(directory, "wrong")
            environment = os.environ.copy()
            environment.update(
                FN_TLS_TEST_CERT=str(certificate),
                FN_TLS_TEST_KEY=str(private_key),
                FN_TLS_TEST_WRONG_KEY=str(wrong_key),
            )
            process = subprocess.Popen(
                [sbcl, "--noinform", "--disable-debugger", "--script",
                 "tests/native_tls_transport.lisp"],
                cwd=ROOT,
                env=environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                bufsize=1,
            )
            assert process.stdout is not None
            lines: list[str] = []
            port: int | None = None
            try:
                for line in process.stdout:
                    lines.append(line)
                    if line.startswith("PORT "):
                        port = int(line.split()[1])
                        break
                self.assertIsNotNone(port, "native TLS server did not publish its port")

                with socket.create_connection(("127.0.0.1", port), timeout=5) as raw_peer:
                    raw_peer.sendall(b"not a TLS ClientHello\r\n")

                for line in process.stdout:
                    lines.append(line)
                    if line.startswith("FAILURE-ISOLATED"):
                        break
                self.assertIn("FAILURE-ISOLATED\n", lines)

                context = ssl.create_default_context()
                context.check_hostname = False
                context.verify_mode = ssl.CERT_NONE
                context.minimum_version = ssl.TLSVersion.TLSv1_2
                with socket.create_connection(("127.0.0.1", port), timeout=5) as raw_peer:
                    with context.wrap_socket(raw_peer, server_hostname="localhost") as protected:
                        protected.sendall(b"CAPABILITIES\r\n")
                        self.assertEqual(protected.recv(64), b"200 ok\r\n")

                remainder = process.communicate(timeout=10)[0]
                lines.append(remainder)
                self.assertEqual(process.returncode, 0, "".join(lines))
                self.assertIn("ROUNDTRIP-PASSED", "".join(lines))
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()


if __name__ == "__main__":
    unittest.main()

