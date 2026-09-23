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
import threading


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

    def _encrypted_certificate(self, directory: Path) -> tuple[Path, Path]:
        certificate = directory / "encrypted-certificate.pem"
        private_key = directory / "encrypted-private-key.pem"
        subprocess.run(
            [
                "openssl", "req", "-x509", "-newkey", "rsa:2048",
                "-keyout", str(private_key), "-out", str(certificate),
                "-sha256", "-days", "1", "-passout", "pass:not-stdin",
                "-subj", "/CN=localhost",
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
            encrypted_certificate, encrypted_key = self._encrypted_certificate(directory)
            environment = os.environ.copy()
            environment.update(
                FN_TLS_TEST_CERT=str(certificate),
                FN_TLS_TEST_KEY=str(private_key),
                FN_TLS_TEST_WRONG_KEY=str(wrong_key),
                FN_TLS_TEST_ENCRYPTED_CERT=str(encrypted_certificate),
                FN_TLS_TEST_ENCRYPTED_KEY=str(encrypted_key),
            )
            process = subprocess.Popen(
                [sbcl, "--noinform", "--disable-debugger", "--script",
                 "tests/native_tls_transport.lisp"],
                cwd=ROOT,
                env=environment,
                text=True,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                bufsize=1,
            )
            assert process.stdout is not None
            assert process.stdin is not None
            process.stdin.write("stdin-sentinel\n")
            process.stdin.flush()
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
                        for line in process.stdout:
                            lines.append(line)
                            if line.startswith("TLS-READY"):
                                break
                        self.assertIn("TLS-READY\n", lines)
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

    def _run_client_case(self, certificate: Path, private_key: Path,
                         anchor: Path, name: str, expect: str,
                         interrupt: bool = False) -> subprocess.CompletedProcess:
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(certificate, private_key)
        listener = socket.socket()
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        def serve() -> None:
            try:
                raw, _ = listener.accept()
                with raw:
                    if interrupt:
                        return
                    try:
                        with context.wrap_socket(raw, server_side=True) as protected:
                            if protected.recv(64) == b"PING\r\n":
                                protected.sendall(b"PONG\r\n")
                    except ssl.SSLError:
                        pass
            finally:
                listener.close()
        worker = threading.Thread(target=serve, daemon=True)
        worker.start()
        environment = os.environ.copy()
        environment.update(FN_TLS_CLIENT_PORT=str(listener.getsockname()[1]),
                           FN_TLS_CLIENT_CA=str(anchor), FN_TLS_CLIENT_NAME=name,
                           FN_TLS_CLIENT_EXPECT=expect)
        result = subprocess.run([shutil.which("sbcl"), "--noinform", "--disable-debugger",
                                 "--script", "tests/native_tls_client.lisp"], cwd=ROOT,
                                env=environment, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, timeout=15)
        worker.join(timeout=5)
        return result

    def test_client_chain_and_hostname_verification(self) -> None:
        self.assertIsNotNone(shutil.which("sbcl"))
        with tempfile.TemporaryDirectory(prefix="fn-native-tls-client-") as raw:
            directory = Path(raw)
            certificate, key = self._certificate(directory, "server")
            wrong_certificate, _ = self._certificate(directory, "wrong")
            good = self._run_client_case(certificate, key, certificate, "localhost", "success")
            self.assertEqual(good.returncode, 0, good.stdout)
            self.assertIn("TLS-CLIENT-PASSED", good.stdout)
            wrong_name = self._run_client_case(certificate, key, certificate,
                                               "elsewhere.invalid", "failure")
            self.assertEqual(wrong_name.returncode, 0, wrong_name.stdout)
            self.assertIn("TLS-CLIENT-REFUSED", wrong_name.stdout)
            wrong_chain = self._run_client_case(certificate, key, wrong_certificate,
                                                "localhost", "failure")
            self.assertEqual(wrong_chain.returncode, 0, wrong_chain.stdout)
            interrupted = self._run_client_case(certificate, key, certificate,
                                                "localhost", "failure", interrupt=True)
            self.assertEqual(interrupted.returncode, 0, interrupted.stdout)
            self.assertIn("TLS-CLIENT-REFUSED", interrupted.stdout)


if __name__ == "__main__":
    unittest.main()
