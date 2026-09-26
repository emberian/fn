#!/usr/bin/env python3
"""SCN-143 (HST-020, PRF-212): `operator CONFIG tls reload' on a running owner.

The owner starts with certificate A.  A session opens and handshakes; the
files are replaced by a second self-signed pair B and `tls reload' is asked
over the control socket: it is accepted, the next handshake is served B, and
the session opened before still answers on A's context.  `status' prints the
served names and notAfter.  Then the key file is replaced by a key that does
not match the chain: `tls reload' is refused by name (key-mismatch, exit 1)
and new handshakes are still served B; a certificate that drops a served name
is refused (names-dropped) the same way.  The module runs against both images
the release builds: the production image (FN_NATIVE_HOST) and the developer
image (FN_NATIVE_DEVELOPER_HOST).  Refuted: a restart, a new handshake served
the old certificate after an accepted reload, a closed or failing older
session, a refusal that changed what is served, or a refusal without its name.
"""

from __future__ import annotations

import os
from pathlib import Path
import socket
import ssl
import subprocess
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
DEVELOPER = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                                ROOT / "build" / "fn-host-developer"))


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


def recv_line(peer) -> bytes:
    buffered = b""
    while not buffered.endswith(b"\r\n"):
        piece = peer.recv(1)
        if not piece:
            raise EOFError("connection ended before an NNTP line")
        buffered += piece
    return buffered


def client_context() -> ssl.SSLContext:
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    return context


class TlsReloadCases:
    IMAGE: Path

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-tls-reload-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.tls = self.root / "tls"
        self.tls.mkdir()
        self.control = self.root / "control.sock"
        self.port = free_loopback_port()
        initialized = subprocess.run(
            [str(self.IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, env=environment(), capture_output=True, timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.certificate = self.tls / "cert.pem"
        self.private_key = self.tls / "key.pem"
        self.a = self.make_pair("a", "localhost")
        self.install(*self.a)
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n\n[auth]\nprotected_only = true\n\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.certificate,
                                             self.private_key, self.control),
            encoding="ascii")

    def make_pair(self, name: str, *dns: str) -> tuple[Path, Path]:
        certificate = self.root / (name + "-cert.pem")
        private_key = self.root / (name + "-key.pem")
        subprocess.run(
            ["openssl", "req", "-x509", "-newkey", "ec", "-pkeyopt",
             "ec_paramgen_curve:P-256", "-keyout", str(private_key),
             "-out", str(certificate), "-sha256", "-days", "2", "-nodes",
             "-subj", "/CN=" + dns[0],
             "-addext", "subjectAltName=" + ",".join("DNS:" + d for d in dns)],
            cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            timeout=60, check=True)
        return certificate, private_key

    def install(self, certificate: Path, private_key: Path) -> None:
        """Replace the served paths the way fn-cert-install.sh does: a
        sibling temporary file renamed over each."""
        for source, target in ((certificate, self.certificate),
                               (private_key, self.private_key)):
            staged = target.with_suffix(".new")
            staged.write_bytes(source.read_bytes())
            os.replace(staged, target)

    def operator(self, *argv: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [str(self.IMAGE), "--fn", "operator", str(self.config), *argv],
            cwd=ROOT, env=environment(), capture_output=True, timeout=180, check=False)

    def start(self) -> subprocess.Popen[bytes]:
        process = subprocess.Popen(
            [str(self.IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        line = wait_for_announcement(process, b"LISTENING ")
        if line != "LISTENING {}\n".format(self.port).encode():
            self.fail("owner failed: {!r} {}".format(line, stop_and_diagnostics(process)))
        self.addCleanup(self.stop, process)
        return process

    def stop(self, process: subprocess.Popen[bytes]) -> None:
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            if stream is not None:
                stream.close()

    def protected(self) -> ssl.SSLSocket:
        peer = socket.create_connection(("127.0.0.1", self.port), timeout=15)
        peer.settimeout(15)
        greeting = recv_line(peer)
        self.assertTrue(greeting[:3] in (b"200", b"201"), greeting)
        peer.sendall(b"STARTTLS\r\n")
        self.assertTrue(recv_line(peer).startswith(b"382 "))
        tls = client_context().wrap_socket(peer, server_hostname="localhost")
        self.addCleanup(tls.close)
        return tls

    @staticmethod
    def der(certificate: Path) -> bytes:
        return ssl.PEM_cert_to_DER_cert(certificate.read_text())

    def served(self) -> bytes:
        tls = self.protected()
        served = tls.getpeercert(binary_form=True)
        tls.sendall(b"DATE\r\n")
        self.assertTrue(recv_line(tls).startswith(b"111 "))
        tls.sendall(b"QUIT\r\n")
        return served

    def status_tls_line(self) -> str:
        result = self.operator("status")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        lines = [l for l in result.stdout.decode().splitlines() if l.startswith("tls ")]
        self.assertEqual(len(lines), 1, result.stdout)
        return lines[0]

    def test_reload_serves_new_connections_and_keeps_open_sessions(self) -> None:
        process = self.start()
        before = self.protected()
        self.assertEqual(before.getpeercert(binary_form=True), self.der(self.a[0]))
        self.assertRegex(self.status_tls_line(),
                         r"^tls names=localhost not-after=\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ$")

        b = self.make_pair("b", "localhost", "reload.localhost")
        self.install(*b)
        # Before the reload the owner still serves A from memory.
        self.assertEqual(self.served(), self.der(self.a[0]))
        reloaded = self.operator("tls", "reload")
        self.assertEqual(reloaded.returncode, 0, reloaded.stdout + reloaded.stderr)
        self.assertIn(b"tls names=localhost,reload.localhost not-after=", reloaded.stdout)
        self.assertIn(b"accepted operator tls", reloaded.stderr)
        self.assertEqual(self.served(), self.der(b[0]))
        # The session opened on A still carries NNTP.
        before.sendall(b"DATE\r\n")
        self.assertTrue(recv_line(before).startswith(b"111 "))
        self.assertTrue(self.status_tls_line().startswith(
            "tls names=localhost,reload.localhost not-after="))

        # A key that does not match the chain: refused by name, B still served.
        _, wrong_key = self.make_pair("c", "localhost")
        self.install(b[0], wrong_key)
        refused = self.operator("tls", "reload")
        self.assertEqual(refused.returncode, 1, refused.stdout + refused.stderr)
        self.assertIn(b"refused operator tls key-mismatch", refused.stderr)
        self.assertIn(b"tls names=localhost,reload.localhost", refused.stdout)
        self.assertEqual(self.served(), self.der(b[0]))

        # A certificate that drops a served name: refused, B still served.
        self.install(*self.make_pair("d", "localhost"))
        dropped = self.operator("tls", "reload")
        self.assertEqual(dropped.returncode, 1, dropped.stdout + dropped.stderr)
        self.assertIn(b"refused operator tls names-dropped", dropped.stderr)
        self.assertEqual(self.served(), self.der(b[0]))

        before.sendall(b"QUIT\r\n")
        self.assertTrue(recv_line(before).startswith(b"205 "))
        self.assertIsNone(process.poll(), "the owner stopped")

    def test_reload_without_an_owner_is_not_accepted(self) -> None:
        result = self.operator("tls", "reload")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn(b"accepted operator tls", result.stderr)


@unittest.skipUnless(PRODUCTION.is_file() and os.access(PRODUCTION, os.X_OK),
                     "the production image (FN_NATIVE_HOST) is required")
class ProductionTlsReloadTests(TlsReloadCases, unittest.TestCase):
    IMAGE = PRODUCTION


@unittest.skipUnless(DEVELOPER.is_file() and os.access(DEVELOPER, os.X_OK),
                     "the developer image (FN_NATIVE_DEVELOPER_HOST) is required")
class DeveloperTlsReloadTests(TlsReloadCases, unittest.TestCase):
    IMAGE = DEVELOPER


if __name__ == "__main__":
    unittest.main()
