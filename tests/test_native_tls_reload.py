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
import ssl
import subprocess
import unittest

from tests.native_harness import EXIT, ROOT, Client, Node, native_image, requires

PRODUCTION = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


class TlsReloadCases:
    IMAGE: Path

    def setUp(self) -> None:
        self.node = Node(self, self.IMAGE)
        self.root, self.port = self.node.root, self.node.port
        self.node.store("init", "fn.test", expect=EXIT.OK)
        self.tls = self.root / "tls"
        self.tls.mkdir()
        self.certificate = self.tls / "cert.pem"
        self.private_key = self.tls / "key.pem"
        self.a = self.make_pair("a", "localhost")
        self.install(*self.a)
        self.node.write_config(extra='tls_cert = "{}"\ntls_key = "{}"\n'.format(
            self.certificate, self.private_key), protected_only=True)

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
        return self.node.operator(*argv)

    def protected(self) -> ssl.SSLSocket:
        client = Client(self.port, timeout=15, server_hostname="localhost")
        self.assertTrue(client.starttls().startswith(b"382 "))
        self.addCleanup(client.close, quit=False)
        return client

    @staticmethod
    def der(certificate: Path) -> bytes:
        return ssl.PEM_cert_to_DER_cert(certificate.read_text())

    def served(self) -> bytes:
        tls = self.protected()
        served = tls.sock.getpeercert(binary_form=True)
        self.assertTrue(tls.command(b"DATE").startswith(b"111 "))
        tls.send(b"QUIT\r\n")
        return served

    def status_tls_line(self) -> str:
        result = self.operator("status")
        self.assertEqual(result.returncode, EXIT.OK, result.stdout + result.stderr)
        lines = [l for l in result.stdout.decode().splitlines() if l.startswith("tls ")]
        self.assertEqual(len(lines), 1, result.stdout)
        return lines[0]

    def test_reload_serves_new_connections_and_keeps_open_sessions(self) -> None:
        process = self.node.start()
        before = self.protected()
        self.assertEqual(before.sock.getpeercert(binary_form=True), self.der(self.a[0]))
        self.assertRegex(self.status_tls_line(),
                         r"^tls names=localhost not-after=\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ$")

        b = self.make_pair("b", "localhost", "reload.localhost")
        self.install(*b)
        # Before the reload the owner still serves A from memory.
        self.assertEqual(self.served(), self.der(self.a[0]))
        reloaded = self.operator("tls", "reload")
        self.assertEqual(reloaded.returncode, EXIT.OK, reloaded.stdout + reloaded.stderr)
        self.assertIn(b"tls names=localhost,reload.localhost not-after=", reloaded.stdout)
        self.assertIn(b"accepted operator tls", reloaded.stderr)
        self.assertEqual(self.served(), self.der(b[0]))
        # The session opened on A still carries NNTP.
        self.assertTrue(before.command(b"DATE").startswith(b"111 "))
        self.assertTrue(self.status_tls_line().startswith(
            "tls names=localhost,reload.localhost not-after="))

        # A key that does not match the chain: refused by name, B still served.
        _, wrong_key = self.make_pair("c", "localhost")
        self.install(b[0], wrong_key)
        refused = self.operator("tls", "reload")
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stdout + refused.stderr)
        self.assertIn(b"refused operator tls key-mismatch", refused.stderr)
        self.assertIn(b"tls names=localhost,reload.localhost", refused.stdout)
        self.assertEqual(self.served(), self.der(b[0]))

        # A certificate that drops a served name: refused, B still served.
        self.install(*self.make_pair("d", "localhost"))
        dropped = self.operator("tls", "reload")
        self.assertEqual(dropped.returncode, EXIT.REFUSED, dropped.stdout + dropped.stderr)
        self.assertIn(b"refused operator tls names-dropped", dropped.stderr)
        self.assertEqual(self.served(), self.der(b[0]))

        self.assertTrue(before.command(b"QUIT").startswith(b"205 "))
        self.assertIsNone(process.poll(), "the owner stopped")

    def test_reload_without_an_owner_is_not_accepted(self) -> None:
        result = self.operator("tls", "reload")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn(b"accepted operator tls", result.stderr)


@requires(PRODUCTION)
class ProductionTlsReloadTests(TlsReloadCases, unittest.TestCase):
    IMAGE = PRODUCTION


@requires(DEVELOPER)
class DeveloperTlsReloadTests(TlsReloadCases, unittest.TestCase):
    IMAGE = DEVELOPER


if __name__ == "__main__":
    unittest.main()
