#!/usr/bin/env python3
"""Opt-in relocated frozen-image TLS, ML-DSA, and missing-bundle witness."""
import os
from pathlib import Path
import shutil
import socket
import ssl
import subprocess
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement


IMAGE = Path(os.environ.get("FN_NATIVE_HOST", "/nonexistent/fn-host"))
BUILD_OPENSSL = Path(os.environ.get("FN_BUILD_OPENSSL_PREFIX", "/nonexistent/build-openssl"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")


def invoke(image, *args, timeout=120):
    return subprocess.run([str(image), "--fn", *args], stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout, check=False)


@unittest.skipUnless(os.environ.get("FN_RUN_RELOCATION_E2E") == "1",
                     "set FN_RUN_RELOCATION_E2E=1 for a copied frozen image")
class FrozenRelocationTest(unittest.TestCase):
    def setUp(self):
        self.assertTrue(IMAGE.is_file() and os.access(IMAGE, os.X_OK))
        self.assertFalse(BUILD_OPENSSL.exists(),
                         "build-time OpenSSL path must be unavailable here")
        self.assertTrue((IMAGE.parent / "image.sha256").is_file())
        self.temp = tempfile.TemporaryDirectory(prefix="fn-frozen-relocation-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_relocated_image_uses_bundled_tls_and_ml_dsa(self):
        integrity = subprocess.run(["sha256sum", "-c", "image.sha256"],
                                   cwd=IMAGE.parent, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, timeout=120, check=False)
        self.assertEqual(integrity.returncode, 0, integrity.stderr.decode())
        store = self.root / "store"
        initialized = invoke(IMAGE, "store", str(store), "init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())

        principal = self.root / "principal.bin"
        ed_public = self.root / "ed-public.bin"
        ed_secret = self.root / "ed-secret.bin"
        article = self.root / "article.eml"
        ml_private = self.root / "ml-private.pem"
        ml_public = self.root / "ml-public.pem"
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        article.write_bytes(b"From: test@example.invalid\r\nNewsgroups: fn.test\r\n"
                            b"Subject: relocation\r\nMessage-ID: <relocation@example.invalid>\r\n"
                            b"\r\nexact octets\r\n")
        for argv in ([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(ml_private)],
                     [OPENSSL, "pkey", "-in", str(ml_private), "-pubout", "-out", str(ml_public)]):
            generated = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       timeout=60, check=False)
            self.assertEqual(generated.returncode, 0, generated.stderr.decode())
        signed = invoke(IMAGE, "hybrid-sign", str(principal), str(ed_public),
                        str(ed_secret), str(ml_public), str(ml_private), str(article))
        self.assertEqual(signed.returncode, 0, signed.stderr.decode())
        lines = dict(line.split() for line in signed.stdout.decode().splitlines())
        self.assertEqual(len(bytes.fromhex(lines["ed25519"])), 64)
        self.assertGreater(len(bytes.fromhex(lines["ml-dsa-65"])), 2000)

        cert, key = self.root / "cert.pem", self.root / "key.pem"
        generated = subprocess.run(
            [OPENSSL, "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256",
             "-days", "1", "-subj", "/CN=localhost", "-keyout", str(key),
             "-out", str(cert)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=60, check=False)
        self.assertEqual(generated.returncode, 0, generated.stderr.decode())
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        config = self.root / "fn.toml"
        config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
                          'port = {}\ntls_cert = "{}"\ntls_key = "{}"\n'
                          '[control]\npath = "{}"\n'.format(
                              store, port, cert, key, self.root / "control.sock"),
                          encoding="ascii")
        owner = subprocess.Popen([str(IMAGE), "--fn", "operator", str(config), "run"],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            wait_for_announcement(owner, b"LISTENING ")
            with socket.create_connection(("127.0.0.1", port), timeout=15) as raw:
                greeting = raw.recv(1024)
                self.assertTrue(greeting.startswith((b"200 ", b"201 ")), greeting)
                raw.sendall(b"STARTTLS\r\n")
                self.assertTrue(raw.recv(1024).startswith(b"382 "))
                context = ssl.create_default_context(cafile=str(cert))
                with context.wrap_socket(raw, server_hostname="localhost") as protected:
                    protected.sendall(b"CAPABILITIES\r\n")
                    self.assertTrue(protected.recv(1024).startswith(b"101 "))
        finally:
            diagnostic = stop_and_diagnostics(owner, timeout=60)
            self.assertEqual(owner.returncode, 0, diagnostic)

    def test_missing_bundled_openssl_refuses_startup(self):
        # Symlink only immutable runtime/core files into a separate launcher
        # directory. The launcher resolves its OpenSSL prefix beside itself.
        missing = self.root / "missing-pair"
        missing.mkdir()
        shutil.copy2(IMAGE, missing / IMAGE.name)
        (missing / (IMAGE.name + ".core")).symlink_to(IMAGE.parent / (IMAGE.name + ".core"))
        (missing / "runtime").symlink_to(IMAGE.parent / "runtime", target_is_directory=True)
        (missing / "lib").symlink_to(IMAGE.parent / "lib", target_is_directory=True)
        (missing / "openssl" / "lib").mkdir(parents=True)
        # A refused start is exit 5 with its reason on stderr, whatever stdin
        # is: closed, or a pipe held open as a supervisor or a shell holds it.
        # Until the startup checks ran under a handler, it printed the ACL2
        # prompt and waited on stdin (native-subsets 47bdb9a4, failure 5).
        for label, stdin in (("stdin closed", subprocess.DEVNULL),
                             ("stdin held open", subprocess.PIPE)):
            with self.subTest(label):
                store = self.root / "bad-store-{}".format(stdin)
                out_path = self.root / "refused-{}.out".format(stdin)
                err_path = self.root / "refused-{}.err".format(stdin)
                with open(out_path, "wb") as out_file, open(err_path, "wb") as err_file:
                    proc = subprocess.Popen(
                        [str(missing / IMAGE.name), "--fn", "store", str(store),
                         "init", "fn.test"],
                        stdin=stdin, stdout=out_file, stderr=err_file)
                    try:
                        proc.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait()
                        self.fail("refused start still running after 10 s ({}): {}".format(
                            label, err_path.read_bytes()[-500:]))
                    finally:
                        if proc.stdin:
                            proc.stdin.close()
                out, err = out_path.read_bytes(), err_path.read_bytes()
                self.assertEqual(proc.returncode, 5, (label, out, err))
                self.assertEqual(out, b"", label)
                self.assertIn(b"refused start", err)
                self.assertIn(b"OpenSSL", err)
                self.assertFalse(store.exists())


if __name__ == "__main__":
    unittest.main()
