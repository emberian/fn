#!/usr/bin/env python3
"""Opt-in saved-image vertical for the mandatory hybrid author profile."""
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import unittest
from tests.native_process import wait_for_announcement, stop_and_diagnostics

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(os.environ.get("FN_RUN_HYBRID_E2E") == "1",
                     "set FN_RUN_HYBRID_E2E=1 for the OpenSSL 3.5 saved-image gate")
@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeHybridAuthorTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-hybrid-author-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.port = free_port()
        self.config = self.root / "fn.toml"
        initialized = self.invoke("store", str(self.store), "init", "fn.test", timeout=180)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.principal = self.root / "principal.bin"
        self.ed_public = self.root / "ed-public.bin"
        self.ed_secret = self.root / "ed-secret.bin"
        self.principal.write_bytes(bytes([85]) * 32)
        self.ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ml_private = self.root / "ml-private.pem"
        self.ml_public = self.root / "ml-public.pem"
        generated = subprocess.run(
            [OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(self.ml_private)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60, check=False)
        self.assertEqual(generated.returncode, 0,
                         "opted-in hybrid gate requires working ML-DSA-65: "
                         + generated.stderr.decode("utf-8", "replace"))
        subprocess.run([OPENSSL, "pkey", "-in", str(self.ml_private), "-pubout",
                        "-out", str(self.ml_public)], timeout=60, check=True)
        self.ml_private_b = self.root / "ml-private-b.pem"
        self.ml_public_b = self.root / "ml-public-b.pem"
        subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                        str(self.ml_private_b)], timeout=60, check=True)
        subprocess.run([OPENSSL, "pkey", "-in", str(self.ml_private_b), "-pubout",
                        "-out", str(self.ml_public_b)], timeout=60, check=True)

    def invoke(self, *args, timeout=60):
        return subprocess.run([str(IMAGE), "--fn", *args], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=timeout, check=False)

    def start_owner(self):
        proc = subprocess.Popen([str(IMAGE), "--fn", "operator", str(self.config), "run"],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        wait_for_announcement(proc, b"LISTENING ")
        return proc

    def stop_owner(self, proc):
        diagnostic = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostic)

    def test_enroll_author_refuse_tamper_and_restart_query(self):
        article = self.root / "article.eml"
        msgid = "<hybrid-native@example.invalid>"
        article.write_bytes(b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                            b"Subject: hybrid\r\nMessage-ID: " + msgid.encode() +
                            b"\r\n\r\nexact bytes\r\n")
        owner = self.start_owner()
        try:
            enrolled = self.invoke("hybrid-enroll", str(self.control), "1",
                                str(self.principal), str(self.ed_public), str(self.ml_public))
            self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
            signed = self.invoke("hybrid-sign", str(self.principal), str(self.ed_public),
                              str(self.ed_secret), str(self.ml_public), str(self.ml_private),
                              str(article))
            self.assertEqual(signed.returncode, 0, signed.stderr.decode())
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig, ml_sig = self.root / "ed.sig", self.root / "ml.sig"
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            bad = self.root / "bad-ml.sig"
            damaged = bytearray(ml_sig.read_bytes()); damaged[0] ^= 1; bad.write_bytes(damaged)
            common = [str(self.control), "1", str(article), str(ed_sig)]
            refused = self.invoke("hybrid-author", *(common + [str(bad), str(self.ml_public)]))
            self.assertEqual(refused.returncode, 1, refused.stderr.decode())
            accepted = self.invoke("hybrid-author", *(common + [str(ml_sig), str(self.ml_public)]))
            self.assertEqual(accepted.returncode, 0, accepted.stderr.decode())
            wrong_ed = self.root / "wrong-ed-public.bin"
            wrong_ed.write_bytes(bytes([99]) * 32)
            enrolled_b = self.invoke("hybrid-enroll", str(self.control), "2",
                                  str(self.principal), str(wrong_ed), str(self.ml_public_b))
            self.assertEqual(enrolled_b.returncode, 0, enrolled_b.stderr.decode())
            wrong_generation = self.invoke(
                "hybrid-author", str(self.control), "2", str(article), str(ed_sig),
                str(ml_sig), str(self.ml_public_b))
            self.assertEqual(wrong_generation.returncode, 1,
                             wrong_generation.stderr.decode())
        finally:
            self.stop_owner(owner)
        owner = self.start_owner()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(("ARTICLE {}\r\n".format(msgid)).encode())
                    self.assertTrue(stream.readline().startswith(b"220 "))
                    returned = bytearray()
                    while True:
                        line = stream.readline()
                        self.assertTrue(line, "ARTICLE response ended before dot terminator")
                        if line == b".\r\n":
                            break
                        returned.extend(line[1:] if line.startswith(b"..") else line)
                    self.assertEqual(bytes(returned), article.read_bytes())
        finally:
            self.stop_owner(owner)


if __name__ == "__main__":
    unittest.main()
