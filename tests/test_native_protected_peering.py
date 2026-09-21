"""Opt-in reciprocal STARTTLS+AUTHINFO native peering witness.

Both peers are saved-image owner processes. Python creates private credentials,
certificates and configuration, starts the processes, and observes public NNTP.
"""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
import unittest

from tests import test_native_peering as peer

ACTUAL_CORE = peer.ACTUAL_CORE
ACTUAL_LAUNCHER = peer.ACTUAL_LAUNCHER
IMAGE = peer.IMAGE
READY = peer.READY
ROOT = peer.ROOT
SOURCE = peer.SOURCE
free_port = peer.free_port


@unittest.skipUnless(READY, "set explicit source-matched native image and hashes")
class NativeProtectedPeeringTests(unittest.TestCase):
    command = peer.NativePeeringTests.command
    start = peer.NativePeeringTests.start
    stop_all = peer.NativePeeringTests.stop_all
    article = staticmethod(peer.NativePeeringTests.article)
    post = peer.NativePeeringTests.post
    article_from = peer.NativePeeringTests.article_from
    await_article = peer.NativePeeringTests.await_article
    duplicate_offer = peer.NativePeeringTests.duplicate_offer
    capabilities = peer.NativePeeringTests.capabilities

    @classmethod
    def setUpClass(cls):
        print("native-protected-peering launcher-sha256={} core-sha256={} source={}".format(
            ACTUAL_LAUNCHER, ACTUAL_CORE, SOURCE))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-protected-peer-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.processes = []
        self.addCleanup(self.stop_all)

    def make_certificate(self, root, name):
        certificate = root / (name + "-certificate.pem")
        key = root / (name + "-key.pem")
        result = subprocess.run(
            ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
             "-sha256", "-days", "1", "-subj", "/CN=localhost",
             "-keyout", str(key), "-out", str(certificate)],
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return certificate, key

    def initialize(self, name, port, login, password):
        root = self.base / name
        root.mkdir()
        store = root / "store"
        control = root / "control.sock"
        auth = root / "auth.toml"
        certificate, key = self.make_certificate(root, name)
        self.command([IMAGE, "--fn", "store", store, "init", "fn.test"])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = true\npath = "{}"\n'.format(
                store, port, certificate, key, control, auth), encoding="ascii")
        enrolled = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(config), "principal",
             "set-password", login, "--posting"], cwd=ROOT, env=self.env,
            input=(password + "\n" + password + "\n").encode(),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
        listed = self.command([IMAGE, "--fn", "operator", config,
                               "principal", "list"]).stdout.decode("ascii")
        matches = re.findall(r"[0-9a-f]{64}", listed)
        self.assertEqual(len(matches), 1, listed)
        return {"name": name, "root": root, "store": store, "control": control,
                "config": config, "port": port, "certificate": certificate,
                "principal": matches[0], "login": login, "password": password}

    def profile(self, source, target, password=None):
        path = source["root"] / (target["name"] + ".fnauth")
        path.write_bytes(("FNAUTH1\n{}\n{}\n".format(
            target["login"], password or target["password"])).encode("ascii"))
        path.chmod(0o600)
        return path

    def configure_peer(self, source, target, profile, anchor=None):
        self.command([
            IMAGE, "--fn", "operator", source["config"], "peer", "add",
            target["name"], target["name"] + ".example.invalid", "127.0.0.1",
            str(target["port"]), "fn.*", "fn.*", "principal",
            source["principal"], profile, "false", "true", "starttls",
            "localhost", anchor or target["certificate"],
        ])

    def assert_not_received(self, node, message_id, seconds=3):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            self.assertIsNone(self.article_from(node, message_id))
            time.sleep(0.1)

    def test_reciprocal_starttls_authinfo_transfer_and_reconnect(self):
        a = self.initialize("protected-a", free_port(), "b-at-a", "b-secret")
        b = self.initialize("protected-b", free_port(), "a-at-b", "a-secret")
        self.configure_peer(a, b, self.profile(a, b))
        self.configure_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)

        for source, target, label in ((a, b, "a-to-b"), (b, a, "b-to-a")):
            message_id = "<protected-{}@example.invalid>".format(label)
            self.post(source, message_id, label)
            self.assertEqual(self.await_article(target, message_id),
                             self.await_article(source, message_id))
            self.assertTrue(self.duplicate_offer(target, message_id).startswith(b"480 "))

        # Drop both processes after durable acknowledgements, then demonstrate
        # fresh TLS and AUTHINFO sessions in both directions after restart.
        self.stop_all()
        self.start(a)
        self.start(b)
        for source, target, label in ((a, b, "a-reconnect"), (b, a, "b-reconnect")):
            message_id = "<protected-{}@example.invalid>".format(label)
            self.post(source, message_id, label)
            self.assertEqual(self.await_article(target, message_id),
                             self.await_article(source, message_id))

    def test_bad_outbound_password_never_falls_back_to_cleartext(self):
        a = self.initialize("bad-auth-a", free_port(), "b-at-a", "b-secret")
        b = self.initialize("bad-auth-b", free_port(), "a-at-b", "a-secret")
        self.configure_peer(a, b, self.profile(a, b, password="wrong"))
        self.configure_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)
        message_id = "<protected-bad-password@example.invalid>"
        self.post(a, message_id, "bad-password")
        self.assert_not_received(b, message_id)
        self.assertIsNone(a["process"].poll())
        self.assertIsNone(b["process"].poll())

    def test_untrusted_certificate_keeps_durable_feed_pending(self):
        a = self.initialize("bad-cert-a", free_port(), "b-at-a", "b-secret")
        b = self.initialize("bad-cert-b", free_port(), "a-at-b", "a-secret")
        unrelated, _ = self.make_certificate(a["root"], "unrelated-anchor")
        self.configure_peer(a, b, self.profile(a, b), anchor=unrelated)
        self.configure_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)
        message_id = "<protected-bad-certificate@example.invalid>"
        self.post(a, message_id, "bad-certificate")
        self.assert_not_received(b, message_id)
        journal = a["store"] / "feed" / (b["name"] + ".fnfd")
        self.assertTrue(journal.is_file(), "TLS refusal lost the durable feed intent")
        self.assertIsNone(a["process"].poll())
        self.assertIsNone(b["process"].poll())


if __name__ == "__main__":
    unittest.main()
