"""Opt-in reciprocal STARTTLS+AUTHINFO native peering witness.

Both peers are saved-image owner processes. Python creates private credentials,
certificates and configuration, starts the processes, and observes public NNTP.

Each test prints one `NATIVE-PROTECTED-WITNESS <json>` line when its
assertions have passed; tools/v0_matrix.py's native slice maps those lines,
and nothing else, to its V0-TRANSIT-TLS / V0-TRANSIT-AUTHINFO rows.  What a
line establishes is stated by the configuration it ran under: the target
requires authentication and refuses AUTHINFO before TLS (`required = true`,
`protected_only = true`), and the source's record for it names STARTTLS,
the target's certificate as the only anchor, and the credential profile.
"""
import json
import os
from pathlib import Path
import re
import socket
import ssl
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
    process_identity = peer.NativePeeringTests.process_identity
    verify_process_identity = peer.NativePeeringTests.verify_process_identity
    stop_all = peer.NativePeeringTests.stop_all
    article = staticmethod(peer.NativePeeringTests.article)
    post = peer.NativePeeringTests.post
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

    def article_from(self, node, message_id):
        """Observe through a fully protected reader; only 430 means absent."""
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=15) as raw:
            def recvline(sock):
                line = bytearray()
                while not line.endswith(b"\n"):
                    chunk = sock.recv(1)
                    if not chunk:
                        break
                    line.extend(chunk)
                return bytes(line)

            greeting = recvline(raw)
            self.assertTrue(greeting.startswith((b"200 ", b"201 ")), greeting)
            raw.sendall(b"STARTTLS\r\n")
            response = recvline(raw)
            self.assertTrue(response.startswith(b"382 "), response)
            context = ssl.create_default_context(cafile=str(node["certificate"]))
            with context.wrap_socket(raw, server_hostname="localhost") as tls:
                with tls.makefile("rwb", buffering=0) as stream:
                    stream.write(b"AUTHINFO USER " + node["login"].encode() + b"\r\n")
                    response = stream.readline()
                    self.assertTrue(response.startswith(b"381 "), response)
                    stream.write(b"AUTHINFO PASS " + node["password"].encode() + b"\r\n")
                    response = stream.readline()
                    self.assertTrue(response.startswith(b"281 "), response)
                    stream.write(b"ARTICLE " + message_id.encode() + b"\r\n")
                    response = stream.readline()
                    if response.startswith(b"430 "):
                        return None
                    self.assertTrue(response.startswith(b"220 "), response)
                    article = bytearray()
                    while True:
                        line = stream.readline()
                        self.assertNotEqual(line, b"", "protected observer article EOF")
                        if line == b".\r\n":
                            return bytes(article)
                        article.extend(line[1:] if line.startswith(b"..") else line)

    @staticmethod
    def witness(record):
        print("NATIVE-PROTECTED-WITNESS " + json.dumps(record, sort_keys=True), flush=True)

    def test_reciprocal_starttls_authinfo_transfer_and_reconnect(self):
        a = self.initialize("protected-a", free_port(), "b-at-a", "b-secret")
        b = self.initialize("protected-b", free_port(), "a-at-b", "a-secret")
        self.configure_peer(a, b, self.profile(a, b))
        self.configure_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)

        transit = {}
        for source, target, way in ((a, b, "ab"), (b, a, "ba")):
            label = "a-to-b" if way == "ab" else "b-to-a"
            message_id = "<protected-{}@example.invalid>".format(label)
            self.post(source, message_id, label)
            identical = (self.await_article(target, message_id)
                         == self.await_article(source, message_id))
            self.assertTrue(identical)
            # The same offer on a connection that did not log in is 480: the
            # article above arrived on one that did.
            reader_offer = self.duplicate_offer(target, message_id)
            self.assertTrue(reader_offer.startswith(b"480 "))
            transit[way] = {"identical": identical,
                            "unauthenticated_offer": reader_offer.decode(
                                "ascii", "replace").strip()}

        # Drop both processes after durable acknowledgements, then demonstrate
        # fresh TLS and AUTHINFO sessions in both directions after restart.
        self.stop_all()
        self.start(a)
        self.start(b)
        reconnect = {}
        for source, target, way in ((a, b, "ab"), (b, a, "ba")):
            label = "a-reconnect" if way == "ab" else "b-reconnect"
            message_id = "<protected-{}@example.invalid>".format(label)
            self.post(source, message_id, label)
            identical = (self.await_article(target, message_id)
                         == self.await_article(source, message_id))
            self.assertTrue(identical)
            reconnect[way] = {"identical": identical}
        self.witness({
            "kind": "protected-feed", "security": "starttls", "auth": "authinfo",
            "target_policy": {"required": True, "protected_only": True},
            "transit": transit, "reconnect": reconnect,
            "identity": {"a": a["identities"][-1], "b": b["identities"][-1]}})

    def test_bad_outbound_password_yields_authenticated_430_observation(self):
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
        self.witness({"kind": "protected-refusal", "case": "wrong-password",
                      "delivered": False, "source_alive": True, "target_alive": True,
                      "identity": {"a": a["identities"][-1], "b": b["identities"][-1]}})

    def test_untrusted_certificate_yields_430_and_feed_journal_evidence(self):
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
        self.assertTrue(journal.is_file(), "accepted post produced no feed journal evidence")
        self.assertIsNone(a["process"].poll())
        self.assertIsNone(b["process"].poll())
        self.witness({"kind": "protected-refusal", "case": "wrong-anchor",
                      "delivered": False, "journal": True, "source_alive": True,
                      "target_alive": True,
                      "identity": {"a": a["identities"][-1], "b": b["identities"][-1]}})


if __name__ == "__main__":
    unittest.main()
