"""PKT-613 (PRF-231, SCN-157): a peer named by a DNS name, natively.

Two saved-image owners on loopback.  A scratch CA signs each node's
certificate; the dialling node is started with SSL_CERT_FILE naming that CA,
so the record `peer add ... HOST ... starttls - -` writes (the host's own
name, the system's public roots) verifies against it exactly as a node
anchored on the system bundle verifies a Let's Encrypt chain.  The name is
`localhost`, resolved by getaddrinfo on each attempt (no /etc/hosts edit).

Cases:
  * by name: the feed dials `localhost`, verifies the chain under the
    system roots and the name `localhost`, and the article arrives;
  * name mismatch: the target's certificate names `other.test`; the dial is
    refused by name (`outcome=name-mismatch`), retried, and nothing arrives;
  * resolution failure: the peer's host is `no-such-peer.invalid` (RFC 6761
    section 6.4: never resolves); the dial is reported `outcome=unresolved`,
    retried, and the node keeps serving.

Each case prints one `NATIVE-PEER-BY-NAME-WITNESS <json>` line after its
assertions pass.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest

from tests import test_native_peering as peer
from tests import test_native_protected_peering as protected

READY = peer.READY
IMAGE = peer.IMAGE
free_port = peer.free_port

Base = protected.NativeProtectedPeeringTests


@unittest.skipUnless(READY, "set explicit source-matched native image and hashes")
class NativePeerByNameTests(unittest.TestCase):
    command = Base.command
    process_identity = Base.process_identity
    stop_all = Base.stop_all
    article = staticmethod(Base.article)
    post = Base.post
    await_article = Base.await_article
    start = Base.start
    verify_process_identity = Base.verify_process_identity
    initialize = Base.initialize
    profile = Base.profile
    assert_not_received = Base.assert_not_received
    article_from = Base.article_from

    setUp = Base.setUp

    def scratch_ca(self):
        if getattr(self, "ca", None):
            return self.ca
        self.ca_key = self.base / "ca-key.pem"
        self.ca = self.base / "ca.pem"
        self.openssl(["req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256",
                      "-days", "1", "-subj", "/CN=fn scratch CA",
                      "-addext", "basicConstraints=critical,CA:TRUE",
                      "-addext", "keyUsage=critical,keyCertSign,cRLSign",
                      "-keyout", str(self.ca_key), "-out", str(self.ca)])
        return self.ca

    def openssl(self, arguments):
        result = subprocess.run(["openssl"] + arguments, stdout=subprocess.DEVNULL,
                                stderr=subprocess.PIPE, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())

    def make_certificate(self, root, name):
        """A leaf for the DNS name this test gives the node, signed by the CA."""
        dns = getattr(self, "certificate_names", {}).get(root.name, "localhost")
        ca = self.scratch_ca()
        key = root / (name + "-key.pem")
        request = root / (name + ".csr")
        certificate = root / (name + "-certificate.pem")
        extensions = root / (name + ".ext")
        extensions.write_text("subjectAltName=DNS:{}\nbasicConstraints=CA:FALSE\n"
                              "extendedKeyUsage=serverAuth\n".format(dns), encoding="ascii")
        self.openssl(["req", "-new", "-newkey", "rsa:2048", "-nodes", "-subj",
                      "/CN=" + dns, "-keyout", str(key), "-out", str(request)])
        self.openssl(["x509", "-req", "-in", str(request), "-CA", str(ca),
                      "-CAkey", str(self.ca_key), "-CAcreateserial", "-days", "1",
                      "-sha256", "-extfile", str(extensions), "-out", str(certificate)])
        return certificate, key

    def node(self, name, login, password):
        node = self.initialize(name, free_port(), login, password)
        # Observers and the pinned reverse direction anchor on the scratch CA.
        node["certificate"] = self.ca
        # The system roots of this node's TLS library are the scratch CA.
        node["owner_env"] = {"SSL_CERT_FILE": str(self.ca)}
        return node

    def add_named_peer(self, source, target, host):
        self.command([
            IMAGE, "--fn", "operator", source["config"], "peer", "add",
            target["name"], target["name"] + ".example.invalid", host,
            str(target["port"]), "fn.*", "fn.*", "principal", source["principal"],
            self.profile(source, target), "false", "true", "starttls", "-", "-"])

    def add_pinned_peer(self, source, target):
        self.command([
            IMAGE, "--fn", "operator", source["config"], "peer", "add",
            target["name"], target["name"] + ".example.invalid", "127.0.0.1",
            str(target["port"]), "fn.*", "fn.*", "principal", source["principal"],
            self.profile(source, target), "false", "true", "starttls",
            "localhost", str(self.ca)])

    def peer_list(self, node):
        return self.command([IMAGE, "--fn", "operator", node["config"], "peer",
                             "list"]).stdout.decode("ascii")

    def dial_lines(self, node, outcome, count, timeout=60):
        pattern = "outcome={} retry=yes".format(outcome)
        deadline = time.monotonic() + timeout
        lines = []
        while time.monotonic() < deadline:
            text = node["stderr_path"].read_text(errors="replace")
            lines = [line for line in text.splitlines()
                     if line.startswith("peer dial ") and pattern in line]
            if len(lines) >= count:
                return lines
            time.sleep(0.5)
        self.fail("{} logged {} of {} `{}` dial lines:\n{}".format(
            node["name"], len(lines), count, pattern,
            node["stderr_path"].read_text(errors="replace")[-4000:]))

    @staticmethod
    def witness(record):
        print("NATIVE-PEER-BY-NAME-WITNESS " + json.dumps(record, sort_keys=True),
              flush=True)

    def test_feed_by_name_under_the_system_roots(self):
        a = self.node("byname-a", "b-at-a", "b-secret")
        b = self.node("byname-b", "a-at-b", "a-secret")
        self.add_named_peer(a, b, "localhost")
        self.add_pinned_peer(b, a)
        listed = self.peer_list(a)
        self.assertIn("address=localhost ", listed)
        self.start(a)
        self.start(b)
        message_id = "<by-name@example.invalid>"
        self.post(a, message_id, "by-name")
        self.assertEqual(self.await_article(b, message_id),
                         self.await_article(a, message_id))
        text = a["stderr_path"].read_text(errors="replace")
        self.assertNotIn("peer dial via=feed", text)
        self.witness({"case": "by-name", "host": "localhost", "server_name": "localhost",
                      "trust": "system-roots", "delivered": True,
                      "identity": {"a": a["identities"][-1], "b": b["identities"][-1]}})

    def test_name_mismatch_is_refused_by_name_and_retried(self):
        self.certificate_names = {"mismatch-b": "other.test"}
        a = self.node("mismatch-a", "b-at-a", "b-secret")
        b = self.node("mismatch-b", "a-at-b", "a-secret")
        self.add_named_peer(a, b, "localhost")
        self.add_pinned_peer(b, a)
        self.start(a)
        self.start(b)
        message_id = "<by-name-mismatch@example.invalid>"
        self.post(a, message_id, "mismatch")
        lines = self.dial_lines(a, "name-mismatch", 2)
        self.assertIn("host=localhost", lines[0])
        self.assert_not_received(b, message_id)
        self.assertIsNone(a["process"].poll())
        self.assertIsNone(b["process"].poll())
        self.witness({"case": "name-mismatch", "host": "localhost",
                      "certificate": "other.test", "refusals": len(lines),
                      "line": lines[0], "delivered": False, "source_alive": True})

    def test_resolution_failure_is_named_and_retried(self):
        a = self.node("unresolved-a", "b-at-a", "b-secret")
        b = self.node("unresolved-b", "a-at-b", "a-secret")
        self.add_named_peer(a, b, "no-such-peer.invalid")
        self.start(a)
        message_id = "<by-name-unresolved@example.invalid>"
        self.post(a, message_id, "unresolved")
        lines = self.dial_lines(a, "unresolved", 2)
        self.assertIn("host=no-such-peer.invalid", lines[0])
        self.assertIsNone(a["process"].poll())
        # Still serving: the posted article reads back on a fresh connection.
        self.assertIsNotNone(self.await_article(a, message_id))
        self.witness({"case": "unresolved", "host": "no-such-peer.invalid",
                      "failures": len(lines), "line": lines[0], "source_alive": True})

    def test_peer_add_refuses_a_host_that_is_not_a_host(self):
        a = self.node("refuse-a", "b-at-a", "b-secret")
        b = self.node("refuse-b", "a-at-b", "a-secret")
        for host, name in (("bad_host.example", "-"), ("127.0.0.1", "-")):
            result = subprocess.run(
                [str(IMAGE), "--fn", "operator", str(a["config"]), "peer", "add",
                 "b", "b.example.invalid", host, str(b["port"]), "fn.*", "fn.*",
                 "principal", a["principal"], str(self.profile(a, b)), "false",
                 "true", "starttls", name, "-"],
                cwd=peer.ROOT, env=self.env, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, timeout=180)
            self.assertNotEqual(result.returncode, 0, (host, result.stdout))
        self.assertNotIn("b path-identity", self.peer_list(a))
        self.witness({"case": "refused-words", "hosts": ["bad_host.example", "127.0.0.1 with -"]})


if __name__ == "__main__":
    unittest.main()
