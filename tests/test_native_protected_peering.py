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
import ssl
import subprocess
import time
import unittest

from tests import test_native_peering as peer
from tests.native_harness import (
    EXIT_OK, Acl2Session, Client, Node, acl2_nat, acl2_result, native_image, scratch)

ACTUAL_CORE = peer.ACTUAL_CORE
ACTUAL_LAUNCHER = peer.ACTUAL_LAUNCHER
IMAGE = peer.IMAGE
READY = peer.READY
SOURCE = peer.SOURCE
# The developer image must be named explicitly: the case pins its core.
DEVELOPER_TEXT = os.environ.get("FN_NATIVE_DEVELOPER_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST") if DEVELOPER_TEXT else None
DEVELOPER_CORE_SHA256 = os.environ.get("FN_NATIVE_DEVELOPER_CORE_SHA256")
DEVELOPER_LAUNCHER_SHA256 = os.environ.get("FN_NATIVE_DEVELOPER_LAUNCHER_SHA256")


def inspect_feed_journal(path, msgid, peer):
    """An at-rest FNFD file read through ACL2's own scanner and replay
    (books/feed-journal.lisp), in the developer image's session: Python only
    reads the prefix length ACL2 names, so the record kinds, queue state and
    attempt count are the book's projection of the durable bytes."""
    with Acl2Session(DEVELOPER) as acl2:
        def symbol(form):
            text = acl2_result(acl2.call(form)).decode("ascii", "replace").strip().lower()
            return text[1:] if text.startswith(":") else text

        def nat(form):
            return acl2_nat(acl2.call(form))

        acl2.call("(f-put-global 'fn-owner-feed-safe-offset 0 state)")
        acl2.call("(f-put-global 'fn-test-feed (fn-feed-open '{} (fn-feed-limits 100 1000 3 t) "
                  "(fn-sched-contact \"inn\" 0 1000000) nil) state)".format(acl2.literal(peer)))
        if symbol("(fn-feedp (@ fn-test-feed))") != "t":
            raise AssertionError("ACL2 inspector initial feed is invalid")
        counts = {}
        prefix_size = nat("*fn-feed-journal-prefix-size*")
        with Path(path).open("rb") as source:
            while True:
                prefix = source.read(prefix_size)
                if not prefix:
                    break
                plan = symbol("(fn-feed-journal-prefix '{})".format(acl2.literal(prefix)))
                if not plan.isdigit():
                    raise AssertionError("ACL2 refused FNFD prefix: {}".format(plan))
                frame = source.read(int(plan))
                if len(frame) != int(plan):
                    raise AssertionError("short FNFD frame")
                acl2.call("(f-put-global 'fn-test-scan (fn-feed-journal-scan '{} '{} '{} "
                          "(@ fn-owner-feed-safe-offset)) state)".format(
                              acl2.literal(peer), acl2.literal(prefix), acl2.literal(frame)))
                state = symbol("(car (@ fn-test-scan))")
                if state != "next":
                    raise AssertionError("ACL2 refused FNFD frame: {}".format(state))
                acl2.call("(f-put-global 'fn-owner-feed-safe-offset (cadr (@ fn-test-scan)) state)")
                acl2.call("(f-put-global 'fn-test-feed (fn-feed-replay (@ fn-test-feed) "
                          "(list (caddr (@ fn-test-scan)))) state)")
                if symbol("(fn-feedp (@ fn-test-feed))") != "t":
                    raise AssertionError("ACL2 replay left the feed recognizer")
                kind = symbol("(fn-feed-journal-kind (caddr (@ fn-test-scan)))")
                counts[kind] = counts.get(kind, 0) + 1
        mid = acl2.literal(msgid.encode("ascii"))
        queue = "(fn-feed-queue (@ fn-test-feed))"
        before = symbol("(fn-feed-state-of '{} {})".format(mid, queue))
        sent_before = symbol("(fn-feed-sentp (fn-feed-state-of '{} {}))".format(mid, queue))
        acl2.call("(f-put-global 'fn-test-feed (fn-feed-restart (@ fn-test-feed)) state)")
        return {"records": counts, "state_before_restart": before,
                "sent_before_restart": sent_before,
                "state_after_restart": symbol("(fn-feed-state-of '{} {})".format(mid, queue)),
                "queue_length": nat("(len {})".format(queue)),
                # An acknowledged entry is retired by its outcome record
                # (fn-feed-done): it has left the queue and has no attempts.
                "attempts": (None if symbol("(fn-feed-find '{} {})".format(mid, queue)) == "nil"
                             else nat("(fn-feed-entry-attempts (fn-feed-find '{} {}))".format(mid, queue))),
                "next_attempt": nat("(fn-feed-next-attempt (@ fn-test-feed))"),
                "inflight": symbol("(fn-feed-inflightp '{} (@ fn-test-feed))".format(mid))}


@unittest.skipUnless(READY, "set explicit source-matched native image and hashes")
class NativeProtectedPeeringTests(unittest.TestCase):
    process_identity = peer.NativePeeringTests.process_identity
    def stop_all(self):
        # This module's owners are a Popen whose stderr is a file (start
        # below); peer.NativePeeringTests.stop_all expects the drained
        # NativeProcess and failed every test here with AttributeError
        # 'stop' (seen by lane feed-tls-read, 2026-09-28).
        for process in self.processes:
            process.terminate()
        for process in self.processes:
            if hasattr(process, "stop"):
                process.stop()
                continue
            try:
                process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=15)
        self.processes = []
    article = staticmethod(peer.NativePeeringTests.article)
    post = peer.NativePeeringTests.post
    await_article = peer.NativePeeringTests.await_article

    @classmethod
    def setUpClass(cls):
        print("native-protected-peering launcher-sha256={} core-sha256={} source={}".format(
            ACTUAL_LAUNCHER, ACTUAL_CORE, SOURCE))

    def setUp(self):
        self.base = scratch(self, "fn-native-protected-peer-")

    def start(self, node):
        """The owner on NODE.owner_image (default the node's image) with
        NODE.owner_env; drained, so the many unclean TLS closes the probes
        log never block it."""
        node.start(image=getattr(node, "owner_image", None),
                   env=getattr(node, "owner_env", None))
        self.verify_process_identity(node)

    @staticmethod
    def stop_all(*nodes):
        for node in nodes:
            node.stop_all()

    def verify_process_identity(self, node):
        found = self.process_identity(node.process)
        if found["status"] != "observed":
            self.skipTest("cannot observe native runtime/core: {}".format(found["reason"]))
        self.assertEqual(found["runtime_sha256"], peer.RUNTIME_SHA256, found)
        self.assertEqual(found["core_sha256"],
                         getattr(node, "expected_core_sha256", peer.CORE_SHA256), found)
        node.identities = getattr(node, "identities", []) + [found]
        return found

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

    def initialize(self, name, login, password):
        node = Node(self, IMAGE, root=self.base / name, name=name)
        auth = node.root / "auth.toml"
        certificate, key = self.make_certificate(node.root, name)
        node.store("init", "fn.test", expect=EXIT_OK)
        node.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = true\npath = "{}"\n'.format(
                node.store_path, node.port, certificate, key, node.control, auth),
            encoding="ascii")
        node.operator("principal", "set-password", login, "--posting",
                      input=(password + "\n" + password + "\n").encode(), expect=EXIT_OK)
        listed = node.operator("principal", "list", expect=EXIT_OK).stdout.decode("ascii")
        matches = re.findall(r"[0-9a-f]{64}", listed)
        self.assertEqual(len(matches), 1, listed)
        node.certificate, node.principal = certificate, matches[0]
        node.login, node.password = login, password
        return node

    def profile(self, source, target, password=None):
        path = source.root / (target.name + ".fnauth")
        path.write_bytes(("FNAUTH1\n{}\n{}\n".format(
            target.login, password or target.password)).encode("ascii"))
        path.chmod(0o600)
        return path

    def configure_peer(self, source, target, profile, anchor=None):
        source.operator(
            "peer", "add", target.name, target.name + ".example.invalid", "127.0.0.1",
            str(target.port), "fn.*", "fn.*", "principal", source.principal, profile,
            "false", "true", "starttls", "localhost", anchor or target.certificate,
            expect=EXIT_OK)

    def assert_not_received(self, node, message_id, seconds=3):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            self.assertIsNone(self.article_from(node, message_id))
            time.sleep(0.1)

    def capture_owner_failure(self, nodes, stage):
        """Keep bounded process evidence before unittest cleanup stops owners."""
        root = os.environ.get("FN_NATIVE_TEST_DIAGNOSTIC_DIR")
        if not root:
            return
        report = {"stage": stage, "owners": {}}
        for node in nodes:
            process = node.process
            proc = Path("/proc") / str(process.pid)
            threads = {}
            for task in (proc / "task").glob("*") if proc.is_dir() else ():
                info = {}
                for name in ("wchan", "stack", "status"):
                    try:
                        info[name] = (task / name).read_text(errors="replace")[:3000]
                    except OSError as error:
                        info[name] = type(error).__name__
                threads[task.name] = info
            pipes = {name: getattr(process, name).tail(16384).decode("utf-8", "replace")
                     for name in ("stdout", "stderr")}
            report["owners"][node.name] = {
                "pid": process.pid, "exit": process.poll(),
                "threads": threads, "pipes": pipes}
        destination = Path(root) / (stage + ".json")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(report, indent=2), encoding="utf-8")
        print("NATIVE-PROTECTED-DIAGNOSTIC " + str(destination), flush=True)

    def protected_client(self, node):
        """A connection through STARTTLS, verified against NODE's certificate
        (tests/test_native_peer_by_name.py verifies under its scratch CA)."""
        client = Client(node.port, timeout=15, server_hostname="localhost")
        response = client.starttls(ssl.create_default_context(cafile=str(node.certificate)))
        self.assertTrue(response.startswith(b"382 "), response)
        return client

    def article_from(self, node, message_id):
        """Observe through a fully protected reader; only 430 means absent."""
        with self.protected_client(node) as client:
            response = client.command(b"AUTHINFO USER " + node.login.encode())
            self.assertTrue(response.startswith(b"381 "), response)
            response = client.command(b"AUTHINFO PASS " + node.password.encode())
            self.assertTrue(response.startswith(b"281 "), response)
            response, article = client.multiline(b"ARTICLE " + message_id.encode())
            if response.startswith(b"430 "):
                return None
            self.assertTrue(response.startswith(b"220 "), response)
            return article

    def unauthenticated_offer(self, node, message_id):
        """Probe the protected ingress after TLS, without AUTHINFO."""
        with self.protected_client(node) as client:
            return client.command(b"IHAVE " + message_id.encode("ascii"))

    @staticmethod
    def witness(record):
        print("NATIVE-PROTECTED-WITNESS " + json.dumps(record, sort_keys=True), flush=True)

    def test_reciprocal_starttls_authinfo_transfer_and_reconnect(self):
        a = self.initialize("protected-a", "b-at-a", "b-secret")
        b = self.initialize("protected-b", "a-at-b", "a-secret")
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
            # The same offer on a protected connection without the peer role
            # is denied as transit; the article above arrived on one that
            # completed AUTHINFO.
            reader_offer = self.unauthenticated_offer(target, message_id)
            self.assertTrue(reader_offer.startswith(b"502 "), reader_offer)
            transit[way] = {"identical": identical,
                            "unauthenticated_offer": reader_offer.decode(
                                "ascii", "replace").strip()}

        # Drop both processes after durable acknowledgements, then demonstrate
        # fresh TLS and AUTHINFO sessions in both directions after restart.
        self.stop_all(a, b)
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
            "identity": {"a": a.identities[-1], "b": b.identities[-1]}})

    def test_bad_outbound_password_yields_authenticated_430_observation(self):
        a = self.initialize("bad-auth-a", "b-at-a", "b-secret")
        b = self.initialize("bad-auth-b", "a-at-b", "a-secret")
        self.configure_peer(a, b, self.profile(a, b, password="wrong"))
        self.configure_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)
        message_id = "<protected-bad-password@example.invalid>"
        self.post(a, message_id, "bad-password")
        self.assert_not_received(b, message_id)
        self.assertIsNone(a.process.poll())
        self.assertIsNone(b.process.poll())
        self.witness({"kind": "protected-refusal", "case": "wrong-password",
                      "delivered": False, "source_alive": True, "target_alive": True,
                      "identity": {"a": a.identities[-1], "b": b.identities[-1]}})

    def test_acknowledged_protected_feed_does_not_reoffer_after_source_death(self):
        a = self.initialize("once-a", "b-at-a", "b-secret")
        b = self.initialize("once-b", "a-at-b", "a-secret")
        self.configure_peer(a, b, self.profile(a, b))
        self.configure_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)
        message_id = "<protected-feed-once@example.invalid>"
        self.post(a, message_id, "feed-once")
        try:
            self.assertEqual(self.await_article(b, message_id),
                             self.await_article(a, message_id))
        except Exception:
            self.capture_owner_failure((a, b), "feed-once-initial")
            raise
        journal = a.store_path / "feed" / "once-b.fnfd"
        self.assertTrue(journal.is_file())

        # The target has accepted the article.  Kill the sender, then let
        # ACL2 replay its durable FNFD bytes, not a Python FNFD decoder.
        # A bounded wait allows its acknowledged outcome to cross FNFD's
        # durability barrier before the kill; an absent outcome fails below.
        time.sleep(0.5)
        source = a.process
        source.kill()
        source.wait(timeout=30)
        source.finish()
        before = inspect_feed_journal(journal, message_id, b"once-b")
        # The acknowledged entry is RETIRED by its outcome record (fn-feed-done:
        # it leaves the queue, the outcome record keeps which it was), before
        # and after the restart fold: nothing is left to offer.
        self.assertEqual(before["state_before_restart"], "nil", before)
        self.assertEqual(before["state_after_restart"], "nil", before)
        self.assertEqual(before["queue_length"], 0, before)
        self.assertGreaterEqual(before["records"].get("feed-commit", 0), 1, before)
        self.assertGreaterEqual(before["records"].get("feed-outcome", 0), 1, before)

        self.start(a)
        time.sleep(2)
        self.assertEqual(self.await_article(b, message_id),
                         self.await_article(a, message_id))
        identity = {"a": self.verify_process_identity(a),
                    "b": self.verify_process_identity(b)}
        self.stop_all(a, b)
        after = inspect_feed_journal(journal, message_id, b"once-b")
        self.assertEqual(after["state_after_restart"], "nil", after)
        self.assertEqual(after["queue_length"], 0, after)
        self.assertEqual(after["records"].get("feed-offer", 0),
                         before["records"].get("feed-offer", 0), (before, after))
        self.assertEqual(after["records"].get("feed-sent", 0),
                         before["records"].get("feed-sent", 0), (before, after))
        status = b.operator("status", expect=EXIT_OK)
        self.assertIn(b"articles=1", status.stdout, status.stdout)
        self.witness({"kind": "feed-once", "security": "starttls",
                      "auth": "authinfo", "source_killed": True,
                      "source_restarted": True, "recipient_articles": 1,
                      "before": before, "after": after, "identity": identity})

    def test_durable_sent_cut_requeues_on_protected_restart(self):
        if not (DEVELOPER and DEVELOPER.is_file()
                and os.access(DEVELOPER, os.X_OK)
                and Path(str(DEVELOPER) + ".core").is_file()
                and DEVELOPER_LAUNCHER_SHA256 == peer.digest(DEVELOPER)
                and DEVELOPER_CORE_SHA256 == peer.digest(Path(str(DEVELOPER) + ".core"))):
            self.skipTest("source-matched developer image and hashes required")
        a = self.initialize("sent-a", "b-at-a", "b-secret")
        b = self.initialize("sent-b", "a-at-b", "a-secret")
        self.configure_peer(a, b, self.profile(a, b))
        self.configure_peer(b, a, self.profile(b, a))
        a.owner_image = DEVELOPER
        a.expected_core_sha256 = DEVELOPER_CORE_SHA256
        a.owner_env = {"FN_NATIVE_FEED_TEST_STOP_AFTER_SENT": "1"}
        self.start(a)
        self.start(b)
        message_id = "<protected-sent-restart@example.invalid>"
        self.post(a, message_id, "sent-restart")

        source = a.process
        deadline = time.monotonic() + 45
        stopped = False
        while time.monotonic() < deadline and source.poll() is None:
            try:
                state = (Path("/proc") / str(source.pid) / "status").read_text()
                stopped = any(line.startswith("State:") and "T (stopped)" in line
                              for line in state.splitlines())
            except OSError:
                pass
            if stopped:
                break
            time.sleep(0.05)
        if not stopped:
            self.capture_owner_failure((a, b), "feed-sent-cut-missing")
            source.kill()
            self.fail("developer source did not stop after durable :feed-sent")
        self.assertIsNone(self.article_from(b, message_id))
        source.kill()
        self.assertEqual(source.wait(timeout=30), -9)
        source.finish()
        journal = a.store_path / "feed" / "sent-b.fnfd"
        interrupted = inspect_feed_journal(journal, message_id, b"sent-b")
        self.assertEqual(interrupted["sent_before_restart"], "t", interrupted)
        self.assertEqual(interrupted["state_after_restart"], "queued", interrupted)
        self.assertGreaterEqual(interrupted["records"].get("feed-sent", 0), 1)
        self.assertEqual(interrupted["records"].get("feed-outcome", 0), 0)

        a.owner_image = IMAGE
        a.expected_core_sha256 = peer.CORE_SHA256
        a.owner_env = {}
        self.start(a)
        self.assertEqual(self.await_article(b, message_id),
                         self.await_article(a, message_id))
        identity = {"a": self.verify_process_identity(a),
                    "b": self.verify_process_identity(b)}
        self.stop_all(a, b)
        settled = inspect_feed_journal(journal, message_id, b"sent-b")
        self.assertEqual(settled["state_after_restart"], "nil", settled)
        self.assertEqual(settled["queue_length"], 0, settled)
        self.assertGreaterEqual(settled["records"].get("feed-outcome", 0), 1, settled)
        self.assertGreater(settled["records"].get("feed-offer", 0),
                           interrupted["records"].get("feed-offer", 0))
        status = b.operator("status", expect=EXIT_OK)
        self.assertIn(b"articles=1", status.stdout, status.stdout)
        self.witness({"kind": "feed-sent-restart", "security": "starttls",
                      "auth": "authinfo", "sender_stopped_after_sent": True,
                      "sender_killed": True, "sender_restarted": True,
                      "recipient_articles": 1, "interrupted": interrupted,
                      "settled": settled, "identity": identity,
                      "developer_identity": a.identities[0]})

    def test_untrusted_certificate_yields_430_and_feed_journal_evidence(self):
        a = self.initialize("bad-cert-a", "b-at-a", "b-secret")
        b = self.initialize("bad-cert-b", "a-at-b", "a-secret")
        unrelated, _ = self.make_certificate(a.root, "unrelated-anchor")
        self.configure_peer(a, b, self.profile(a, b), anchor=unrelated)
        self.configure_peer(b, a, self.profile(b, a))
        self.start(a)
        self.start(b)
        message_id = "<protected-bad-certificate@example.invalid>"
        self.post(a, message_id, "bad-certificate")
        self.assert_not_received(b, message_id)
        journal = a.store_path / "feed" / (b.name + ".fnfd")
        self.assertTrue(journal.is_file(), "accepted post produced no feed journal evidence")
        self.assertIsNone(a.process.poll())
        self.assertIsNone(b.process.poll())
        self.witness({"kind": "protected-refusal", "case": "wrong-anchor",
                      "delivered": False, "journal": True, "source_alive": True,
                      "target_alive": True,
                      "identity": {"a": a.identities[-1], "b": b.identities[-1]}})


if __name__ == "__main__":
    unittest.main()
