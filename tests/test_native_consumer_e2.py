"""Real local-owner E2 cursor declarations through one saved native image.

Requires the combined consumer-local command and production bootstrap.
The cursor files are ACL2 output; this test never constructs or edits fncu bytes.
There is no served poll endpoint yet, so these cases exercise a zero-position
ack and do not claim nonzero scan progress or consumer inbox processing.
"""

import os
import json
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))
ENABLED = os.environ.get("FN_RUN_CONSUMER_E2E") == "1"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(ENABLED and IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "set FN_RUN_CONSUMER_E2E=1 and a source-matched "
                     "FN_NATIVE_DEVELOPER_HOST")
class NativeConsumerE2Tests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="fn-consumer-e2-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.env.pop("FN_NATIVE_CONTROL_FAULT", None)
        self.env.pop("FN_NATIVE_CONTROL_TEST_STOP", None)

    def native(self, *words, env=None, timeout=120):
        return subprocess.run([str(IMAGE), "--fn", *map(str, words)],
                              cwd=ROOT, env=env or self.env,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=timeout, check=False)

    def accepted(self, *words, env=None):
        result = self.native(*words, env=env)
        self.assertEqual(result.returncode, 0,
                         result.stderr.decode("utf-8", "replace"))
        return result

    def node(self, name):
        base = self.root / name
        base.mkdir()
        store = base / "store"
        control = base / "control.sock"
        config = base / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(
                store, free_port(), control), encoding="ascii")
        self.accepted("store", store, "init", "fn.test")
        return {"base": base, "store": store, "control": control,
                "config": config}

    def start_owner(self, node, *, stop_after_submit=False):
        env = dict(self.env)
        if stop_after_submit:
            env["FN_NATIVE_CONTROL_TEST_STOP"] = "after-submit"
        proc = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
        self.addCleanup(self.reap, proc)
        wait_for_announcement(proc, b"LISTENING ", timeout=120)
        return proc

    @staticmethod
    def reap(proc):
        if proc.poll() is None:
            proc.kill()
            proc.wait(timeout=10)
        for stream in (proc.stdout, proc.stderr):
            if stream and not stream.closed:
                stream.close()

    def stop_owner(self, proc):
        diagnostics = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostics)

    def consumer(self, verb, node, *args, expected=0):
        result = self.native("consumer", verb, node["control"], *args)
        self.assertEqual(result.returncode, expected,
                         result.stderr.decode("utf-8", "replace"))
        return result

    def bootstrap(self, node):
        self.assertIn(b"consumer accepted",
                      self.consumer("bootstrap", node).stdout)

    def register(self, node, name, target):
        result = self.consumer("register", node, name, "fn.test", target)
        self.assertIn(b"consumer accepted", result.stdout)
        token = target.read_bytes()
        self.assertTrue(token.startswith(b"fncu\x01"), token[:8])
        return token

    def position(self, node, name, target, *, expected=0):
        result = self.consumer("position", node, name, target,
                               expected=expected)
        if expected == 0:
            self.assertIn(b"consumer accepted", result.stdout)
            self.assertTrue(target.is_file())
            return target.read_bytes()
        self.assertFalse(target.exists())
        return None

    def test_durable_scope_ack_and_unrelated_article(self):
        first = self.node("first")
        owner = self.start_owner(first)
        unbootstrapped = first["base"] / "unbootstrapped.fncu"
        self.consumer("register", first, "worker", "fn.test",
                      unbootstrapped, expected=1)
        self.assertFalse(unbootstrapped.exists())
        self.bootstrap(first)
        token_path = first["base"] / "initial.fncu"
        initial = self.register(first, "worker", token_path)
        self.assertEqual(self.position(first, "worker",
                                       first["base"] / "before.fncu"), initial)

        # A normal accepted article adds a Store record but does not declare
        # consumer processing. The native POSITION output remains unchanged.
        msgid = "<consumer-unrelated@example.invalid>"
        source = (b"From: author@example.invalid\r\n"
                  b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                  b"Newsgroups: fn.test\r\nSubject: unrelated\r\n"
                  b"Message-ID: " + msgid.encode("ascii") +
                  b"\r\n\r\nunrelated exact body\r\n")
        article = first["base"] / "unrelated.eml"
        article.write_bytes(source)
        self.accepted("operator", first["config"], "post", "--message-id",
                      msgid, "--payload", article, "--group", "fn.test")
        self.assertEqual(self.position(first, "worker",
                                       first["base"] / "after-post.fncu"), initial)
        self.assertIn(b"consumer accepted",
                      self.consumer("ack", first, token_path).stdout)
        self.assertEqual(self.position(first, "worker",
                                       first["base"] / "after-ack.fncu"), initial)

        # The same ID in an independent history cannot use this cursor.
        other = self.node("other")
        other_owner = self.start_owner(other)
        self.bootstrap(other)
        other_token = self.register(other, "worker", other["base"] / "other.fncu")
        self.assertNotEqual(other_token, initial)
        self.consumer("ack", other, token_path, expected=1)
        self.assertEqual(self.position(other, "worker",
                                       other["base"] / "other-position.fncu"),
                         other_token)

        self.consumer("unregister", first, "worker")
        self.position(first, "worker", first["base"] / "removed.fncu", expected=1)
        current = self.register(first, "worker", first["base"] / "renewed.fncu")
        self.assertNotEqual(current, initial)  # durable registration epoch
        self.consumer("ack", first, token_path, expected=1)
        self.assertEqual(self.position(first, "worker",
                                       first["base"] / "renewed-position.fncu"),
                         current)
        self.stop_owner(owner)
        self.stop_owner(other_owner)
        inspected = self.accepted("store", first["store"], "inspect", msgid)
        self.assertIn(b"unrelated exact body", inspected.stdout)
        reopened = self.start_owner(first)
        self.assertEqual(self.position(first, "worker",
                                       first["base"] / "reopened.fncu"), current)
        self.stop_owner(reopened)

    def test_lost_register_reply_resolves_by_reopened_position(self):
        node = self.node("uncertain")
        bootstrap_owner = self.start_owner(node)
        self.bootstrap(node)
        self.stop_owner(bootstrap_owner)
        owner = self.start_owner(node, stop_after_submit=True)
        token_path = node["base"] / "lost-reply.fncu"
        client = subprocess.Popen(
            [str(IMAGE), "--fn", "consumer", "register", str(node["control"]),
             "worker", "fn.test", str(token_path)],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        self.addCleanup(self.reap, client)
        wait_for_announcement(owner, b"CONTROL-SUBMITTED", timeout=120)
        owner.kill()  # actual process death after durable completion, pre-reply
        owner.wait(timeout=10)
        stdout, stderr = client.communicate(timeout=30)
        self.assertEqual(client.returncode, 3, (stdout + stderr).decode())
        self.assertFalse(token_path.exists())

        reopened = self.start_owner(node)
        recovered = self.position(node, "worker", node["base"] / "recovered.fncu")
        # Same-scope registration is idempotent after replay: no fresh epoch.
        again = self.register(node, "worker", node["base"] / "again.fncu")
        self.assertEqual(again, recovered)
        self.consumer("ack", node, node["base"] / "recovered.fncu")
        self.assertEqual(self.position(node, "worker",
                                       node["base"] / "after-resolution.fncu"),
                         recovered)
        self.stop_owner(reopened)

    @unittest.skipUnless(os.environ.get("FN_RUN_CONSUMER_POLL_E2E") == "1",
                         "requires the ACL2-owned consumer poll command")
    def test_signed_composite_poll_and_lost_positive_ack_reply(self):
        from tools import run_store

        node = self.node("signed-poll")
        owner = self.start_owner(node)
        self.bootstrap(node)
        before = self.register(node, "worker", node["base"] / "registered.fncu")

        principal = node["base"] / "principal.bin"
        ed_public = node["base"] / "ed-public.bin"
        ed_secret = node["base"] / "ed-secret.bin"
        ml_private = node["base"] / "ml-private.pem"
        ml_public = node["base"] / "ml-public.pem"
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        made = subprocess.run([openssl, "genpkey", "-algorithm", "ML-DSA-65",
                               "-out", str(ml_private)], cwd=ROOT,
                              env=self.env, capture_output=True, timeout=60,
                              check=False)
        self.assertEqual(made.returncode, 0, made.stderr.decode("utf-8", "replace"))
        exported = subprocess.run([openssl, "pkey", "-in", str(ml_private),
                                   "-pubout", "-out", str(ml_public)],
                                  cwd=ROOT, env=self.env, capture_output=True,
                                  timeout=60, check=False)
        self.assertEqual(exported.returncode, 0,
                         exported.stderr.decode("utf-8", "replace"))

        source_name = os.environ.get("FN_CONSUMER_POLL_SOURCE_FILE")
        if source_name:
            source_path = Path(source_name)
            self.assertTrue(source_path.is_absolute() and source_path.is_file())
            source = source_path.read_bytes()
        else:
            source = (b"From: author@example.invalid\r\n"
                      b"Newsgroups: fn.test\r\nSubject: exact consumer poll\r\n"
                      b"Message-ID: <consumer-poll@example.invalid>\r\n"
                      b"\r\nsigned source body\r\n")
        article = node["base"] / "authored.eml"
        article.write_bytes(source)
        self.accepted("hybrid-enroll", node["control"], "1", principal,
                      ed_public, ml_public)
        signatures = self.accepted("hybrid-sign", principal, ed_public,
                                   ed_secret, ml_public, ml_private, article)
        parts = dict(line.split() for line in signatures.stdout.decode("ascii").splitlines())
        ed_sig = node["base"] / "ed.sig"
        ml_sig = node["base"] / "ml.sig"
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        self.accepted("hybrid-author", node["control"], "1", article,
                      ed_sig, ml_sig, ml_public)

        poll_cursor = node["base"] / "polled.fncu"
        report_path = node["base"] / "polled.event"
        self.consumer("poll", node, "worker", poll_cursor, report_path)
        continuation = poll_cursor.read_bytes()
        report = report_path.read_bytes()
        self.assertTrue(continuation.startswith(b"fncu\x01"))
        self.assertNotEqual(continuation, before)
        self.assertTrue(report)
        self.assertEqual(self.position(node, "worker",
                                       node["base"] / "pre-ack.fncu"), before)

        # ACL2 decodes and checks the returned parent and its exact signed
        # source. Python only transports the returned Store event octets.
        bridge = run_store.Acl2Store()
        try:
            form = ("(let ((decoded (fn-stxa-decode-exact '" +
                    bridge.literal(report) + "))) "
                    "(and (fn-stmt-okp decoded) "
                    "(let* ((event (fn-stmt-value decoded)) "
                    "(record-result (fn-record-decode-exact "
                    "(fn-stxa-article-record event)))) "
                    "(and (fn-stxa-bindsp event) "
                    "(equal (fn-stxa-authored-source event) '" +
                    bridge.literal(source) + ") "
                    "(fn-record-result-okp record-result))))))")
            self.assertTrue(run_store.acl2_boolean(bridge.call(form)))
        finally:
            bridge.close()

        # Poll is read-only even when repeated; only an explicit ack commits
        # the returned frontier. Lose the reply after that durable ack.
        second_cursor = node["base"] / "second-polled.fncu"
        second_report = node["base"] / "second-polled.event"
        self.consumer("poll", node, "worker", second_cursor, second_report)
        self.assertEqual(second_cursor.read_bytes(), continuation)
        self.assertEqual(second_report.read_bytes(), report)

        # Optional cross-process Mini join.  The external driver must itself
        # call the live local poll route and establish its signed result; this
        # handoff only keeps the synthetic owner open until that work finishes.
        handoff_name = os.environ.get("FN_CONSUMER_POLL_LIVE_HANDOFF_DIR")
        if handoff_name:
            handoff = Path(handoff_name)
            self.assertTrue(handoff.is_absolute())
            handoff.mkdir(parents=True, exist_ok=False)
            ready = {
                "version": 1,
                "control": str(node["control"]),
                "consumer": "worker",
                "registered_cursor": str(node["base"] / "registered.fncu"),
                "poll_cursor": str(poll_cursor),
                "poll_report": str(report_path),
                "authored_source": str(article),
                "principal": str(principal),
                "ed_public": str(ed_public),
                "ml_public": str(ml_public),
            }
            (handoff / "ready.json").write_text(
                json.dumps(ready, sort_keys=True) + "\n", encoding="utf-8")
            deadline = time.monotonic() + 600
            marker = handoff / "mini-finished.marker"
            while not marker.exists() and time.monotonic() < deadline:
                self.assertIsNone(owner.poll(), "synthetic owner died during Mini join")
                time.sleep(0.1)
            self.assertTrue(marker.is_file(), "Mini join handoff timed out")
            self.assertEqual(marker.read_bytes(), b"continue\n")

        self.stop_owner(owner)

        cut_owner = self.start_owner(node, stop_after_submit=True)
        client = subprocess.Popen(
            [str(IMAGE), "--fn", "consumer", "ack", str(node["control"]),
             str(poll_cursor)], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(self.reap, client)
        wait_for_announcement(cut_owner, b"CONTROL-SUBMITTED", timeout=120)
        cut_owner.kill()
        cut_owner.wait(timeout=10)
        stdout, stderr = client.communicate(timeout=30)
        self.assertEqual(client.returncode, 3, (stdout + stderr).decode())

        reopened = self.start_owner(node)
        self.assertEqual(self.position(node, "worker",
                                       node["base"] / "recovered-ack.fncu"),
                         continuation)
        after_cursor = node["base"] / "after-ack-poll.fncu"
        after_report = node["base"] / "after-ack-poll.event"
        self.consumer("poll", node, "worker", after_cursor, after_report)
        self.assertEqual(after_report.read_bytes(), b"")
        self.stop_owner(reopened)

        # Optional byte-for-byte synthetic fixture for an independent
        # consumer. The test validates it before publication and makes no
        # decision from these copied bytes.
        export_name = os.environ.get("FN_CONSUMER_POLL_EVIDENCE_DIR")
        if export_name:
            export = Path(export_name)
            self.assertTrue(export.is_absolute())
            export.mkdir(parents=True, exist_ok=False)
            (export / "authored.source").write_bytes(source)
            # This token arrived from REGISTER before the article and poll.
            # It is an independent temporal scope pin for a downstream test.
            (export / "registered.fncu").write_bytes(before)
            (export / "accepted.fn-e").write_bytes(report)
            (export / "continuation.fncu").write_bytes(continuation)
            (export / "principal.bin").write_bytes(principal.read_bytes())
            (export / "ed-public.bin").write_bytes(ed_public.read_bytes())
            (export / "ml-public.pem").write_bytes(ml_public.read_bytes())

    @unittest.skipUnless(sys.platform.startswith("linux") and os.geteuid() == 0
                         and shutil.which("setpriv"),
                         "requires Linux root and setpriv to offer a distinct "
                         "SO_PEERCRED uid to the real owner socket")
    def test_different_local_uid_is_refused_by_owner(self):
        node = self.node("foreign-uid")
        owner = self.start_owner(node)
        self.bootstrap(node)
        self.register(node, "worker", node["base"] / "owner.fncu")
        self.root.chmod(0o755)
        node["base"].chmod(0o755)
        node["control"].chmod(0o666)  # pass the filesystem gate in this fixture
        target = node["base"] / "foreign.fncu"
        result = subprocess.run(
            ["setpriv", "--reuid", "65534", "--regid", "65534",
             "--clear-groups", str(IMAGE), "--fn", "consumer", "position",
             str(node["control"]), "worker", str(target)],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=30, check=False)
        self.assertEqual(result.returncode, 1,
                         result.stderr.decode("utf-8", "replace"))
        self.assertFalse(target.exists())
        self.position(node, "worker", node["base"] / "owner-still.fncu")
        self.stop_owner(owner)


if __name__ == "__main__":
    unittest.main()
