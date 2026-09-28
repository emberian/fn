"""Real local-owner E2 cursor declarations through one saved native image.

Requires the combined consumer-local command and production bootstrap.
The cursor files are ACL2 output; this test never constructs or edits fncu bytes.
The first two cases exercise declarations at position zero.  The gated
signed-poll case (FN_RUN_CONSUMER_POLL_E2E=1) drives `consumer poll`, checks
the exact signed composite through ACL2, and loses a positive ack reply.
Consumer inbox processing is tests/test_native_consumer_exchange.py.
"""

import os
import json
import re
from pathlib import Path
import shutil
import sys
import time
import unittest

from tests.native_harness import (
    EXIT_OK, EXIT_UNCERTAIN, Node, acl2_boolean, assert_outcome, environment,
    native_image, requires, run, scratch, start)


IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
ENABLED = os.environ.get("FN_RUN_CONSUMER_E2E") == "1"


@unittest.skipUnless(ENABLED, "set FN_RUN_CONSUMER_E2E=1 and a source-matched "
                     "FN_NATIVE_DEVELOPER_HOST")
@requires(IMAGE)
class NativeConsumerE2Tests(unittest.TestCase):
    def setUp(self):
        self.root = scratch(self, "fn-consumer-e2-")
        self.env = environment()

    def native(self, *words, env=None, timeout=120):
        return run([IMAGE, "--fn", *words], env=env or self.env, timeout=timeout)

    def accepted(self, *words, env=None):
        return assert_outcome(self, self.native(*words, env=env), EXIT_OK)

    def node(self, name):
        """A node under ROOT/NAME whose store `store init` made."""
        node = Node(self, IMAGE, root=self.root / name, name=name)
        self.accepted("store", node.store_path, "init", "fn.test")
        return node

    def start_owner(self, node, *, stop_after_submit=False):
        return node.start(timeout=120, env={"FN_NATIVE_CONTROL_TEST_STOP": "after-submit"}
                          if stop_after_submit else None)

    def stop_owner(self, proc):
        assert_outcome(self, proc.stop(grace=60), EXIT_OK, log=proc)

    def lose_reply(self, owner, words):
        """Run `fn WORDS` against an owner stopped after it completes the
        request; kill the owner before it replies.  The client's (stdout, stderr)."""
        client = start([IMAGE, "--fn", *words], env=self.env)
        self.addCleanup(client.stop, 10)
        owner.announcement(b"CONTROL-SUBMITTED", timeout=120)
        owner.kill()  # actual process death after durable completion, pre-reply
        owner.wait(timeout=10)
        owner.finish()
        stdout, stderr = client.communicate(timeout=30)
        self.assertEqual(client.returncode, EXIT_UNCERTAIN, (stdout + stderr).decode())
        return stdout, stderr

    def consumer(self, verb, node, *args, expected=0):
        result = self.native("consumer", verb, node.control, *args)
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

    def status(self, node, name, *, expected=0):
        result = self.consumer("status", node, name, expected=expected)
        if expected:
            self.assertIn(b"consumer status refused", result.stdout)
            return None
        match = re.search(
            rb"consumer status accepted committed-ack=(\d+) "
            rb"committed-journal-frontier=(\d+) journal-event-distance=(\d+)",
            result.stdout)
        self.assertIsNotNone(match, result.stdout)
        ack, frontier, distance = map(int, match.groups())
        self.assertLessEqual(ack, frontier)
        self.assertEqual(distance, frontier - ack)
        return ack, frontier, distance

    def test_durable_scope_ack_and_unrelated_article(self):
        first = self.node("first")
        owner = self.start_owner(first)
        # PKT-709: `fn consumer' prints the grammar (exit 0), and `register'
        # bootstraps the node's consumer history itself; an explicit
        # bootstrap afterwards is the refused duplicate.
        usage = self.native("consumer")
        self.assertEqual(usage.returncode, 0, usage.stderr)
        self.assertIn(b"register CONTROL NAME GROUP CURSOR-OUT", usage.stdout)
        refused = self.native("consumer", "register", first.control, "worker")
        self.assertEqual(refused.returncode, 5, refused.stderr)
        self.assertIn(b"usage: fn consumer [--json] COMMAND CONTROL", refused.stderr)
        token_path = first.root / "initial.fncu"
        initial = self.register(first, "worker", token_path)
        self.consumer("bootstrap", first, expected=1)
        self.assertEqual(self.position(first, "worker",
                                       first.root / "before.fncu"), initial)
        before_status = self.status(first, "worker")
        self.assertEqual(before_status[0], 0)
        self.assertIsNone(self.status(first, "unknown", expected=1))

        # A normal accepted article adds a Store record but does not declare
        # consumer processing. The native POSITION output remains unchanged.
        msgid = "<consumer-unrelated@example.invalid>"
        source = (b"From: author@example.invalid\r\n"
                  b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                  b"Newsgroups: fn.test\r\nSubject: unrelated\r\n"
                  b"Message-ID: " + msgid.encode("ascii") +
                  b"\r\n\r\nunrelated exact body\r\n")
        article = first.root / "unrelated.eml"
        article.write_bytes(source)
        self.accepted("operator", first.config, "post", "--message-id",
                      msgid, "--payload", article, "--group", "fn.test")
        self.assertEqual(self.position(first, "worker",
                                       first.root / "after-post.fncu"), initial)
        after_post_status = self.status(first, "worker")
        self.assertEqual(after_post_status[0], before_status[0])
        self.assertGreater(after_post_status[1], before_status[1])
        self.assertGreater(after_post_status[2], before_status[2])
        self.assertIn(b"consumer accepted",
                      self.consumer("ack", first, token_path).stdout)
        self.assertEqual(self.position(first, "worker",
                                       first.root / "after-ack.fncu"), initial)

        # The same ID in an independent history cannot use this cursor.
        other = self.node("other")
        other_owner = self.start_owner(other)
        self.bootstrap(other)
        other_token = self.register(other, "worker", other.root / "other.fncu")
        self.assertNotEqual(other_token, initial)
        self.consumer("ack", other, token_path, expected=1)
        self.assertEqual(self.position(other, "worker",
                                       other.root / "other-position.fncu"),
                         other_token)

        self.consumer("unregister", first, "worker")
        self.position(first, "worker", first.root / "removed.fncu", expected=1)
        current = self.register(first, "worker", first.root / "renewed.fncu")
        self.assertNotEqual(current, initial)  # durable registration epoch
        self.consumer("ack", first, token_path, expected=1)
        self.assertEqual(self.position(first, "worker",
                                       first.root / "renewed-position.fncu"),
                         current)
        self.stop_owner(owner)
        self.stop_owner(other_owner)
        inspected = self.accepted("store", first.store_path, "inspect", msgid)
        self.assertIn(b"unrelated exact body", inspected.stdout)
        reopened = self.start_owner(first)
        self.assertEqual(self.position(first, "worker",
                                       first.root / "reopened.fncu"), current)
        self.assertEqual(self.status(first, "worker")[0], 0)
        self.stop_owner(reopened)

    def test_refusals_name_their_reason_json_lines_and_bind_of_an_unknown_name(self):
        """PKT-709 (CNS-009, PRF-263): a refusal names the owner's reason
        (the reasoned consumer request, FNCT kind 22, answered with the
        reasoned reply); `--json` prints ACL2's one JSON line; `consumer
        bind` of a name no registration declared is refused by name."""
        node = self.node("reasons")
        owner = self.start_owner(node)
        self.register(node, "worker", node.root / "worker.fncu")
        # The reason, in text.
        status = self.consumer("status", node, "ghost", expected=1)
        self.assertIn(b"consumer status refused unknown-consumer", status.stdout)
        poll = self.consumer("poll", node, "ghost", node.root / "g.fncu",
                             node.root / "g.report", expected=1)
        self.assertIn(b"consumer refused unknown-consumer", poll.stdout)
        # The same, as JSON; every line is one JSON object.
        refused = self.native("consumer", "--json", "poll", node.control, "ghost",
                              node.root / "g2.fncu", node.root / "g2.report")
        self.assertEqual(refused.returncode, 1, refused.stderr)
        line = json.loads(refused.stdout.decode("ascii").strip().splitlines()[-1])
        self.assertEqual(line, {"command": "poll", "outcome": "refused",
                                "reason": "unknown-consumer"})
        counts = self.native("consumer", "--json", "status", node.control, "worker")
        self.assertEqual(counts.returncode, 0, counts.stderr)
        line = json.loads(counts.stdout.decode("ascii").strip().splitlines()[-1])
        self.assertEqual(line["outcome"], "accepted")
        self.assertIsNone(line["reason"])
        self.assertEqual(line["journal_event_distance"],
                         line["journal_frontier"] - line["committed_ack"])
        empty = self.native("consumer", "--json", "poll", node.control, "worker",
                            node.root / "w.fncu", node.root / "w.report")
        self.assertEqual(empty.returncode, 0, empty.stderr)
        line = json.loads(empty.stdout.decode("ascii").strip().splitlines()[-1])
        self.assertEqual((line["outcome"], line["report"]), ("accepted", "empty"))
        # `fn consumer-article` on the empty report names it.
        article = self.native("consumer-article", "--json", node.root / "w.report")
        self.assertEqual(article.returncode, 1, article.stderr)
        self.assertEqual(json.loads(article.stdout.decode("ascii").strip()),
                         {"report": "empty"})
        # A bind of a name no registration declared is refused by name; the
        # registered one is bound.
        ghost = self.native("operator", node.config, "consumer", "bind",
                            "ghost", "--account", "bob")
        self.assertEqual(ghost.returncode, 1, ghost.stdout + ghost.stderr)
        self.assertIn(b"unknown-consumer", ghost.stdout + ghost.stderr)
        bound = self.native("operator", node.config, "consumer", "bind",
                            "worker", "--account", "bob")
        self.assertEqual(bound.returncode, 0, bound.stdout + bound.stderr)
        # The plain poll of the now bound consumer names why it is refused.
        plain = self.consumer("poll", node, "worker", node.root / "b.fncu",
                              node.root / "b.report", expected=1)
        self.assertIn(b"consumer refused bound", plain.stdout)
        self.stop_owner(owner)

    def test_lost_register_reply_resolves_by_reopened_position(self):
        node = self.node("uncertain")
        bootstrap_owner = self.start_owner(node)
        self.bootstrap(node)
        self.stop_owner(bootstrap_owner)
        owner = self.start_owner(node, stop_after_submit=True)
        token_path = node.root / "lost-reply.fncu"
        self.lose_reply(owner, ("consumer", "register", node.control, "worker", "fn.test",
                                token_path))
        self.assertFalse(token_path.exists())

        reopened = self.start_owner(node)
        recovered = self.position(node, "worker", node.root / "recovered.fncu")
        # Same-scope registration is idempotent after replay: no fresh epoch.
        again = self.register(node, "worker", node.root / "again.fncu")
        self.assertEqual(again, recovered)
        self.consumer("ack", node, node.root / "recovered.fncu")
        self.assertEqual(self.position(node, "worker",
                                       node.root / "after-resolution.fncu"),
                         recovered)
        self.stop_owner(reopened)

    @unittest.skipUnless(os.environ.get("FN_RUN_CONSUMER_POLL_E2E") == "1",
                         "requires the ACL2-owned consumer poll command")
    def test_signed_composite_poll_and_lost_positive_ack_reply(self):

        node = self.node("signed-poll")
        owner = self.start_owner(node)
        self.bootstrap(node)
        before = self.register(node, "worker", node.root / "registered.fncu")

        principal = node.root / "principal.bin"
        ed_public = node.root / "ed-public.bin"
        ed_secret = node.root / "ed-secret.bin"
        ml_private = node.root / "ml-private.pem"
        ml_public = node.root / "ml-public.pem"
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        made = run([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out", ml_private],
                   env=self.env, timeout=60)
        self.assertEqual(made.returncode, 0, made.stderr.decode("utf-8", "replace"))
        exported = run([openssl, "pkey", "-in", ml_private, "-pubout", "-out", ml_public],
                       env=self.env, timeout=60)
        self.assertEqual(exported.returncode, 0,
                         exported.stderr.decode("utf-8", "replace"))

        source_name = os.environ.get("FN_CONSUMER_POLL_SOURCE_FILE")
        if source_name:
            source_path = Path(source_name)
            self.assertTrue(source_path.is_absolute() and source_path.is_file())
            source = source_path.read_bytes()
        else:
            # Local injection requires a Date (an undated source is refused
            # before the owner, as qual-bbf52159's dated-source rerun found).
            source = (b"From: author@example.invalid\r\n"
                      b"Date: Fri, 25 Sep 2026 12:00:00 +0000\r\n"
                      b"Newsgroups: fn.test\r\nSubject: exact consumer poll\r\n"
                      b"Message-ID: <consumer-poll@example.invalid>\r\n"
                      b"\r\nsigned source body\r\n")
        article = node.root / "authored.eml"
        article.write_bytes(source)
        self.accepted("hybrid-enroll", node.control, "1", principal,
                      ed_public, ml_public)
        signatures = self.accepted("hybrid-sign", principal, ed_public,
                                   ed_secret, ml_public, ml_private, article)
        parts = dict(line.split() for line in signatures.stdout.decode("ascii").splitlines())
        ed_sig = node.root / "ed.sig"
        ml_sig = node.root / "ml.sig"
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        self.accepted("hybrid-author", node.control, "1", article,
                      ed_sig, ml_sig, ml_public)

        poll_cursor = node.root / "polled.fncu"
        report_path = node.root / "polled.event"
        self.consumer("poll", node, "worker", poll_cursor, report_path)
        continuation = poll_cursor.read_bytes()
        report = report_path.read_bytes()
        self.assertTrue(continuation.startswith(b"fncu\x01"))
        self.assertNotEqual(continuation, before)
        self.assertTrue(report)
        self.assertEqual(self.position(node, "worker",
                                       node.root / "pre-ack.fncu"), before)

        # ACL2 decodes and checks the returned parent and its exact signed
        # source. Python only transports the returned Store event octets.
        with Acl2Session(IMAGE) as bridge:
            form = ("(let ((decoded (fn-stxa-decode-exact '" +
                    bridge.literal(report) + "))) "
                    "(and (fn-stmt-okp decoded) "
                    "(let* ((event (fn-stmt-value decoded)) "
                    "(record-result (fn-record-decode-exact "
                    "(fn-stxa-article-record event)))) "
                    "(and (fn-stxa-bindsp event) "
                    "(equal (fn-stxa-authored-source event) '" +
                    bridge.literal(source) + ") "
                    "(fn-record-result-okp record-result)))))")
            self.assertTrue(acl2_boolean(bridge.call(form)))

        # Poll is read-only even when repeated; only an explicit ack commits
        # the returned frontier. Lose the reply after that durable ack.
        second_cursor = node.root / "second-polled.fncu"
        second_report = node.root / "second-polled.event"
        self.consumer("poll", node, "worker", second_cursor, second_report)
        self.assertEqual(second_cursor.read_bytes(), continuation)
        self.assertEqual(second_report.read_bytes(), report)
        status_before_ack = self.status(node, "worker")
        self.assertEqual(status_before_ack[0], 0)

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
                "control": str(node.control),
                "consumer": "worker",
                "registered_cursor": str(node.root / "registered.fncu"),
                "poll_cursor": str(poll_cursor),
                "poll_report": str(report_path),
                "authored_source": str(article),
                "principal": str(principal),
                "ed_public": str(ed_public),
                "ml_public": str(ml_public),
            }
            ready_tmp = handoff / "ready.json.tmp"
            ready_tmp.write_text(
                json.dumps(ready, sort_keys=True) + "\n", encoding="utf-8")
            ready_tmp.replace(handoff / "ready.json")
            deadline = time.monotonic() + 600
            marker = handoff / "mini-finished.marker"
            # The external driver publishes this marker by same-directory
            # rename after its own evidence files are complete.
            while not marker.exists() and time.monotonic() < deadline:
                self.assertIsNone(owner.poll(), "synthetic owner died during Mini join")
                time.sleep(0.1)
            self.assertTrue(marker.is_file(), "Mini join handoff timed out")
            self.assertEqual(marker.read_bytes(), b"continue\n")

        self.stop_owner(owner)

        cut_owner = self.start_owner(node, stop_after_submit=True)
        self.lose_reply(cut_owner, ("consumer", "ack", node.control, poll_cursor))

        reopened = self.start_owner(node)
        self.assertEqual(self.position(node, "worker",
                                       node.root / "recovered-ack.fncu"),
                         continuation)
        status_after_ack = self.status(node, "worker")
        self.assertGreater(status_after_ack[0], status_before_ack[0])
        after_cursor = node.root / "after-ack-poll.fncu"
        after_report = node.root / "after-ack-poll.event"
        self.consumer("poll", node, "worker", after_cursor, after_report)
        self.assertEqual(after_report.read_bytes(), b"")
        self.assertEqual(self.status(node, "worker"), status_after_ack)
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
        self.register(node, "worker", node.root / "owner.fncu")
        self.root.chmod(0o755)
        node.root.chmod(0o755)
        node.control.chmod(0o666)  # pass the filesystem gate in this fixture
        target = node.root / "foreign.fncu"
        result = run(["setpriv", "--reuid", "65534", "--regid", "65534",
                      "--clear-groups", IMAGE, "--fn", "consumer", "position",
                      node.control, "worker", target], env=self.env, timeout=30)
        self.assertEqual(result.returncode, 1,
                         result.stderr.decode("utf-8", "replace"))
        self.assertFalse(target.exists())
        self.position(node, "worker", node.root / "owner-still.fncu")
        self.stop_owner(owner)


if __name__ == "__main__":
    unittest.main()
