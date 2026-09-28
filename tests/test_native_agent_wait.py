"""SCN-172: agents sleep until there is news (PRF-252, CNS-007).

One node, two invitation-code accounts, alice and bob, each reading only its
own group (`account access LOGIN --read fn.LOGIN --post fn.*`), and two
consumers bound to them: alice-inbox on fn.alice, bob-inbox on fn.bob.

  * Both agents wait (`consumer bound-wait ... --timeout 60`) at once; a post
    to fn.bob wakes bob's wait, which answers the post within WAKE_BOUND
    seconds of the post's 240, while alice's wait sleeps on.  A post to
    fn.alice then wakes alice's.
  * A wait with nothing new answers the empty page at its timeout (exit 0,
    an empty report), not before.
  * Twelve waits are admitted at once (fn-cwait-capacity); the thirteenth is
    refused (exit 1) at once; one post wakes all twelve with the same event.
  * An owner restart keeps both cursors: bob's acked event is not delivered
    again (his wait times out empty), alice's unacked one is (at-least-once).
  * tools/fn_agent.py drives a whole exchange without NNTP in the agent:
    bob's `next` prints alice's question as JSON, his `reply` posts to
    fn.alice with References set, his `ack` acks it; alice's `next` prints
    the reply with the question's Message-ID in its References.

Each wait is one `fn consumer (bound-)wait` process: it sleeps in the owner
(books/consumer-wait.lisp fn-cwait-step; host/native/owner.lisp
fnn-owner-consumer-local-wait, woken by fnn-owner-signal-commit), never
polling.  The scenario runs on the production image (FN_NATIVE_HOST) and on
the developer image (FN_NATIVE_DEVELOPER_HOST).

Run: FN_NATIVE_HOST=<production launcher> FN_NATIVE_DEVELOPER_HOST=<developer
launcher> python3 -m unittest -v tests.test_native_agent_wait
"""

import json
import os
import re
import subprocess
import sys
import time
import unittest

from tests.native_harness import (
    ROOT, Client, Node, article, client_context, environment, executable, native_image)

IMAGES = [("production", native_image("FN_NATIVE_HOST")),
          ("developer", native_image("FN_NATIVE_DEVELOPER_HOST"))]
READY = all(executable(p) for _, p in IMAGES)
# The wake bound: from the post's 240 to the waiting process's exit.
WAKE_BOUND = 5.0
CAPACITY = 12


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace").strip()


class AgentWaitSourceTests(unittest.TestCase):
    def test_the_host_calls_the_wait_decisions(self):
        host = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        # The step over the live arena (records flip), with the view's
        # withdrawals in its page (PKT-710, books/consumer-withdrawal.lisp).
        self.assertIn("(fn-cwd-wait-step-over (fn-owner-ocfg state) (fn-owner-auth state)", host)
        self.assertIn("(fn-cwait-admit waiters)", host)
        control = (ROOT / "host" / "native-control-host.lisp").read_text(encoding="ascii")
        self.assertIn("(fn-cwait-request-decode octets)", control)
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="ascii")
        # The wake is the durable publication's, and the sleep is a
        # condition wait, not a timer loop.
        self.assertIn("(fnn-owner-signal-commit service)\n    :durable", owner)
        self.assertIn("sb-thread:condition-wait queue lock", owner)


class Wait:
    """One `consumer (bound-)wait` process and its two output files."""

    def __init__(self, test, node, name, secret, seconds):
        tag = name + "-" + os.urandom(4).hex()
        self.cursor = node.root / ("cursor-" + tag)
        self.report = node.root / ("report-" + tag)
        words = [str(node.image), "--fn", "consumer"]
        if secret is None:
            words += ["wait", str(node.control), name]
        else:
            words += ["bound-wait", str(node.control), name, str(node.secrets[secret])]
        words += [str(self.cursor), str(self.report), "--timeout", str(seconds)]
        self.started = time.monotonic()
        self.process = subprocess.Popen(words, cwd=ROOT, env=environment(),
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        test.addCleanup(self.kill)

    def kill(self):
        if self.process.poll() is None:
            self.process.kill()
        self.process.communicate()

    def finish(self, timeout):
        """(exit code, message tag or None, seconds since start)."""
        out, err = self.process.communicate(timeout=timeout)
        elapsed = time.monotonic() - self.started
        code = self.process.returncode
        print("NATIVE-AGENT-WAIT wait ->", code, "after %.2f s" % elapsed,
              (out + err).decode("utf-8", "replace").strip()[-200:])
        if code != 0:
            return code, None, elapsed
        found = re.findall(rb"<([a-z0-9-]+)@example\.invalid>", self.report.read_bytes())
        return 0, (found[0].decode("ascii") if found else None), elapsed


@unittest.skipUnless(READY, "the production and developer images are required")
class NativeAgentWaitTests(unittest.TestCase):
    def node(self, image):
        node = Node(self, image).use_tls(alt_name=True)
        node.secrets = {}
        for login in ("alice", "bob"):
            path = node.root / ("secret-" + login)
            path.write_bytes(("pw-" + login + "\n").encode("ascii"))
            os.chmod(path, 0o600)
            node.secrets[login] = path
        return node

    def native(self, node, *words):
        result = node.invoke(*words, timeout=240)
        print("NATIVE-AGENT-WAIT", " ".join(map(str, words[:3])), "->",
              result.returncode)
        return result

    def ok(self, node, *words):
        result = self.native(node, "operator", node.config, *words)
        self.assertEqual(result.returncode, 0, text(result))
        return result

    def consumer(self, node, verb, *args):
        return self.native(node, "consumer", verb, node.control, *args)

    def tls(self, node):
        client = Client(node.tls_port, timeout=60, implicit_tls=client_context(),
                        greeting=None)
        self.addCleanup(client.close)
        return client

    @staticmethod
    def line(client, command):
        return client.command(command).decode("ascii", "replace").rstrip("\r\n")

    def account(self, node, login):
        result = self.ok(node, "account", "invite", "--expires", "3600")
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, text(result))
        client = self.tls(node)
        self.assertTrue(self.line(client, "XREDEEM {} {}".format(
            codes[0].decode("ascii"), login)).startswith("381"))
        self.assertTrue(self.line(client, "XREDEEM PASS pw-" + login).startswith("281"))

    def post(self, node, group, tag, login="alice"):
        """Post one article; the monotonic time of its 240."""
        client = self.tls(node)
        self.assertTrue(self.line(client, "AUTHINFO USER " + login).startswith("381"))
        self.assertTrue(self.line(client, "AUTHINFO PASS pw-" + login).startswith("281"))
        first, final = client.post(article(
            "<{}@example.invalid>".format(tag), groups=group, subject=tag,
            sender=login + "@example.invalid", date=None, body=b"what is the news?\r\n"))
        self.assertTrue(first.startswith(b"340"), first)
        reply = final.decode("ascii", "replace")
        accepted = time.monotonic()
        self.assertTrue(reply.startswith("240"), (tag, reply))
        return accepted

    def ack(self, node, cursor, secret):
        return self.consumer(node, "bound-ack", cursor,
                             node.secrets[secret]).returncode

    def agent(self, node, login, *words, stdin=b""):
        config = node.root / ("agent-" + login + ".json")
        if not config.exists():
            config.write_text(json.dumps({
                "image": str(node.image), "control": str(node.control),
                "consumer": login + "-inbox", "secret_file": str(node.secrets[login]),
                "login": login, "from": "{0} <{0}@example.invalid>".format(login),
                "node": "127.0.0.1:{}".format(node.port), "cafile": str(node.cert),
                "state": str(node.root / ("agent-state-" + login))}), encoding="utf-8")
        result = subprocess.run([sys.executable, str(ROOT / "tools" / "fn_agent.py"),
                                 str(config), *words], input=stdin, cwd=ROOT,
                                env=environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=300, check=False)
        print("NATIVE-AGENT-WAIT fn_agent", login, words[0], "->", result.returncode,
              result.stdout.decode("utf-8", "replace").strip()[-300:])
        lines = result.stdout.decode("utf-8").strip().splitlines()
        return result.returncode, (json.loads(lines[-1]) if lines else None), text(result)

    def scenario(self, image):
        node = self.node(image)
        self.ok(node, "init", "local.general")
        for group in ("fn.alice", "fn.bob"):
            self.ok(node, "group", "create", group)
        node.start(timeout=240)
        for login in ("alice", "bob"):
            self.account(node, login)
            self.ok(node, "account", "access", login, "--read", "fn." + login,
                    "--post", "fn.*")
        self.assertEqual(self.consumer(node, "bootstrap").returncode, 0)
        for login in ("alice", "bob"):
            name = login + "-inbox"
            result = self.consumer(node, "register", name, "fn." + login,
                                   node.root / ("registered-" + name))
            self.assertEqual(result.returncode, 0, text(result))
            self.ok(node, "consumer", "bind", name, "--account", login)

        # 1. Two agents asleep; a post to fn.bob wakes bob's, not alice's.
        alice = Wait(self, node, "alice-inbox", "alice", 60)
        bob = Wait(self, node, "bob-inbox", "bob", 60)
        time.sleep(4)
        self.assertIsNone(alice.process.poll(), "alice's wait returned early")
        self.assertIsNone(bob.process.poll(), "bob's wait returned early")
        posted = self.post(node, "fn.bob", "for-bob")
        code, tag, _ = bob.finish(timeout=60)
        woke = time.monotonic() - posted
        print("NATIVE-AGENT-WAIT bob woke %.3f s after the 240" % woke)
        self.assertEqual((code, tag), (0, "for-bob"))
        self.assertLess(woke, WAKE_BOUND)
        time.sleep(2)
        self.assertIsNone(alice.process.poll(), "alice's wait woke for bob's post")
        posted = self.post(node, "fn.alice", "for-alice", login="bob")
        code, tag, _ = alice.finish(timeout=60)
        woke = time.monotonic() - posted
        print("NATIVE-AGENT-WAIT alice woke %.3f s after the 240" % woke)
        self.assertEqual((code, tag), (0, "for-alice"))
        self.assertLess(woke, WAKE_BOUND)
        # bob acks his; alice does not ack hers.
        self.assertEqual(self.ack(node, bob.cursor, "bob"), 0)

        # 2. A timeout answers the empty page, at its deadline.
        empty = Wait(self, node, "bob-inbox", "bob", 3)
        code, tag, elapsed = empty.finish(timeout=60)
        self.assertEqual((code, tag), (0, None))
        self.assertEqual(empty.report.read_bytes(), b"")
        self.assertGreaterEqual(elapsed, 3.0)
        self.assertLess(elapsed, 3.0 + WAKE_BOUND + 10)
        # A wait is refused like the poll it is: the wrong password.
        refused = Wait(self, node, "bob-inbox", "alice", 30)
        code, _, elapsed = refused.finish(timeout=60)
        self.assertEqual(code, 1)
        self.assertLess(elapsed, 20)

        # 3. Twelve waiters; the thirteenth refused; one post wakes all.
        waits = [Wait(self, node, "bob-inbox", "bob", 60) for _ in range(CAPACITY)]
        time.sleep(8)
        for one in waits:
            self.assertIsNone(one.process.poll(), "a waiter returned early")
        extra = Wait(self, node, "bob-inbox", "bob", 60)
        code, _, elapsed = extra.finish(timeout=60)
        self.assertEqual(code, 1, "the thirteenth waiter was not refused")
        self.assertLess(elapsed, 30)
        posted = self.post(node, "fn.bob", "for-all")
        for one in waits:
            self.assertEqual(one.finish(timeout=60)[:2], (0, "for-all"))
        print("NATIVE-AGENT-WAIT twelve woke within %.3f s of the 240"
              % (time.monotonic() - posted))
        self.assertEqual(self.ack(node, waits[0].cursor, "bob"), 0)

        # 4. Restart keeps both cursors.
        node.stop()
        node.start(timeout=240)
        code, tag, elapsed = Wait(self, node, "bob-inbox", "bob", 3).finish(timeout=60)
        self.assertEqual((code, tag), (0, None))
        code, tag, elapsed = Wait(self, node, "alice-inbox", "alice", 30).finish(timeout=60)
        self.assertEqual((code, tag), (0, "for-alice"))
        self.assertLess(elapsed, 20)

        # 5. fn_agent: alice asks bob; bob answers; alice reads the answer.
        code, alice_event, detail = self.agent(node, "alice", "next", "--timeout", "30")
        self.assertEqual(code, 0, detail)
        self.assertEqual(alice_event["message_id"], "<for-alice@example.invalid>")
        self.assertEqual(self.agent(node, "alice", "ack")[0], 0)
        self.post(node, "fn.bob", "question")
        code, event, detail = self.agent(node, "bob", "next", "--timeout", "30")
        self.assertEqual(code, 0, detail)
        self.assertEqual(event["kind"], "article")
        self.assertEqual(event["message_id"], "<question@example.invalid>")
        self.assertEqual(event["groups"], ["fn.bob"])
        self.assertEqual(event["subject"], "question")
        self.assertIn("alice@example.invalid", event["from"])
        self.assertIn("what is the news?", event["body"])
        code, reply, detail = self.agent(node, "bob", "reply", "--subject",
                                         "Re: question", "--group", "fn.alice",
                                         stdin=b"the news is that bob is awake\n")
        self.assertEqual(code, 0, detail)
        self.assertEqual(reply["outcome"], "accepted")
        self.assertEqual(self.agent(node, "bob", "ack")[0], 0)
        code, answer, detail = self.agent(node, "alice", "next", "--timeout", "30")
        self.assertEqual(code, 0, detail)
        self.assertEqual(answer["message_id"], reply["message_id"])
        self.assertEqual(answer["subject"], "Re: question")
        self.assertIn("<question@example.invalid>", answer["references"])
        self.assertIn("bob is awake", answer["body"])
        self.assertEqual(self.agent(node, "alice", "ack")[0], 0)
        code, empty_event, _ = self.agent(node, "bob", "next", "--timeout", "1")
        self.assertEqual((code, empty_event), (0, {"kind": "empty"}))
        node.stop()

    def test_two_agents_wait_for_their_own_news(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.scenario(image)


if __name__ == "__main__":
    unittest.main()
