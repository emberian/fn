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
from pathlib import Path
import re
import select
import signal
import socket
import ssl
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
PRODUCTION = os.environ.get("FN_NATIVE_HOST")
DEVELOPER = os.environ.get("FN_NATIVE_DEVELOPER_HOST")
IMAGES = [(name, Path(value)) for name, value in
          (("production", PRODUCTION), ("developer", DEVELOPER)) if value]
READY = bool(IMAGES) and all(p.is_file() and os.access(p, os.X_OK) for _, p in IMAGES)
# The wake bound: from the post's 240 to the waiting process's exit.
WAKE_BOUND = 5.0
CAPACITY = 12


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


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
        self.cursor = node["root"] / ("cursor-" + tag)
        self.report = node["root"] / ("report-" + tag)
        words = [str(node["image"]), "--fn", "consumer"]
        if secret is None:
            words += ["wait", str(node["control"]), name]
        else:
            words += ["bound-wait", str(node["control"]), name,
                      str(node["secrets"][secret])]
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


@unittest.skipUnless(READY, "set FN_NATIVE_HOST and/or FN_NATIVE_DEVELOPER_HOST")
class NativeAgentWaitTests(unittest.TestCase):
    def node(self, image):
        root = Path(tempfile.mkdtemp(prefix="fn-agent-wait-"))
        self.addCleanup(subprocess.run, ["rm", "-rf", str(root)], check=False)
        port, tls_port = free_port(), free_port()
        cert, key = root / "cert.pem", root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout",
                        str(key), "-out", str(cert), "-days", "2", "-nodes",
                        "-subj", "/CN=127.0.0.1",
                        "-addext", "subjectAltName=IP:127.0.0.1"], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        config = root / "fn.toml"
        control = root / "control.sock"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nprotected_only = true\n'.format(
                root / "store", port, tls_port, cert, key, control),
            encoding="ascii")
        secrets = {}
        for login in ("alice", "bob"):
            path = root / ("secret-" + login)
            path.write_bytes(("pw-" + login + "\n").encode("ascii"))
            os.chmod(path, 0o600)
            secrets[login] = path
        return {"image": image, "config": config, "port": port, "tls_port": tls_port,
                "cert": cert, "control": control, "root": root, "secrets": secrets,
                "process": None}

    def native(self, node, *words):
        result = subprocess.run(
            [str(node["image"]), "--fn", *map(str, words)],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=240, check=False)
        print("NATIVE-AGENT-WAIT", " ".join(map(str, words[:3])), "->",
              result.returncode)
        return result

    def ok(self, node, *words):
        result = self.native(node, "operator", node["config"], *words)
        self.assertEqual(result.returncode, 0, text(result))
        return result

    def consumer(self, node, verb, *args):
        return self.native(node, "consumer", verb, node["control"], *args)

    def start(self, node):
        process = subprocess.Popen(
            [str(node["image"]), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
        node["process"] = process
        self.addCleanup(self.reap, node)
        seen = 0
        for _ in range(6):
            self.assertTrue(select.select([process.stdout], [], [], 240)[0])
            if process.stdout.readline().startswith(b"LISTENING"):
                seen += 1
                if seen == 2:
                    return
        self.fail("owner readiness output was malformed")

    def stop(self, node):
        process = node["process"]
        process.send_signal(signal.SIGTERM)
        self.assertEqual(process.wait(timeout=60), 0)
        self.reap(node)

    def reap(self, node):
        process, node["process"] = node["process"], None
        if process is None:
            return
        if process.poll() is None:
            process.send_signal(signal.SIGKILL)
            process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            if stream and not stream.closed:
                stream.close()

    def tls(self, node):
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        context.check_hostname = False
        context.verify_mode = ssl.CERT_NONE
        raw = socket.create_connection(("127.0.0.1", node["tls_port"]), timeout=60)
        stream = context.wrap_socket(raw).makefile("rwb", buffering=0)
        self.addCleanup(stream.close)
        stream.readline()
        return stream

    @staticmethod
    def line(stream, command):
        stream.write(command.encode("ascii") + b"\r\n")
        return stream.readline().decode("ascii", "replace").rstrip("\r\n")

    def account(self, node, login):
        result = self.ok(node, "account", "invite", "--expires", "3600")
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, text(result))
        stream = self.tls(node)
        self.assertTrue(self.line(stream, "XREDEEM {} {}".format(
            codes[0].decode("ascii"), login)).startswith("381"))
        self.assertTrue(self.line(stream, "XREDEEM PASS pw-" + login).startswith("281"))

    def post(self, node, group, tag, login="alice"):
        """Post one article; the monotonic time of its 240."""
        stream = self.tls(node)
        self.assertTrue(self.line(stream, "AUTHINFO USER " + login).startswith("381"))
        self.assertTrue(self.line(stream, "AUTHINFO PASS pw-" + login).startswith("281"))
        self.assertTrue(self.line(stream, "POST").startswith("340"))
        stream.write(("From: {0}@example.invalid\r\nNewsgroups: {1}\r\n"
                      "Subject: {2}\r\nMessage-ID: <{2}@example.invalid>\r\n\r\n"
                      "what is the news?\r\n.\r\n".format(login, group, tag))
                     .encode("ascii"))
        reply = stream.readline().decode("ascii", "replace")
        accepted = time.monotonic()
        self.assertTrue(reply.startswith("240"), (tag, reply))
        return accepted

    def ack(self, node, cursor, secret):
        return self.consumer(node, "bound-ack", cursor,
                             node["secrets"][secret]).returncode

    def agent(self, node, login, *words, stdin=b""):
        config = node["root"] / ("agent-" + login + ".json")
        if not config.exists():
            config.write_text(json.dumps({
                "image": str(node["image"]), "control": str(node["control"]),
                "consumer": login + "-inbox", "secret_file": str(node["secrets"][login]),
                "login": login, "from": "{0} <{0}@example.invalid>".format(login),
                "node": "127.0.0.1:{}".format(node["port"]), "cafile": str(node["cert"]),
                "state": str(node["root"] / ("agent-state-" + login))}), encoding="utf-8")
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
        self.start(node)
        for login in ("alice", "bob"):
            self.account(node, login)
            self.ok(node, "account", "access", login, "--read", "fn." + login,
                    "--post", "fn.*")
        self.assertEqual(self.consumer(node, "bootstrap").returncode, 0)
        for login in ("alice", "bob"):
            name = login + "-inbox"
            result = self.consumer(node, "register", name, "fn." + login,
                                   node["root"] / ("registered-" + name))
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
        self.stop(node)
        self.start(node)
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
        self.stop(node)

    def test_two_agents_wait_for_their_own_news(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.scenario(image)


if __name__ == "__main__":
    unittest.main()
