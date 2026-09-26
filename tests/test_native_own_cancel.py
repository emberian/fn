"""Opt-in native: a friend cancels their own unsigned post (SEC-006, PRF-210).

Three saved-image nodes on loopback.  H requires AUTHINFO and has two
logins, alice and bob; A and B receive over IHAVE from a configured peer.
Nothing is signed: the only authority is the login, carried as RFC 8315
Cancel-Lock / Cancel-Key lines the owner writes (books/cancel-lock.lisp
fn-cl-served-payload, called at host/native/owner.lisp
fnn-owner-attempt-served).

- alice POSTs T: the stored T carries one `Cancel-Lock: sha256:` line,
  directly after the node's Injection-Info line.
- bob POSTs a cancel of T (240, filed): T is still served (220), since
  bob's key opens nothing (fn-ctl-key-record-without-an-opened-lock-
  declines-by-name).
- alice POSTs a cancel of T (240): ARTICLE T answers 430 and OVER over the
  group no longer lists it (fn-ctl-withdrawal-authority-is-exactly-signer-
  or-poster, :poster).  After a SIGKILL and restart the answer is unchanged
  (the decision replays from the two stored articles).
- Across nodes: T, bob's cancel and alice's cancel, as H stored them, are
  relayed to A (target first) and B (cancels first).  Both end at 430 for
  T: alice's key travels in her cancel's octets (visible(T,C) =
  visible(C,T)); after T and bob's cancel alone A still serves T.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_own_cancel
"""

import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = (Path(IMAGE_TEXT) if IMAGE_TEXT else
         next((p for p in (ROOT / "build" / "fn-host-developer", ROOT / "build" / "fn-host")
               if p.is_file()), None))
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
GROUPS = ["fn.own.t", "control.cancel"]
TARGET = "<own-target@example.invalid>"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def article(message_id, extra=None, subject=None):
    lines = ["From: friend <friend@example.invalid>", "Newsgroups: fn.own.t",
             "Subject: " + (subject or "own-cancel " + message_id),
             "Message-ID: " + message_id] + ([extra] if extra else [])
    return ("\r\n".join(lines) + "\r\n\r\nbody\r\n").encode("ascii")


def cancel_of(message_id, target):
    return article(message_id, "Control: cancel " + target, "cmsg cancel " + target)


def stuffed(octets):
    return b"".join((b"." + line if line.startswith(b".") else line)
                    for line in octets.splitlines(keepends=True))


@unittest.skipUnless(READY, "set FN_NATIVE_HOST (a saved fn image)")
class NativeOwnCancelTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-own-cancel-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("FN_HOST", None)
        self.processes = []
        self.addCleanup(self.stop_all)

    def command(self, arguments, expected=0, timeout=180):
        result = subprocess.run(list(map(str, arguments)), cwd=ROOT, env=self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        self.assertEqual(result.returncode, expected, result)
        return result

    def initialize(self, name, auth):
        root = self.base / name
        root.mkdir()
        store = root / "store"
        port = free_port()
        self.command([IMAGE, "--fn", "store", store, "init", *GROUPS])
        config = root / "fn.toml"
        text = ('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                '[control]\npath = "{}"\n'.format(store, port, root / "control.sock"))
        if auth:
            text += ('[auth]\nrequired = true\nprotected_only = false\npath = "{}"\n'
                     .format(root / "credentials.toml"))
        config.write_text(text, encoding="ascii")
        node = {"name": name, "root": root, "config": config, "port": port,
                "store": store, "starts": 0}
        if auth:
            for login in ("alice", "bob"):
                self.command([sys.executable, "bin/fn", "--config", config, "principal",
                              "set-password", login, "--password", login + "-pw",
                              "--posting"], timeout=600)
        else:
            self.command([IMAGE, "--fn", "operator", config, "peer", "add", "source",
                          "source.example.invalid", "127.0.0.1", str(free_port()),
                          "fn.*", "-", "127.0.0.1", "true"])
        return node

    def start(self, node):
        node["starts"] += 1
        log = open(node["root"] / "node-{}.log".format(node["starts"]), "wb")
        self.addCleanup(log.close)
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=log)
        self.processes.append(process)
        node["process"] = process
        wait_for_announcement(process, b"LISTENING ")

    def kill(self, node):
        process = node.pop("process")
        process.kill()
        process.communicate(timeout=60)
        self.processes.remove(process)

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                process.communicate(timeout=60)

    def connect(self, node, login=None):
        client = socket.create_connection(("127.0.0.1", node["port"]), timeout=30)
        self.addCleanup(client.close)
        stream = client.makefile("rwb", buffering=0)
        self.assertTrue(stream.readline()[:1] == b"2")
        if login:
            stream.write(b"AUTHINFO USER " + login.encode() + b"\r\n")
            self.assertTrue(stream.readline().startswith(b"381"))
            stream.write(b"AUTHINFO PASS " + login.encode() + b"-pw\r\n")
            reply = stream.readline()
            self.assertTrue(reply.startswith(b"281"), reply)
        return stream

    def post(self, node, login, payload):
        stream = self.connect(node, login)
        stream.write(b"POST\r\n")
        first = stream.readline()
        self.assertTrue(first.startswith(b"340"), first)
        stream.write(stuffed(payload) + b".\r\n")
        return stream.readline().decode().strip()

    def answer(self, node, message_id, login="alice"):
        stream = self.connect(node, login if node["name"] == "h" else None)
        stream.write(b"ARTICLE " + message_id.encode() + b"\r\n")
        line = stream.readline()
        if line.startswith(b"220"):
            while stream.readline() not in (b".\r\n", b""):
                pass
        return line.decode().strip()

    def fetch(self, node, message_id):
        stream = self.connect(node, "alice")
        stream.write(b"ARTICLE " + message_id.encode() + b"\r\n")
        status = stream.readline()
        self.assertTrue(status.startswith(b"220"), (message_id, status))
        lines = []
        while True:
            line = stream.readline()
            if line in (b".\r\n", b""):
                break
            lines.append(line[1:] if line.startswith(b".") else line)
        return b"".join(lines)

    def over_ids(self, node):
        stream = self.connect(node, "alice" if node["name"] == "h" else None)
        stream.write(b"GROUP fn.own.t\r\n")
        group = stream.readline()
        if not group.startswith(b"211"):
            return group.decode().strip(), []
        stream.write(b"OVER 1-\r\n")
        first = stream.readline()
        ids = []
        if first.startswith(b"224"):
            while True:
                line = stream.readline()
                if line in (b".\r\n", b""):
                    break
                fields = line.rstrip(b"\r\n").split(b"\t")
                if len(fields) > 4:
                    ids.append(fields[4].decode())
        return first.decode().strip(), ids

    def relay(self, octets, destination, message_id):
        head, _, body = octets.partition(b"\r\n\r\n")
        fields = head.split(b"\r\n")
        rest = [f for f in fields if not f.lower().startswith(b"path:")]
        old = [f for f in fields if f.lower().startswith(b"path:")]
        tail = old[0].split(b":", 1)[1].strip() if old else b"not-for-mail"
        relayed = (b"\r\n".join([b"Path: source.example.invalid!" + tail] + rest)
                   + b"\r\n\r\n" + body)
        stream = self.connect(destination)
        stream.write(b"IHAVE " + message_id.encode() + b"\r\n")
        first = stream.readline().decode().strip()
        if first.startswith("335"):
            stream.write(stuffed(relayed) + b".\r\n")
            first += " / " + stream.readline().decode().strip()
        return first

    def test_a_login_cancels_its_own_post_here_and_on_peers(self):
        h = self.initialize("h", True)
        a = self.initialize("a", False)
        b = self.initialize("b", False)
        for node in (h, a, b):
            self.start(node)
        seen = {}
        seen["post T"] = self.post(h, "alice", article(TARGET))
        target = self.fetch(h, TARGET)
        header = target.partition(b"\r\n\r\n")[0].split(b"\r\n")
        info = [i for i, f in enumerate(header) if f.startswith(b"Injection-Info: ")]
        locks = [i for i, f in enumerate(header) if f.startswith(b"Cancel-Lock: sha256:")]
        seen["T lock lines"] = [header[i].decode() for i in locks]

        bob_id, alice_id = "<own-cancel-bob@example.invalid>", "<own-cancel-alice@example.invalid>"
        seen["post bob cancel"] = self.post(h, "bob", cancel_of(bob_id, TARGET))
        seen["T after bob"] = self.answer(h, TARGET)
        seen["post alice cancel"] = self.post(h, "alice", cancel_of(alice_id, TARGET))
        seen["T after alice"] = self.answer(h, TARGET)
        seen["over after alice"] = self.over_ids(h)
        bob_cancel = self.fetch(h, bob_id)
        alice_cancel = self.fetch(h, alice_id)
        self.kill(h)
        self.start(h)
        seen["T after restart"] = self.answer(h, TARGET)

        seen["A relay T"] = self.relay(target, a, TARGET)
        seen["A relay bob"] = self.relay(bob_cancel, a, bob_id)
        seen["A T after T and bob"] = self.answer(a, TARGET)
        seen["A relay alice"] = self.relay(alice_cancel, a, alice_id)
        seen["A T after alice"] = self.answer(a, TARGET)
        seen["B relay alice"] = self.relay(alice_cancel, b, alice_id)
        seen["B relay bob"] = self.relay(bob_cancel, b, bob_id)
        seen["B relay T"] = self.relay(target, b, TARGET)
        seen["B T"] = self.answer(b, TARGET)
        seen["B over"] = self.over_ids(b)
        print("NATIVE-OWN-CANCEL-WITNESS " + json.dumps(seen, sort_keys=True))

        self.assertTrue(seen["post T"].startswith("240"), seen)
        self.assertEqual(len(locks), 1, seen)
        self.assertEqual(locks[0], info[0] + 1, seen)
        self.assertTrue(seen["post bob cancel"].startswith("240"), seen)
        self.assertTrue(seen["T after bob"].startswith("220"), seen)
        self.assertTrue(seen["post alice cancel"].startswith("240"), seen)
        self.assertTrue(seen["T after alice"].startswith("430"), seen)
        self.assertNotIn(TARGET, seen["over after alice"][1], seen)
        self.assertTrue(seen["T after restart"].startswith("430"), seen)
        self.assertIn(b"\r\nCancel-Key: sha256:", alice_cancel)
        self.assertIn(b"\r\nCancel-Key: sha256:", bob_cancel)
        self.assertTrue(seen["A T after T and bob"].startswith("220"), seen)
        self.assertTrue(seen["A T after alice"].startswith("430"), seen)
        self.assertTrue(seen["B T"].startswith("430"), seen)
        self.assertNotIn(TARGET, seen["B over"][1], seen)


if __name__ == "__main__":
    unittest.main()
