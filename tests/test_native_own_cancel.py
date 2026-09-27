"""Opt-in native: a friend cancels their own unsigned post by RFC 8315 (SEC-006, PRF-210).

Three saved-image nodes on loopback.  H requires AUTHINFO (logins alice and
bob); A and B receive over IHAVE from a configured peer.  Nothing is signed.
The poster's client supplies the RFC 8315 lines, as tin does with its own
secret: alice's post carries `Cancel-Lock: sha256:Base64(SHA-256(K))`, her
cancel `Cancel-Key: sha256:K`; bob's cancel carries a key of his own.  The
decision is ACL2's (books/control-authority.lisp fn-ctl-withdrawal-plan and
the :poster arm of fn-ctl-withdrawal-effect; keystone
fn-ctl-withdrawal-authority-is-exactly-signer-or-poster).

- bob's cancel (240, filed): T is still served (220): his key opens nothing.
- alice's cancel (240): ARTICLE T answers 430 and OVER no longer lists it;
  after a SIGKILL and restart the answer is unchanged.
- T and both cancels, as H stored them, relayed to A (target first) and B
  (cancels first): both end at 430 for T; A still serves T after T and bob's
  cancel alone.

The node-written lines (Thunderbird's case: a client that writes no
Cancel-Lock): alice posts T2 with none; the stored T2 opens with exactly one
`Cancel-Lock: sha256:...' the node wrote for her account, IN FRONT of the
injected block (books/cancel-lock.lisp fn-cl-served-payload, outside the D25
source); bob's key-less cancel is filed and T2 stays; alice's key-less
cancel gets the node's `Cancel-Key' for her account and T2 answers 430, is
gone from OVER, stays gone after a restart, and a peer receiving T2 and her
cancel decides the same.

D25 across accounts and key epochs (gpt-6's wave-5 review section 3): bob
POSTs alice's source again under its Message-ID and is told it is already
stored, the held lock unchanged; bob's cancel withdraws nothing; the source
with a changed user-supplied Cancel-Lock is a conflict; after `store ROOT
node-secret rotate' alice's retry is still already stored, and her cancel
after the rotation and a restart withdraws her pre-rotation post (the
cancel carries one key per kept epoch).

The key files: init writes STORE/keys/node-secret.key (a `fn-node-secret v1'
file, 0600, directory 0700); `node-secret create' refuses by name while one
exists; a start refuses by name when the file is readable by others or
missing (and does not recreate it) or a kept epoch is missing.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_own_cancel
"""

import base64
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import unittest

from tests.native_process import wait_for_announcement
from tools.wire_stream import whole_stream

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


def cancel_of(message_id, target, key):
    lines = ["From: friend <friend@example.invalid>", "Newsgroups: fn.own.t",
             "Subject: cmsg cancel " + target, "Message-ID: " + message_id,
             "Control: cancel " + target, "Cancel-Key: sha256:" + key]
    return ("\r\n".join(lines) + "\r\n\r\ncancel\r\n").encode("ascii")


def key_of(secret):
    """A client's c-key-string: Base64 of 32 octets (RFC 8315 section 4)."""
    return base64.b64encode(hashlib.sha256(secret).digest()).decode("ascii")


def lock_of(key):
    """RFC 8315 section 2.1: Base64(SHA-256(the key's octets))."""
    return base64.b64encode(hashlib.sha256(key.encode("ascii")).digest()).decode("ascii")


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
                # The native operator reads the password on stdin.
                result = subprocess.run(
                    [str(IMAGE), "--fn", "operator", str(config), "principal",
                     "set-password", login, "--posting"],
                    cwd=ROOT, env=self.env, input=((login + "-correct-horse-battery\n") * 2).encode(),
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600,
                    check=False)
                self.assertEqual(result.returncode, 0, result)
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
        stream = whole_stream(client)
        self.assertTrue(stream.readline()[:1] == b"2")
        if login:
            stream.write(b"AUTHINFO USER " + login.encode() + b"\r\n")
            self.assertTrue(stream.readline().startswith(b"381"))
            stream.write(b"AUTHINFO PASS " + login.encode() + b"-correct-horse-battery\r\n")
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

    def run_refused(self, node):
        result = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=300, check=False)
        return result.returncode, (result.stdout + result.stderr).decode("utf-8", "replace")

    def node_secret(self, node, *words, expected=0):
        result = self.command([IMAGE, "--fn", "store", node["store"], "node-secret", *words],
                              expected=expected)
        return (result.stdout + result.stderr).decode("utf-8", "replace").strip()

    def test_node_secret_is_written_at_init_and_refused_by_name(self):
        node = self.initialize("s", False)
        key = node["store"] / "keys" / "node-secret.key"
        original = key.read_bytes()
        seen = {"size": len(original), "magic": original[:18].decode("ascii", "replace"),
                "mode": oct(key.stat().st_mode & 0o777),
                "dir mode": oct(key.parent.stat().st_mode & 0o777)}
        seen["create over existing"] = self.run_create_refused(node)
        seen["unchanged"] = key.read_bytes() == original
        key.chmod(0o644)
        seen["world-readable"] = self.run_refused(node)
        key.chmod(0o600)
        key.rename(node["root"] / "node-secret.aside")
        seen["missing"] = self.run_refused(node)
        seen["not recreated"] = not key.exists()
        seen["create"] = self.node_secret(node, "create")
        seen["new differs"] = key.read_bytes() != original
        self.start(node)
        print("NATIVE-NODE-SECRET-WITNESS " + json.dumps(seen, sort_keys=True))
        # magic 18, epoch 4, identity length 2, "local" 5, root 32
        self.assertEqual(seen["size"], 61, seen)
        self.assertEqual(seen["magic"], "fn-node-secret v1\n", seen)
        self.assertEqual(seen["mode"], "0o600", seen)
        self.assertEqual(seen["dir mode"], "0o700", seen)
        self.assertNotEqual(seen["create over existing"][0], 0, seen)
        self.assertIn("exists; refusing to replace it", seen["create over existing"][1], seen)
        self.assertTrue(seen["unchanged"], seen)
        self.assertNotEqual(seen["world-readable"][0], 0, seen)
        self.assertIn("readable or writable by group or others", seen["world-readable"][1], seen)
        self.assertNotEqual(seen["missing"][0], 0, seen)
        self.assertIn("node-secret.key is missing", seen["missing"][1], seen)
        self.assertTrue(seen["not recreated"], seen)
        self.assertEqual(seen["create"], "node-secret created epoch 1", seen)
        self.assertTrue(seen["new differs"], seen)

    def run_create_refused(self, node):
        result = subprocess.run(
            [str(IMAGE), "--fn", "store", str(node["store"]), "node-secret", "create"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=300, check=False)
        return result.returncode, (result.stdout + result.stderr).decode("utf-8", "replace")

    def test_a_same_source_retry_is_already_stored_across_accounts_and_epochs(self):
        try:
            self.retry_scenario()
        except BaseException:
            for log in sorted(self.base.glob("*/node-*.log")):
                print("== {}\n{}".format(log, log.read_bytes()[-3000:].decode(
                    "utf-8", "replace")))
            raise

    def retry_scenario(self):
        h = self.initialize("h", True)
        self.start(h)
        target = "<own-target-3@example.invalid>"
        source = article(target)
        seen = {}
        lock_lines = lambda octets: [f.decode() for f in
                                     octets.partition(b"\r\n\r\n")[0].split(b"\r\n")
                                     if f.lower().startswith(b"cancel-lock:")]
        seen["alice post"] = self.post(h, "alice", source)
        held = self.fetch(h, target)
        seen["held locks"] = lock_lines(held)
        seen["bob retry"] = self.post(h, "bob", source)
        seen["held unchanged after bob"] = self.fetch(h, target) == held
        seen["changed user lock"] = self.post(h, "bob", article(
            target, "Cancel-Lock: sha256:" + lock_of(key_of(b"bob client secret"))))
        bob_id = "<own-cancel-bob-3@example.invalid>"
        plain = lambda mid: (("\r\n".join([
            "From: friend <friend@example.invalid>", "Newsgroups: fn.own.t",
            "Subject: cmsg cancel " + target, "Message-ID: " + mid,
            "Control: cancel " + target]) + "\r\n\r\ncancel\r\n").encode("ascii"))
        seen["bob cancel"] = self.post(h, "bob", plain(bob_id))
        seen["T3 after bob cancel"] = self.answer(h, target)
        self.kill(h)
        seen["rotate"] = self.node_secret(h, "rotate")
        seen["kept epoch 1"] = (h["store"] / "keys" / "node-secret-1.key").is_file()
        self.start(h)
        seen["alice retry after rotation"] = self.post(h, "alice", source)
        seen["held unchanged after rotation"] = self.fetch(h, target) == held
        self.kill(h)
        self.start(h)
        alice_id = "<own-cancel-alice-3@example.invalid>"
        seen["alice cancel"] = self.post(h, "alice", plain(alice_id))
        seen["T3 after alice cancel"] = self.answer(h, target)
        alice_cancel = self.fetch(h, alice_id)
        seen["alice cancel keys"] = [f.decode() for f in
                                     alice_cancel.partition(b"\r\n\r\n")[0].split(b"\r\n")
                                     if f.lower().startswith(b"cancel-key:")]
        self.kill(h)
        kept = h["store"] / "keys" / "node-secret-1.key"
        kept.rename(h["root"] / "kept.aside")
        seen["kept epoch missing"] = self.run_refused(h)
        (h["root"] / "kept.aside").rename(kept)
        print("NATIVE-OWN-CANCEL-RETRY-WITNESS " + json.dumps(seen, sort_keys=True))

        self.assertTrue(seen["alice post"].startswith("240"), seen)
        self.assertEqual(len(seen["held locks"]), 1, seen)
        self.assertIn("already stored here", seen["bob retry"], seen)
        self.assertTrue(seen["held unchanged after bob"], seen)
        self.assertIn("a different article with this Message-ID", seen["changed user lock"], seen)
        self.assertTrue(seen["bob cancel"].startswith("240"), seen)
        self.assertTrue(seen["T3 after bob cancel"].startswith("220"), seen)
        self.assertEqual(seen["rotate"], "node-secret rotated epoch 2", seen)
        self.assertTrue(seen["kept epoch 1"], seen)
        self.assertIn("already stored here", seen["alice retry after rotation"], seen)
        self.assertTrue(seen["held unchanged after rotation"], seen)
        self.assertTrue(seen["alice cancel"].startswith("240"), seen)
        self.assertTrue(seen["T3 after alice cancel"].startswith("430"), seen)
        # One key per kept epoch, current first; the epoch-1 key opens T3's lock.
        self.assertEqual(len(seen["alice cancel keys"]), 1, seen)
        entries = [w.split("sha256:", 1)[1] for w in seen["alice cancel keys"][0].split()
                   if w.startswith("sha256:")]
        self.assertEqual(len(entries), 2, seen)
        self.assertIn(seen["held locks"][0], ["Cancel-Lock: sha256:" + lock_of(k) for k in entries],
                      seen)
        self.assertNotEqual(seen["kept epoch missing"][0], 0, seen)
        self.assertIn("retained epoch 1 missing", seen["kept epoch missing"][1], seen)

    def test_the_node_writes_the_lock_and_key_for_a_login(self):
        try:
            self.node_written_scenario()
        except BaseException:
            for log in sorted(self.base.glob("*/node-*.log")):
                print("== {}\n{}".format(log, log.read_bytes()[-3000:].decode(
                    "utf-8", "replace")))
            raise

    def node_written_scenario(self):
        h = self.initialize("h", True)
        a = self.initialize("a", False)
        for node in (h, a):
            self.start(node)
        target = "<own-target-2@example.invalid>"
        seen = {}
        # Thunderbird's form: no Cancel-Lock, no Cancel-Key.
        seen["post T2"] = self.post(h, "alice", article(target))
        stored = self.fetch(h, target)
        header = stored.partition(b"\r\n\r\n")[0].split(b"\r\n")
        # ARTICLE puts the serving node's own Xref first (reader-compat,
        # PRF-243; RFC 5536 section 3.2.14); the stored article follows it.
        if header and header[0].startswith(b"Xref: "):
            header = header[1:]
        locks = [i for i, f in enumerate(header) if f.lower().startswith(b"cancel-lock:")]
        seen["T2 locks"] = [header[i].decode() for i in locks]
        # In front of the injected block: the stored article's first line.
        seen["lock is the first line"] = locks == [0]
        bob_id = "<own-cancel-bob-2@example.invalid>"
        alice_id = "<own-cancel-alice-2@example.invalid>"
        plain = lambda mid: (("\r\n".join([
            "From: friend <friend@example.invalid>", "Newsgroups: fn.own.t",
            "Subject: cmsg cancel " + target, "Message-ID: " + mid,
            "Control: cancel " + target]) + "\r\n\r\ncancel\r\n").encode("ascii"))
        seen["post bob cancel"] = self.post(h, "bob", plain(bob_id))
        seen["T2 after bob"] = self.answer(h, target)
        seen["post alice cancel"] = self.post(h, "alice", plain(alice_id))
        seen["T2 after alice"] = self.answer(h, target)
        seen["over after alice"] = self.over_ids(h)
        bob_cancel = self.fetch(h, bob_id)
        alice_cancel = self.fetch(h, alice_id)
        keys = lambda octets: [f.decode() for f in
                               octets.partition(b"\r\n\r\n")[0].split(b"\r\n")
                               if f.lower().startswith(b"cancel-key:")]
        seen["alice cancel keys"] = keys(alice_cancel)
        seen["bob cancel keys"] = keys(bob_cancel)
        self.kill(h)
        self.start(h)
        seen["T2 after restart"] = self.answer(h, target)
        seen["A relay T2"] = self.relay(stored, a, target)
        seen["A relay bob"] = self.relay(bob_cancel, a, bob_id)
        seen["A T2 after bob"] = self.answer(a, target)
        seen["A relay alice"] = self.relay(alice_cancel, a, alice_id)
        seen["A T2 after alice"] = self.answer(a, target)
        print("NATIVE-OWN-CANCEL-NODE-WRITTEN-WITNESS " + json.dumps(seen, sort_keys=True))

        self.assertTrue(seen["post T2"].startswith("240"), seen)
        self.assertEqual(len(seen["T2 locks"]), 1, seen)
        self.assertRegex(seen["T2 locks"][0], r"^Cancel-Lock: sha256:[A-Za-z0-9+/]{43}=$")
        self.assertTrue(seen["lock is the first line"], seen)
        self.assertTrue(seen["post bob cancel"].startswith("240"), seen)
        self.assertTrue(seen["T2 after bob"].startswith("220"), seen)
        self.assertEqual(len(seen["bob cancel keys"]), 1, seen)
        self.assertEqual(len(seen["alice cancel keys"]), 1, seen)
        self.assertNotEqual(seen["bob cancel keys"], seen["alice cancel keys"], seen)
        # The key alice's cancel carries opens T2's lock (RFC 8315 2.1).
        key = seen["alice cancel keys"][0].split("sha256:", 1)[1]
        self.assertEqual(seen["T2 locks"][0], "Cancel-Lock: sha256:" + lock_of(key), seen)
        self.assertTrue(seen["post alice cancel"].startswith("240"), seen)
        self.assertTrue(seen["T2 after alice"].startswith("430"), seen)
        self.assertNotIn(target, seen["over after alice"][1], seen)
        self.assertTrue(seen["T2 after restart"].startswith("430"), seen)
        self.assertTrue(seen["A T2 after bob"].startswith("220"), seen)
        self.assertTrue(seen["A T2 after alice"].startswith("430"), seen)

    def test_a_login_cancels_its_own_post_here_and_on_peers(self):
        try:
            self.scenario()
        except BaseException:
            # The nodes' own logs name a host fault; the temporary tree goes.
            for log in sorted(self.base.glob("*/node-*.log")):
                print("== {}\n{}".format(log, log.read_bytes()[-3000:].decode(
                    "utf-8", "replace")))
            raise

    def scenario(self):
        h = self.initialize("h", True)
        a = self.initialize("a", False)
        b = self.initialize("b", False)
        for node in (h, a, b):
            self.start(node)
        seen = {}
        alice_key, bob_key = key_of(b"alice client secret"), key_of(b"bob client secret")
        seen["post T"] = self.post(h, "alice", article(
            TARGET, "Cancel-Lock: sha256:" + lock_of(alice_key)))
        target = self.fetch(h, TARGET)
        header = target.partition(b"\r\n\r\n")[0].split(b"\r\n")
        info = [i for i, f in enumerate(header) if f.startswith(b"Injection-Info: ")]
        locks = [i for i, f in enumerate(header) if f.startswith(b"Cancel-Lock: sha256:")]
        seen["T lock lines"] = [header[i].decode() for i in locks]

        bob_id, alice_id = "<own-cancel-bob@example.invalid>", "<own-cancel-alice@example.invalid>"
        seen["post bob cancel"] = self.post(h, "bob", cancel_of(bob_id, TARGET, bob_key))
        seen["T after bob"] = self.answer(h, TARGET)
        seen["post alice cancel"] = self.post(h, "alice", cancel_of(alice_id, TARGET, alice_key))
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
        self.assertEqual(seen["T lock lines"],
                         ["Cancel-Lock: sha256:" + lock_of(alice_key)], seen)
        self.assertTrue(info, seen)
        self.assertTrue(seen["post bob cancel"].startswith("240"), seen)
        self.assertTrue(seen["T after bob"].startswith("220"), seen)
        self.assertTrue(seen["post alice cancel"].startswith("240"), seen)
        self.assertTrue(seen["T after alice"].startswith("430"), seen)
        self.assertNotIn(TARGET, seen["over after alice"][1], seen)
        self.assertTrue(seen["T after restart"].startswith("430"), seen)
        self.assertIn(("Cancel-Key: sha256:" + alice_key).encode(), alice_cancel)
        self.assertIn(("Cancel-Key: sha256:" + bob_key).encode(), bob_cancel)
        self.assertTrue(seen["A T after T and bob"].startswith("220"), seen)
        self.assertTrue(seen["A T after alice"].startswith("430"), seen)
        self.assertTrue(seen["B T"].startswith("430"), seen)
        self.assertNotIn(TARGET, seen["B over"][1], seen)


if __name__ == "__main__":
    unittest.main()
