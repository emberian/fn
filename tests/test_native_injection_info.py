"""Opt-in native: Injection-Info names the login's account and the complaints address (PKT-597).

Two saved-image nodes on loopback.  H requires AUTHINFO (logins alice and
bob); A receives over IHAVE from a configured peer and takes local POST
without a login.  The decision is ACL2's: books/injection-info-params.lisp
fn-ipp-injected-octets (called by books/owner-served-invariants.lisp
fn-own-sub-stored-octets for every local submission the owner stages),
keystone fn-ipp-injected-octets-carry-the-parameters; the login is the one
the :submit effect carries (books/served.lisp fn-served-login).

- `policy set complaints-to abuse@example.org' on the running H (a live
  :set-policy row); a non-address is refused.
- alice's unsigned post on H is stored with exactly one Injection-Info:
  `H-AGENT; posting-account="HEX"; mail-complaints-to="abuse@example.org"',
  HEX 64 lowercase hex digits and no octet of the login; `account hash
  alice' prints HEX, `account hash bob' another value.
- bob's post carries bob's value; a post on A without a login carries no
  posting-account.
- An article relayed to A over IHAVE keeps the peer's Injection-Info line
  octet for octet (no rewriting on the transit arm).

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_injection_info
"""

import json
import os
from pathlib import Path
import re
import socket
import subprocess
import tempfile
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = (Path(IMAGE_TEXT) if IMAGE_TEXT else
         next((p for p in (ROOT / "build" / "fn-host-developer", ROOT / "build" / "fn-host")
               if p.is_file()), None))
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
GROUPS = ["fn.inj.t"]
HEX = re.compile(rb'posting-account="([0-9a-f]{64})"')


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def article(message_id, extra=None):
    lines = ["From: friend <friend@example.invalid>", "Newsgroups: fn.inj.t",
             "Subject: injection-info " + message_id,
             "Message-ID: " + message_id] + ([extra] if extra else [])
    return ("\r\n".join(lines) + "\r\n\r\nbody\r\n").encode("ascii")


def stuffed(octets):
    return b"".join((b"." + line if line.startswith(b".") else line)
                    for line in octets.splitlines(keepends=True))


def header_lines(octets, name):
    head = octets.partition(b"\r\n\r\n")[0]
    return [line for line in head.split(b"\r\n")
            if line.lower().startswith(name.lower() + b":")]


@unittest.skipUnless(READY, "set FN_NATIVE_HOST (a saved fn image)")
class NativeInjectionInfoTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-injection-info-")
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
        if expected is not None:
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
                result = subprocess.run(
                    [str(IMAGE), "--fn", "operator", str(config), "principal",
                     "set-password", login, "--posting"],
                    cwd=ROOT, env=self.env,
                    input=((login + "-correct-horse-battery\n") * 2).encode(),
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
            stream.write(b"AUTHINFO PASS " + login.encode() + b"-correct-horse-battery\r\n")
            reply = stream.readline()
            self.assertTrue(reply.startswith(b"281"), reply)
        return stream

    def post(self, node, login, payload):
        stream = self.connect(node, login)
        stream.write(b"POST\r\n")
        first = stream.readline()
        if not first.startswith(b"340"):
            return first.decode().strip()
        stream.write(stuffed(payload) + b".\r\n")
        return stream.readline().decode().strip()

    def fetch(self, node, message_id, login=None):
        stream = self.connect(node, login)
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

    def relay(self, octets, destination, message_id):
        stream = self.connect(destination)
        stream.write(b"IHAVE " + message_id.encode() + b"\r\n")
        first = stream.readline().decode().strip()
        if first.startswith("335"):
            stream.write(stuffed(octets) + b".\r\n")
            first += " / " + stream.readline().decode().strip()
        return first

    def operator(self, node, *words, expected=0):
        return self.command([IMAGE, "--fn", "operator", node["config"], *words],
                            expected=expected)

    def test_injection_info_names_the_account_and_the_complaints_address(self):
        try:
            self.scenario()
        except BaseException:
            for log in sorted(self.base.glob("*/node-*.log")):
                print("== {}\n{}".format(log, log.read_bytes()[-3000:].decode(
                    "utf-8", "replace")))
            raise

    def scenario(self):
        h = self.initialize("h", True)
        a = self.initialize("a", False)
        for node in (h, a):
            self.start(node)
        seen = {}
        refused = self.operator(h, "policy", "set", "complaints-to", "not-an-address",
                                expected=None)
        seen["complaints refused"] = refused.returncode
        self.operator(h, "policy", "set", "complaints-to", "abuse@example.org")

        seen["post alice"] = self.post(h, "alice", article("<inj-alice@example.invalid>"))
        alice = self.fetch(h, "<inj-alice@example.invalid>", "alice")
        info = header_lines(alice, b"Injection-Info")
        seen["alice info"] = [line.decode() for line in info]
        seen["post bob"] = self.post(h, "bob", article("<inj-bob@example.invalid>"))
        bob = self.fetch(h, "<inj-bob@example.invalid>", "bob")
        bob_info = header_lines(bob, b"Injection-Info")
        seen["bob info"] = [line.decode() for line in bob_info]
        hash_alice = self.operator(h, "account", "hash", "alice").stdout.decode().strip()
        hash_bob = self.operator(h, "account", "hash", "bob").stdout.decode().strip()
        seen["account hash alice"] = hash_alice
        seen["account hash bob"] = hash_bob

        seen["post anonymous"] = self.post(a, None, article("<inj-anon@example.invalid>"))
        anon_info = []
        if seen["post anonymous"].startswith("240"):
            anon = self.fetch(a, "<inj-anon@example.invalid>")
            anon_info = header_lines(anon, b"Injection-Info")
        seen["anonymous info"] = [line.decode() for line in anon_info]

        peer_line = (b'Injection-Info: peer.example.invalid; posting-account="0123abcd";'
                     b' mail-complaints-to="usenet@peer.example.invalid"')
        relayed = (b"Path: source.example.invalid!peer.example.invalid!not-for-mail\r\n"
                   b"Date: Sat, 26 Sep 2026 12:00:00 +0000\r\n"
                   b"Injection-Date: Sat, 26 Sep 2026 12:00:00 +0000\r\n"
                   + article("<inj-peer@example.invalid>", peer_line.decode()))
        seen["relay"] = self.relay(relayed, a, "<inj-peer@example.invalid>")
        self.assertTrue(seen["relay"].startswith("335") and " / 235" in seen["relay"], seen)
        peer_stored = self.fetch(a, "<inj-peer@example.invalid>")
        seen["relayed info"] = [line.decode() for line in
                                header_lines(peer_stored, b"Injection-Info")]
        print("NATIVE-INJECTION-INFO-WITNESS " + json.dumps(seen, sort_keys=True))

        self.assertNotEqual(seen["complaints refused"], 0, seen)
        self.assertTrue(seen["post alice"].startswith("240"), seen)
        self.assertEqual(len(info), 1, seen)
        match = HEX.search(info[0])
        self.assertIsNotNone(match, seen)
        self.assertTrue(info[0].endswith(b'; mail-complaints-to="abuse@example.org"'), seen)
        self.assertNotIn(b"alice", info[0], seen)
        self.assertEqual(hash_alice, match.group(1).decode(), seen)
        self.assertEqual(len(bob_info), 1, seen)
        self.assertEqual(hash_bob, HEX.search(bob_info[0]).group(1).decode(), seen)
        self.assertNotEqual(hash_alice, hash_bob, seen)
        self.assertTrue(seen["post anonymous"].startswith("240"), seen)
        self.assertEqual(len(anon_info), 1, seen)
        self.assertNotIn(b"posting-account", anon_info[0], seen)
        self.assertEqual(seen["relayed info"], [peer_line.decode()], seen)


if __name__ == "__main__":
    unittest.main()
