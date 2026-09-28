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
import re
import unittest

from tests.native_harness import EXIT_OK, ROOT, Client, Node, free_port, native_image

IMAGE = native_image("FN_NATIVE_HOST", "build/fn-host-developer")
if not os.environ.get("FN_NATIVE_HOST") and not IMAGE.is_file():
    IMAGE = ROOT / "build" / "fn-host"
READY = bool(IMAGE.is_file() and os.access(IMAGE, os.X_OK))
GROUPS = ["fn.inj.t"]
HEX = re.compile(rb'posting-account="([0-9a-f]{64})"')


def article(message_id, extra=None):
    lines = ["From: friend <friend@example.invalid>", "Newsgroups: fn.inj.t",
             "Subject: injection-info " + message_id,
             "Message-ID: " + message_id] + ([extra] if extra else [])
    return ("\r\n".join(lines) + "\r\n\r\nbody\r\n").encode("ascii")


def header_lines(octets, name):
    head = octets.partition(b"\r\n\r\n")[0]
    return [line for line in head.split(b"\r\n")
            if line.lower().startswith(name.lower() + b":")]


@unittest.skipUnless(READY, "set FN_NATIVE_HOST (a saved fn image)")
class NativeInjectionInfoTests(unittest.TestCase):
    def setUp(self):
        self.nodes = []

    def initialize(self, name, auth):
        node = Node(self, IMAGE, name=name)
        self.nodes.append(node)
        node.store("init", *GROUPS, expect=EXIT_OK)
        if auth:
            node.write_config(extra='[auth]\nrequired = true\nprotected_only = false\n'
                                    'path = "{}"\n'.format(node.root / "credentials.toml"))
            for login in ("alice", "bob"):
                node.operator("principal", "set-password", login, "--posting",
                              input=((login + "-correct-horse-battery\n") * 2).encode(),
                              timeout=600, expect=EXIT_OK)
        else:
            node.operator("peer", "add", "source", "source.example.invalid", "127.0.0.1",
                          str(free_port()), "fn.*", "-", "127.0.0.1", "true", expect=EXIT_OK)
        return node

    def connect(self, node, login=None):
        client = Client(node.port, timeout=30)
        self.addCleanup(client.close)
        self.assertTrue(client.greeting[:1] == b"2")
        if login:
            self.assertTrue(client.command("AUTHINFO USER " + login).startswith(b"381"))
            reply = client.command("AUTHINFO PASS " + login + "-correct-horse-battery")
            self.assertTrue(reply.startswith(b"281"), reply)
        return client

    def post(self, node, login, payload):
        first, final = self.connect(node, login).post(payload)
        return (final if final is not None else first).decode().strip()

    def fetch(self, node, message_id, login=None):
        status, body = self.connect(node, login).multiline("ARTICLE " + message_id)
        self.assertTrue(status.startswith(b"220"), (message_id, status))
        return body

    def relay(self, octets, destination, message_id):
        first, final = self.connect(destination).post(octets, verb="IHAVE " + message_id)
        text = first.decode().strip()
        if final is not None:
            text += " / " + final.decode().strip()
        return text

    def operator(self, node, *words, expected=0):
        return node.operator(*words, expect=expected)

    def test_injection_info_names_the_account_and_the_complaints_address(self):
        try:
            self.scenario()
        except BaseException:
            for node in self.nodes:
                for process in node.processes:
                    print("== {} {}\n{}".format(node.name, process.pid, process.stderr.since(0)[
                        -3000:].decode("utf-8", "replace")))
            raise

    def scenario(self):
        h = self.initialize("h", True)
        a = self.initialize("a", False)
        for node in (h, a):
            node.start()
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
