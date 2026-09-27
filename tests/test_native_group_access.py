"""SCN-152: per-login group access on a running node (PRF-222, NNT-046).

Two invitation-code accounts on one node with an implicit-TLS listener:
alice has no access rule and bob is given `account access bob --read
'fn.*,!fn.private.*' --post fn.public` live.  On a new connection bob cannot
list fn.private.x (LIST ACTIVE, LIST NEWSGROUPS, LIST COUNTS), select it
(GROUP and LISTGROUP answer 411 exactly as for an absent group), read its
article by Message-ID (430, the absent-article line) or post to it (441);
he reads and posts to fn.public, and a cross-posted article is held for him
with an Xref naming only fn.public.  alice lists, selects, reads and posts to
fn.private.x.  `account access show` prints the rule; after a restart it
still holds.  The scenario runs on the production image (FN_NATIVE_HOST)
and on the developer image (FN_NATIVE_DEVELOPER_HOST).

The decisions are ACL2's: books/nntp-auth.lisp fn-auth-delegate-pinned
serves a restricted session the view of books/group-access.lisp
(fn-gac-restrict-state, fn-gac-restrict-index, fn-gac-post-config); the rule
is the configuration's (books/config.lisp fn-cfg-account-access, delta code
22), projected by books/owner-agent.lisp fn-oag-listing.

Run: FN_NATIVE_HOST=<production launcher> FN_NATIVE_DEVELOPER_HOST=<developer
launcher> python3 -m unittest -v tests.test_native_group_access
"""

import os
from pathlib import Path
import re
import select
import signal
import socket
import ssl
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
PRODUCTION = os.environ.get("FN_NATIVE_HOST")
DEVELOPER = os.environ.get("FN_NATIVE_DEVELOPER_HOST")
IMAGES = [(name, Path(value)) for name, value in
          (("production", PRODUCTION), ("developer", DEVELOPER)) if value]
READY = bool(IMAGES) and all(p.is_file() and os.access(p, os.X_OK) for _, p in IMAGES)


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


class GroupAccessSourceTests(unittest.TestCase):
    def test_the_delta_code_is_22(self):
        config = (ROOT / "books" / "config.lisp").read_text(encoding="ascii")
        self.assertIn("((equal kind :account-access) 22)", config)
        self.assertIn("((equal code 22) :account-access)", config)

    def test_the_served_delegate_takes_the_view(self):
        for book, name in (("nntp-auth.lisp", "(defun fn-auth-delegate-pinned"),
                           ("served-carried.lisp", "(defun fn-scar-auth-delegate-pinned")):
            source = (ROOT / "books" / book).read_text(encoding="ascii")
            start = source.index(name)
            body = source[start:source.index("(defthm", start)]
            # The posting configuration is the access view over the
            # connection's moderation view (moderated-groups, PRF-228).
            flat = " ".join(body.split())
            for view in ("(fn-auth-view-session as config)",
                         "(fn-auth-view-archive as config archive)",
                         "(fn-auth-view-index as config archive index)",
                         "(fn-auth-view-config as (fn-auth-moderation-config as config) archive)"):
                self.assertIn(view, flat, book)


@unittest.skipUnless(READY, "set FN_NATIVE_HOST and/or FN_NATIVE_DEVELOPER_HOST")
class NativeGroupAccessTests(unittest.TestCase):
    def node(self, image):
        root = Path(tempfile.mkdtemp(prefix="fn-group-access-"))
        self.addCleanup(subprocess.run, ["rm", "-rf", str(root)], check=False)
        port, tls_port = free_port(), free_port()
        cert, key = root / "cert.pem", root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout",
                        str(key), "-out", str(cert), "-days", "2", "-nodes",
                        "-subj", "/CN=127.0.0.1"], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nprotected_only = true\n'.format(
                root / "store", port, tls_port, cert, key, root / "control.sock"),
            encoding="ascii")
        return {"image": image, "config": config, "tls_port": tls_port, "process": None}

    def operator(self, node, *words):
        result = subprocess.run(
            [str(node["image"]), "--fn", "operator", str(node["config"]), *words],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=240, check=False)
        print("NATIVE-ACCESS", " ".join(words[:3]), "->", result.returncode)
        return result

    def ok(self, node, *words):
        result = self.operator(node, *words)
        self.assertEqual(result.returncode, 0, text(result))
        return result

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

    def multi(self, stream, command):
        status = self.line(stream, command)
        rows = []
        if status[:1] == "2":
            while True:
                raw = stream.readline()
                row = raw.decode("ascii", "replace").rstrip("\r\n")
                if row == "." or raw == b"":
                    break
                rows.append(row)
        return status, rows

    def account(self, node, login):
        result = self.ok(node, "account", "invite", "--expires", "3600")
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, text(result))
        stream = self.tls(node)
        self.assertTrue(self.line(stream, "XREDEEM {} {}".format(
            codes[0].decode("ascii"), login)).startswith("381"))
        self.assertTrue(self.line(stream, "XREDEEM PASS pw-" + login).startswith("281"))

    def login(self, node, login):
        stream = self.tls(node)
        self.assertTrue(self.line(stream, "AUTHINFO USER " + login).startswith("381"))
        self.assertTrue(self.line(stream, "AUTHINFO PASS pw-" + login).startswith("281"))
        return stream

    def post(self, stream, groups, tag):
        status = self.line(stream, "POST")
        if not status.startswith("340"):
            return status
        stream.write(("From: {}@example.invalid\r\nNewsgroups: {}\r\nSubject: {}\r\n"
                      "Message-ID: <{}@example.invalid>\r\n\r\nbody\r\n.\r\n"
                      .format(tag, groups, tag, tag)).encode("ascii"))
        return stream.readline().decode("ascii", "replace").rstrip("\r\n")

    def listed(self, stream, command):
        status, rows = self.multi(stream, command)
        self.assertTrue(status.startswith("215"), status)
        return [row.split()[0] for row in rows if row.strip()]

    def scenario(self, image):
        node = self.node(image)
        self.ok(node, "init", "local.general")
        for group in ("fn.public", "fn.private.x"):
            self.ok(node, "group", "create", group)
        self.start(node)
        self.account(node, "alice")
        self.account(node, "bob")

        alice = self.login(node, "alice")
        for groups, tag in (("fn.private.x", "secret"), ("fn.public", "pub"),
                            ("fn.public,fn.private.x", "cross")):
            self.assertTrue(self.post(alice, groups, tag).startswith("240"), tag)

        # The rule, live; a refused pattern is refused by name.
        self.assertNotEqual(self.operator(node, "account", "access", "bob", "--read",
                                          "fn.[", "--post", "*").returncode, 0)
        self.ok(node, "account", "access", "bob", "--read", "fn.*,!fn.private.*",
                "--post", "fn.public")
        shown = text(self.ok(node, "account", "access", "show"))
        self.assertIn("access bob read fn.*,!fn.private.* post fn.public", shown)

        for phase in ("live", "restart"):
            bob = self.login(node, "bob")
            for command in ("LIST ACTIVE", "LIST NEWSGROUPS", "LIST COUNTS"):
                groups = self.listed(bob, command)
                self.assertNotIn("fn.private.x", groups, (phase, command))
                self.assertIn("fn.public", groups, (phase, command))
            absent = self.line(bob, "GROUP fn.absent")
            self.assertTrue(absent.startswith("411"), absent)
            self.assertEqual(self.line(bob, "GROUP fn.private.x"), absent)
            status, _ = self.multi(bob, "LISTGROUP fn.private.x")
            self.assertTrue(status.startswith("411"), status)
            nothere = self.line(bob, "STAT <nothere@example.invalid>")
            self.assertTrue(nothere.startswith("430"), nothere)
            self.assertEqual(self.line(bob, "STAT <secret@example.invalid>"), nothere)
            status, _ = self.multi(bob, "ARTICLE <secret@example.invalid>")
            self.assertTrue(status.startswith("430"), status)
            self.assertTrue(self.line(bob, "STAT <cross@example.invalid>").startswith("223"))
            self.assertTrue(self.line(bob, "GROUP fn.public").startswith("211"))
            status, rows = self.multi(bob, "OVER <cross@example.invalid>")
            self.assertTrue(status.startswith("224"), status)
            self.assertNotIn("fn.private.x", " ".join(rows))
            refused = self.post(bob, "fn.private.x", "bob-" + phase)
            self.assertTrue(refused.startswith("441"), refused)
            self.assertEqual(refused.replace("fn.private.x", "fn.absent"),
                             self.post(bob, "fn.absent", "bobabs-" + phase)
                             .replace("fn.absent", "fn.absent"))
            self.assertTrue(self.post(bob, "fn.public", "bobpub-" + phase).startswith("240"))

            alice = self.login(node, "alice")
            self.assertIn("fn.private.x", self.listed(alice, "LIST ACTIVE"))
            self.assertTrue(self.line(alice, "GROUP fn.private.x").startswith("211"))
            status, _ = self.multi(alice, "ARTICLE <secret@example.invalid>")
            self.assertTrue(status.startswith("220"), status)
            posted = self.post(alice, "fn.private.x", "alice-" + phase)
            self.assertTrue(posted.startswith("240"), posted)
            if phase == "live":
                self.stop(node)
                self.start(node)
        self.stop(node)

    def test_two_accounts_one_private_group(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.scenario(image)


if __name__ == "__main__":
    unittest.main()
