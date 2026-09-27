"""SCN-155: a moderated group on a running node (PRF-228, NNT-047; RFC 5537
sections 3.5 item 7, 3.5.1 and 7; RFC 6048 section 2.1.1).

One node with an implicit-TLS listener and two invitation-code accounts,
alice and carol.  `group moderate fn.mod --moderators alice` (offline; the
queue defaults to fn.mod.moderation) makes fn.mod moderated: LIST ACTIVE
lists it `m` on every connection.  carol posts to fn.mod without Approved:
240, and the article is NOT in fn.mod (STAT of its Message-ID 430, GROUP
fn.mod still empty); it is in the queue fn.mod.moderation as an envelope
(Content-Type application/news-transmission; usage=moderate) whose Message-ID
is <fn-moderate.ID> and whose body is the proto-article with the Date the
node added.  carol's own Approved is refused by name (441).  alice, the
moderator, posts the envelope's body with an Approved field from her login:
240, and the article is in fn.mod under its original Message-ID.  After a
restart fn.mod is still `m`; `group moderate fn.mod --off` live makes it
`y` on a new connection, and carol's post then lands in fn.mod.  The scenario
runs on the production image (FN_NATIVE_HOST) and the developer image
(FN_NATIVE_DEVELOPER_HOST).

The decisions are ACL2's: books/nntp-post.lisp fn-post-gated-decision
(books/moderation.lisp fn-mod-gate), books/nntp-auth.lisp
fn-auth-moderation-config (the login's approver view), the configuration's
moderation (books/config.lisp code 23) projected by books/owner-agent.lisp
fn-oag-post-config.

Run: FN_NATIVE_HOST=<production launcher> FN_NATIVE_DEVELOPER_HOST=<developer
launcher> python3 -m unittest -v tests.test_native_moderation
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

FORGED = ("441 posting failed; Approved is accepted only from a moderator of "
          "each moderated group named (LIST ACTIVE status m)")


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


class ModerationSourceTests(unittest.TestCase):
    def test_the_delta_code_is_23(self):
        config = (ROOT / "books" / "config.lisp").read_text(encoding="ascii")
        self.assertIn("((equal kind :set-group-moderation) 23)", config)
        self.assertIn("((equal code 23) :set-group-moderation)", config)

    def test_the_post_step_runs_the_gate_after_the_read_only_gate(self):
        post = (ROOT / "books" / "nntp-post.lisp").read_text(encoding="ascii")
        start = post.index("(defun fn-post-gated-decision")
        gated = post[start:post.index("(defthm", start)]
        self.assertLess(gated.index("(fn-gst-post-gate"), gated.index("(fn-mod-gate"))

    def test_the_served_delegate_takes_the_approver_view(self):
        auth = (ROOT / "books" / "nntp-auth.lisp").read_text(encoding="ascii")
        for name in ("(defun fn-auth-delegate ", "(defun fn-auth-delegate-pinned"):
            start = auth.index(name)
            body = auth[start:auth.index("(defun", start + 10)]
            self.assertIn("(fn-auth-moderation-config as config)", body, name)


@unittest.skipUnless(READY, "set FN_NATIVE_HOST and/or FN_NATIVE_DEVELOPER_HOST")
class NativeModerationTests(unittest.TestCase):
    def node(self, image):
        root = Path(tempfile.mkdtemp(prefix="fn-moderation-"))
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
        print("NATIVE-MODERATION", " ".join(words[:4]), "->", result.returncode,
              text(result)[:160].replace("\n", " | "))
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
                rows.append(row[1:] if row.startswith("..") else row)
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

    def post_lines(self, stream, lines):
        status = self.line(stream, "POST")
        if not status.startswith("340"):
            return status
        body = "".join(("." + row if row.startswith(".") else row) + "\r\n"
                       for row in lines)
        stream.write((body + ".\r\n").encode("ascii"))
        return stream.readline().decode("ascii", "replace").rstrip("\r\n")

    def article(self, groups, tag, extra=()):
        return (["From: {}@example.invalid".format(tag), "Newsgroups: " + groups,
                 "Subject: " + tag, "Message-ID: <{}@example.invalid>".format(tag)]
                + list(extra) + ["", "body of " + tag])

    def active(self, stream):
        status, rows = self.multi(stream, "LIST ACTIVE")
        self.assertTrue(status.startswith("215"), status)
        return {row.split()[0]: row.split()[3] for row in rows if row.strip()}

    def count(self, stream, group):
        status = self.line(stream, "GROUP " + group)
        self.assertTrue(status.startswith("211"), status)
        return int(status.split()[1])

    def scenario(self, image):
        node = self.node(image)
        self.ok(node, "init", "fn.test")
        for group in ("fn.mod", "fn.mod.moderation"):
            self.ok(node, "group", "create", group)
        # Offline, refused by name: an absent group, an absent queue.
        self.assertNotEqual(self.operator(node, "group", "moderate", "fn.absent",
                                          "--moderators", "alice").returncode, 0)
        self.assertNotEqual(self.operator(node, "group", "moderate", "fn.test",
                                          "--moderators", "alice", "--queue",
                                          "fn.absent").returncode, 0)
        self.ok(node, "group", "moderate", "fn.mod", "--moderators", "alice")
        self.start(node)
        self.account(node, "alice")
        self.account(node, "carol")
        listed = text(self.ok(node, "account", "list"))
        self.assertIn("moderator alice fn.mod", listed)
        self.assertIn("moderation fn.mod fn.mod.moderation", listed)

        carol = self.login(node, "carol")
        self.assertEqual(self.active(carol),
                         {"fn.mod": "m", "fn.mod.moderation": "y", "fn.test": "y"})
        # Held: 240, not in fn.mod, in the queue as the envelope.
        held = self.post_lines(carol, self.article("fn.mod", "held1"))
        self.assertTrue(held.startswith("240"), held)
        self.assertTrue(self.line(carol, "STAT <held1@example.invalid>").startswith("430"))
        self.assertEqual(self.count(carol, "fn.mod"), 0)
        # Forged: carol's Approved is refused by name, nothing stored.
        forged = self.post_lines(carol, self.article(
            "fn.mod", "forged1", ["Approved: carol@example.invalid"]))
        self.assertEqual(forged, FORGED)
        self.assertTrue(self.line(carol, "STAT <forged1@example.invalid>").startswith("430"))

        alice = self.login(node, "alice")
        self.assertEqual(self.active(alice)["fn.mod"], "m")
        self.assertEqual(self.count(alice, "fn.mod.moderation"), 1)
        status, envelope = self.multi(alice, "ARTICLE <fn-moderate.held1@example.invalid>")
        self.assertTrue(status.startswith("220"), status)
        self.assertIn("Content-Type: application/news-transmission; usage=moderate",
                      envelope)
        self.assertIn("Newsgroups: fn.mod.moderation", envelope)
        proto = envelope[envelope.index("") + 1:]
        self.assertIn("Message-ID: <held1@example.invalid>", proto)
        self.assertTrue(any(row.startswith("Date: ") for row in proto), proto)
        # The moderator approves by posting the proto-article with Approved.
        approved = self.post_lines(alice, ["Approved: alice@example.invalid"] + proto)
        self.assertTrue(approved.startswith("240"), approved)
        reader = self.login(node, "carol")
        self.assertEqual(self.count(reader, "fn.mod"), 1)
        self.assertTrue(self.line(reader, "STAT <held1@example.invalid>").startswith("223"))

        # After a restart the moderation holds.
        self.stop(node)
        self.start(node)
        carol = self.login(node, "carol")
        self.assertEqual(self.active(carol)["fn.mod"], "m")
        held2 = self.post_lines(carol, self.article("fn.test,fn.mod", "held2"))
        self.assertTrue(held2.startswith("240"), held2)
        self.assertTrue(self.line(carol, "STAT <held2@example.invalid>").startswith("430"))

        # Live: end the moderation; a new connection lists "y" and posts.
        self.ok(node, "group", "moderate", "fn.mod", "--off")
        carol = self.login(node, "carol")
        self.assertEqual(self.active(carol)["fn.mod"], "y")
        direct = self.post_lines(carol, self.article("fn.mod", "direct1"))
        self.assertTrue(direct.startswith("240"), direct)
        self.assertTrue(self.line(carol, "STAT <direct1@example.invalid>").startswith("223"))
        self.stop(node)

    def test_moderated_group_holds_approves_and_refuses(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.scenario(image)


if __name__ == "__main__":
    unittest.main()
