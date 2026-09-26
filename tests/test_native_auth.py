"""AUTHINFO through the installed native operator/owner, with no Python server."""
import os
from pathlib import Path
import select
import socket
import subprocess
import sys
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


def free_loopback_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


class NativeAuthTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(
                "native host image missing: {} (tools/build_native_host.sh)".format(IMAGE))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-auth-")
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.store = root / "store"
        self.auth = root / "credentials.toml"
        self.config = root / "fn.toml"
        self.port = free_loopback_port()
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.config.write_text(
            '[store]\npath = "{}"\n\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '\n[auth]\nrequired = true\nprotected_only = false\npath = "{}"\n'
            .format(self.store, self.port, self.auth), encoding="ascii")
        enrolled = subprocess.run(
            [sys.executable, "bin/fn", "--config", str(self.config),
             "principal", "set-password", "native-reader",
             "--password", "correct-horse", "--posting"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=600, check=False)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())

    def start(self):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run", "--once"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment())
        line = wait_for_announcement(process, b"LISTENING ")
        if not line.startswith(b"LISTENING "):
            diagnostic = stop_and_diagnostics(process)
            process.stdout.close()
            process.stderr.close()
            self.fail("native authenticated owner failed: {} {}".format(
                line, diagnostic))
        return process

    def test_generated_credential_gates_reader_and_does_not_grant_transit(self):
        process = self.start()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"201 "))

                stream.write(b"GROUP fn.test\r\n")
                self.assertTrue(stream.readline().startswith(b"480 "))

                # Transit authority remains the peer record's.  A reader
                # login policy neither authorizes nor intercepts IHAVE.
                stream.write(b"IHAVE <reader-is-not-peer@example.invalid>\r\n")
                self.assertTrue(stream.readline().startswith(b"502 "))

                stream.write(b"AUTHINFO USER native-reader\r\n")
                self.assertTrue(stream.readline().startswith(b"381 "))
                stream.write(b"AUTHINFO PASS wrong\r\n")
                self.assertTrue(stream.readline().startswith(b"481 "))
                stream.write(b"GROUP fn.test\r\n")
                self.assertTrue(stream.readline().startswith(b"480 "))

                stream.write(b"AUTHINFO USER native-reader\r\n")
                self.assertTrue(stream.readline().startswith(b"381 "))
                stream.write(b"AUTHINFO PASS correct-horse\r\n")
                self.assertTrue(stream.readline().startswith(b"281 "))
                stream.write(b"GROUP fn.test\r\n")
                self.assertTrue(stream.readline().startswith(b"211 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertEqual(process.wait(timeout=60), 0,
                             process.stderr.read().decode("utf-8", "replace"))
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

    def test_restricted_command_before_login_is_480_and_leaves_no_article(self):
        # P1 (b) on the image: fn-served-dispatch-of-a-gated-command-is-480-
        # and-changes-nothing says a restricted command before the login is
        # answered 480 and the connection -- wire framing included -- is the
        # one it arrived on.  Observed here as: POST is 480 and never 340, the
        # article a client sends anyway is read as command lines and none of
        # them is accepted, and after the run the store holds no article under
        # that Message-ID.  The same client, logged in, posts a second
        # article, which the store then holds: the refusal is the gate's, not
        # a store that accepts nothing.
        refused = "<p1-before-login@example.invalid>"
        posted = "<p1-after-login@example.invalid>"

        def article(message_id):
            return [b"From: Native Reader <reader@example.invalid>",
                    b"Newsgroups: fn.test",
                    b"Subject: P1 gate",
                    b"Message-ID: " + message_id.encode("ascii"),
                    b"",
                    b"P1 gate body."]

        process = self.start()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"201 "))

                stream.write(b"POST\r\n")
                self.assertTrue(stream.readline().startswith(b"480 "))
                # A client that ignores the 480 and sends the article: the wire
                # never entered article mode, so each non-empty line is a
                # command, answered on its own and never accepted.
                for line in article(refused) + [b"."]:
                    if not line:
                        continue
                    stream.write(line + b"\r\n")
                    reply = stream.readline()
                    self.assertFalse(reply.startswith((b"240 ", b"340 ")), reply)
                    self.assertTrue(reply[:1] in (b"4", b"5"), reply)
                for command in (b"ARTICLE " + refused.encode("ascii"),
                                b"STAT " + refused.encode("ascii"),
                                b"GROUP fn.test"):
                    stream.write(command + b"\r\n")
                    self.assertTrue(stream.readline().startswith(b"480 "), command)

                stream.write(b"AUTHINFO USER native-reader\r\n")
                self.assertTrue(stream.readline().startswith(b"381 "))
                stream.write(b"AUTHINFO PASS correct-horse\r\n")
                self.assertTrue(stream.readline().startswith(b"281 "))
                stream.write(b"POST\r\n")
                self.assertTrue(stream.readline().startswith(b"340 "))
                for line in article(posted):
                    stream.write(line + b"\r\n")
                stream.write(b".\r\n")
                self.assertTrue(stream.readline().startswith(b"240 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertEqual(process.wait(timeout=60), 0,
                             process.stderr.read().decode("utf-8", "replace"))
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

        def inspect(message_id):
            return subprocess.run(
                [str(IMAGE), "--fn", "store", str(self.store), "inspect",
                 message_id], cwd=ROOT, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, env=environment(), timeout=180,
                check=False)

        held = inspect(posted)
        self.assertEqual(held.returncode, 0, held.stderr.decode())
        self.assertNotEqual(inspect(refused).returncode, 0)

    def test_protected_only_is_refused_before_listener(self):
        text = self.config.read_text(encoding="ascii").replace(
            "protected_only = false", "protected_only = true")
        protected = Path(self.temporary.name) / "protected.toml"
        protected.write_text(text, encoding="ascii")
        result = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(protected), "run", "--once"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(result.returncode, 5, result.stderr.decode())
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"unsupported-profile", result.stderr.lower())

    def test_legacy_cleartext_registry_is_refused_before_listener(self):
        self.auth.write_text(
            '[login."legacy"]\nsecret = "never-read"\n', encoding="ascii")
        result = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(self.config), "run", "--once"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(result.returncode, 1, result.stderr.decode())
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"cleartext-credential", result.stderr.lower())


    # -------------------------------------------------------------- PKT-221

    def test_a_rebinding_applies_live_and_an_open_session_keeps_its_binding(self):
        """SCN-096 (PKT-221): `principal bind' against a running owner.

        The login is bound to P under `posting-policy bound-logins'.  Session
        A authenticates; the operator re-binds the login to Q while A is open
        and the owner runs (no restart): the verb answers `applied'.  A's
        article signed by P is accepted (A keeps the binding its connection
        pinned, books/login-binding-live.lisp
        fn-lb-an-open-session-is-decided-under-its-pinned-table); a new
        session B's article signed by P is refused `login-not-bound' (B pins
        the published table, fn-lb-a-connection-opened-after-a-publication-
        is-bound-anew).  The owner process is the same throughout."""
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        root = Path(self.temporary.name)
        control, log = root / "control.sock", root / "fn.log"
        config = root / "live.toml"
        config.write_text(self.config.read_text(encoding="ascii")
                          + '\n[control]\npath = "{}"\n\n[log]\npath = "{}"\n'
                          .format(control, log), encoding="ascii")
        operator = [str(IMAGE), "--fn", "operator", str(config)]
        p_principal, q_principal = bytes([85]) * 32, bytes([86]) * 32

        def run(arguments, expected=0):
            result = subprocess.run(arguments, cwd=ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, env=environment(),
                                    timeout=600, check=False)
            self.assertEqual(result.returncode, expected,
                             (arguments, result.stdout, result.stderr))
            return result

        bound = run(operator + ["principal", "bind", "native-reader", p_principal.hex()])
        self.assertIn(b"accepted operator principal bind effective-at-next-start",
                      bound.stderr)
        run(operator + ["policy", "set", "posting-policy", "bound-logins"])
        process = subprocess.Popen(operator + ["run"], cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, env=environment())
        self.addCleanup(lambda: process.poll() is None and stop_and_diagnostics(process))
        line = wait_for_announcement(process, b"LISTENING ")
        self.assertTrue(line.startswith(b"LISTENING "), line)
        # P enrolled at generation 1 (the fixed Ed25519 test key, a fresh
        # ML-DSA-65 key), and two articles signed by P.
        principal, ed_public, ed_secret = (root / "p.bin", root / "ed-public.bin",
                                           root / "ed-secret.bin")
        principal.write_bytes(p_principal)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ml_private, ml_public = root / "ml-private.pem", root / "ml-public.pem"
        run([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(ml_private)])
        run([openssl, "pkey", "-in", str(ml_private), "-pubout", "-out", str(ml_public)])
        run([str(IMAGE), "--fn", "hybrid-enroll", str(control), "1", str(principal),
             str(ed_public), str(ml_public)])
        articles = []
        for name in ("a", "b"):
            source, carried = root / (name + ".eml"), root / (name + "-carried.eml")
            source.write_bytes(
                b"From: bound@example.invalid\r\nDate: Sat, 26 Sep 2026 14:00:00 +0000\r\n"
                b"Newsgroups: fn.test\r\nSubject: signed by P\r\n"
                b"Message-ID: <rebind-" + name.encode() + b"@example.invalid>\r\n\r\n"
                b"signed by P\r\n")
            run([str(IMAGE), "--fn", "hybrid-sign-carrier", str(principal), str(ed_public),
                 str(ed_secret), str(ml_public), str(ml_private), str(source), str(carried)])
            articles.append(carried.read_bytes())

        def session():
            client = socket.create_connection(("127.0.0.1", self.port), timeout=60)
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"20"))
            stream.write(b"AUTHINFO USER native-reader\r\n")
            self.assertTrue(stream.readline().startswith(b"381"))
            stream.write(b"AUTHINFO PASS correct-horse\r\n")
            self.assertTrue(stream.readline().startswith(b"281"))
            return client, stream

        def post(stream, article):
            stream.write(b"POST\r\n")
            self.assertTrue(stream.readline().startswith(b"340"))
            body = article if article.endswith(b"\r\n") else article + b"\r\n"
            stream.write(body + b".\r\n")
            return stream.readline().decode("ascii", "replace").strip()

        client_a, stream_a = session()
        rebound = run(operator + ["principal", "bind", "native-reader", q_principal.hex()])
        self.assertIn(b"accepted operator principal bind applied", rebound.stderr)
        reply_a = post(stream_a, articles[0])
        client_b, stream_b = session()
        reply_b = post(stream_b, articles[1])
        still_running = process.poll() is None
        for client in (client_a, client_b):
            client.close()
        diagnostic = stop_and_diagnostics(process)
        text = log.read_text(encoding="ascii", errors="replace")
        print("NATIVE-AUTH-REBIND-WITNESS", reply_a, "|", reply_b)
        self.assertTrue(still_running, diagnostic)
        self.assertTrue(reply_a.startswith("240"), (reply_a, text))
        self.assertTrue(reply_b.startswith("441"), (reply_b, text))
        self.assertIn("not bound", reply_b)
        self.assertIn("post login=native-reader bound=" + p_principal.hex(), text)
        self.assertIn("post login=native-reader refused login-not-bound", text)

if __name__ == "__main__":
    unittest.main()
