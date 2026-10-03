"""AUTHINFO through the installed native operator/owner, with no Python server."""
import os
import subprocess
import unittest

from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_USAGE, ROOT, Client, Node, native_image, requires)

IMAGE = native_image("FN_NATIVE_HOST")


@requires(IMAGE)
class NativeAuthTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE, control=False)
        self.root, self.store, self.config = self.node.root, self.node.store_path, self.node.config
        self.port = self.node.port
        self.auth = self.root / "credentials.toml"
        initialized = self.node.store("init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.node.write_config(extra='\n[auth]\nrequired = true\nprotected_only = false\n'
                                     'path = "{}"\n'.format(self.auth))
        # The native operator reads the password and its confirmation from
        # standard input when there is no tty.
        self.node.operator("principal", "set-password", "native-reader", "--posting",
                           input=b"correct-horse\ncorrect-horse\n", expect=EXIT_OK)

    def start(self):
        """The owner for one connection (`run --once`)."""
        return self.node.start(verb=("run", "--once"))

    def client(self, greeting=(b"201",)):
        return Client(self.port, timeout=30, greeting=greeting)

    def expect_line(self, client, octets, status):
        client.send(octets + b"\r\n")
        self.assertTrue(client.line().startswith(status), octets)

    def test_generated_credential_gates_reader_and_does_not_grant_transit(self):
        self.start()
        with self.client() as client:
            self.expect_line(client, b"GROUP fn.test", b"480 ")
            # Transit authority remains the peer record's.  A reader
            # login policy neither authorizes nor intercepts IHAVE.
            self.expect_line(client, b"IHAVE <reader-is-not-peer@example.invalid>", b"502 ")
            self.expect_line(client, b"AUTHINFO USER native-reader", b"381 ")
            self.expect_line(client, b"AUTHINFO PASS wrong", b"481 ")
            self.expect_line(client, b"GROUP fn.test", b"480 ")
            self.expect_line(client, b"AUTHINFO USER native-reader", b"381 ")
            self.expect_line(client, b"AUTHINFO PASS correct-horse", b"281 ")
            self.expect_line(client, b"GROUP fn.test", b"211 ")
            self.expect_line(client, b"QUIT", b"205 ")
            client.close(quit=False)
        self.node.exited(EXIT_OK)

    def test_authenticated_starttls_is_unavailable_and_keeps_reader_selection(self):
        # S120 / PRF-1266: real TLS availability makes pre-login advertisement
        # affirmative, so missing STARTTLS after 281 is a discriminator.
        self.node.use_tls(protected_only=False)
        self.config.write_text(self.config.read_text() +
            '\n[auth]\nrequired = true\nprotected_only = false\npath = "{}"\n'.format(self.auth))
        self.start()
        with self.client() as client:
            status, before = client.multiline("CAPABILITIES")
            self.assertTrue(status.startswith(b"101 "), status)
            self.assertIn(b"STARTTLS\r\n", before)
            self.expect_line(client, b"AUTHINFO USER native-reader", b"381 ")
            self.expect_line(client, b"AUTHINFO PASS correct-horse", b"281 ")
            self.expect_line(client, b"GROUP fn.test", b"211 ")
            status, after = client.multiline("CAPABILITIES")
            self.assertTrue(status.startswith(b"101 "), status)
            self.assertNotIn(b"STARTTLS\r\n", after)
            self.expect_line(client, b"STARTTLS", b"502 ")
            # Login and selection both survive refusal; LISTGROUP with no
            # name would be 480/412 if either had been reset.
            status, rows = client.multiline("LISTGROUP")
            self.assertTrue(status.startswith(b"211 "), (status, rows))
            self.expect_line(client, b"QUIT", b"205 ")
            client.close(quit=False)
        self.node.exited(EXIT_OK)

    def test_ten_pipelined_wrong_passwords_get_three_481s_then_400_and_eof(self):
        # Sweep S044, NNT-1002 (fn-auth-failed-pass-at-the-limit-is-481-400-
        # and-closes): one read carrying ten USER/PASS pairs with a wrong
        # password, and a GROUP after them, is answered 381/481 three times,
        # then the 400, then the connection closes; the fourth guess and the
        # GROUP are never answered.  The owner is still serving: a new
        # connection logs in.
        self.node.start()
        with self.client() as client:
            client.send(b"AUTHINFO USER native-reader\r\nAUTHINFO PASS wrong\r\n" * 10
                        + b"GROUP fn.test\r\n")
            replies = []
            try:
                while True:
                    replies.append(client.line()[:3])
            except EOFError:
                pass
            client.close(quit=False)
        self.assertEqual(replies, [b"381", b"481"] * 3 + [b"400"], replies)
        with self.client() as client:
            self.expect_line(client, b"AUTHINFO USER native-reader", b"381 ")
            self.expect_line(client, b"AUTHINFO PASS correct-horse", b"281 ")
            self.expect_line(client, b"QUIT", b"205 ")
            client.close(quit=False)
        self.node.stop()

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

        self.start()
        with self.client() as client:
            self.expect_line(client, b"POST", b"480 ")
            # A client that ignores the 480 and sends the article: the wire
            # never entered article mode, so each non-empty line is a
            # command, answered on its own and never accepted.
            for line in article(refused) + [b"."]:
                if not line:
                    continue
                client.send(line + b"\r\n")
                reply = client.line()
                self.assertFalse(reply.startswith((b"240 ", b"340 ")), reply)
                self.assertTrue(reply[:1] in (b"4", b"5"), reply)
            for command in (b"ARTICLE " + refused.encode("ascii"),
                            b"STAT " + refused.encode("ascii"),
                            b"GROUP fn.test"):
                self.expect_line(client, command, b"480 ")
            self.expect_line(client, b"AUTHINFO USER native-reader", b"381 ")
            self.expect_line(client, b"AUTHINFO PASS correct-horse", b"281 ")
            first, final = client.post(b"\r\n".join(article(posted)) + b"\r\n")
            self.assertTrue(first.startswith(b"340 "), first)
            self.assertTrue(final.startswith(b"240 "), final)
            self.expect_line(client, b"QUIT", b"205 ")
            client.close(quit=False)
        self.node.exited(EXIT_OK)

        def inspect(message_id):
            return self.node.store("inspect", message_id)

        held = inspect(posted)
        self.assertEqual(held.returncode, 0, held.stderr.decode())
        self.assertNotEqual(inspect(refused).returncode, 0)

    def test_protected_only_is_refused_before_listener(self):
        text = self.config.read_text(encoding="ascii").replace(
            "protected_only = false", "protected_only = true")
        protected = self.root / "protected.toml"
        protected.write_text(text, encoding="ascii")
        result = self.node.invoke("operator", protected, "run", "--once")
        self.assertEqual(result.returncode, EXIT_USAGE, result.stderr.decode())
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"unsupported-profile", result.stderr.lower())

    def test_legacy_cleartext_registry_is_refused_before_listener(self):
        self.auth.write_text(
            '[login."legacy"]\nsecret = "never-read"\n', encoding="ascii")
        result = self.node.operator("run", "--once")
        self.assertEqual(result.returncode, EXIT_REFUSED, result.stderr.decode())
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
        root = self.root
        control, log = root / "control.sock", root / "fn.log"
        config = self.config
        config.write_text(self.config.read_text(encoding="ascii")
                          + '\n[control]\npath = "{}"\n\n[log]\npath = "{}"\n'
                          .format(control, log), encoding="ascii")
        operator = [str(IMAGE), "--fn", "operator", str(config)]
        p_principal, q_principal = bytes([85]) * 32, bytes([86]) * 32

        def run(arguments, expected=0):
            result = subprocess.run(arguments, cwd=ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, env=self.node.environment(),
                                    timeout=600, check=False)
            self.assertEqual(result.returncode, expected,
                             (arguments, result.stdout, result.stderr))
            return result

        bound = run(operator + ["principal", "bind", "native-reader", p_principal.hex()])
        self.assertIn(b"accepted operator principal bind effective-at-next-start",
                      bound.stderr)
        run(operator + ["policy", "set", "posting-policy", "bound-logins"])
        process = self.node.start()
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
            client = Client(self.port, timeout=60, greeting=(b"200", b"201"))
            self.expect_line(client, b"AUTHINFO USER native-reader", b"381")
            self.expect_line(client, b"AUTHINFO PASS correct-horse", b"281")
            return client

        def post(client, article):
            first, final = client.post(article)
            self.assertTrue(first.startswith(b"340"), first)
            return final.decode("ascii", "replace").strip()

        client_a = session()
        rebound = run(operator + ["principal", "bind", "native-reader", q_principal.hex()])
        self.assertIn(b"accepted operator principal bind applied", rebound.stderr)
        reply_a = post(client_a, articles[0])
        client_b = session()
        reply_b = post(client_b, articles[1])
        still_running = process.poll() is None
        for client in (client_a, client_b):
            client.close(quit=False)
        self.node.stop(expect=None)
        diagnostic = process.diagnostics()
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
