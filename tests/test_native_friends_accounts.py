"""SCN-094: an invitation-code account, redeemed over TLS, once, across a
crash (PRF-164, NNT-034; PKT-439, PKT-440).

One node A on loopback with an implicit-TLS listener and `[auth]
protected_only = true` and no auth.toml.  The operator runs `account invite`
(the code is printed once); a friend's client, over TLS, sends `XREDEEM CODE
LOGIN` and `XREDEEM PASS PASSWORD` and is answered 281; on a new connection
AUTHINFO USER/PASS as LOGIN is 281 and a POST is 240.  The same code for
another login is 482; the same exchange again is 281 (the resume).  A second
code is redeemed on a developer image with FN_ACCOUNT_TEST_STOP_AFTER_PUBLISH:
the owner dies after the publication and before the reply; after a restart
the account logs in and the retried exchange answers 281.  Plaintext XREDEEM
on the protected listener is 483.  `account list` names both logins and
never a code.  Finally, when FN_OLD_IMAGE names an image from before accounts
(the deployed bbf52159), it refuses to open the store (PKT-440, witnessed).

The decisions are ACL2's: books/nntp-auth.lisp fn-auth-xredeem and
fn-auth-redeem-outcome, books/accounts.lisp fn-acct-redeem-bounded-plan and
fn-acct-redeem-word, run by host/native/admin.lisp fnn-owner-account-redeem.

FN_FRIEND_FN, when set, is `bin/fn` from an unpacked release tarball
(tests/friends_tarball.sh): the node then runs that installed image for
every step except the developer-image crash cut.

PRF-388 (PKT-560): a redeemed login is bound to a signing principal with
the same verb as a credential-file login, `principal bind LOGIN HEX', live
and offline.  Under `posting-policy bound-logins' its unsigned post is then
441 (login-unsigned); the binding survives a restart (the start publication
of the credential file's table leaves an account's binding); `account
delete' is refused while it holds; `principal unbind' ends it (240 again);
and `principal bind' of a login that is neither the file's nor an account's
is refused `unknown-login' (exit 1).  Refuted: a refusal of the redeemed
login, an unsigned 240 while bound, a binding lost at restart, or a binding
of a login nobody holds.

Run: FN_NATIVE_HOST=<developer launcher> python3 -m unittest -v tests.test_native_friends_accounts
"""

import os
import re
import ssl
import subprocess
import unittest

from tests.native_harness import (
    ROOT, Client, Node, article, client_context, free_port, native_image, run)
from tests.sasl_client import scram_login, status_data

IMAGE = native_image("FN_NATIVE_HOST", "build/fn-host-developer")
if not os.environ.get("FN_NATIVE_HOST") and not IMAGE.is_file():
    IMAGE = ROOT / "build" / "fn-host"
FRIEND_FN = os.environ.get("FN_FRIEND_FN")
SMALL_PROFILE = ("--max-transactions", "16384", "--max-history-octets", "8388608",
                 "--max-record-octets", "196608", "--max-article-octets", "32768",
                 "--max-groups-per-article", "16", "--max-open-suffix", "128")
OLD_IMAGE = os.environ.get("FN_OLD_IMAGE")
READY = bool(IMAGE.is_file() and os.access(IMAGE, os.X_OK))
DEVELOPER = "developer" in IMAGE.name


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace").strip()


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativeFriendsAccountsTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE, launcher=FRIEND_FN).use_tls(alt_name=True)
        self.root, self.store, self.port = self.node.root, self.node.store_path, self.node.port
        self.tls_port = self.node.tls_port
        small = SMALL_PROFILE if FRIEND_FN else ()
        self.ok("init", *small, "local.general")

    def operator(self, *words, image=None):
        result = self.node.operator(*words, image=image, timeout=240)
        print("NATIVE-ACCOUNTS", " ".join(words[:2]), "->", result.returncode)
        return result

    def ok(self, *words):
        result = self.operator(*words)
        self.assertEqual(result.returncode, 0, text(result))
        return result

    def stop(self):
        process = self.node.process
        self.node.stop()
        return process.stderr.since(0).decode("utf-8", "replace")

    def tls(self):
        return Client(self.tls_port, implicit_tls=client_context(), greeting=None)

    def exchange(self, client, line):
        reply = client.command(line).decode("ascii", "replace").strip()
        print("NATIVE-ACCOUNTS", line.split()[0], line.split()[1] if " " in line else "",
              "->", reply[:3])
        return reply

    def redeem(self, code, login, password):
        stream = self.tls()
        first = self.exchange(stream, "XREDEEM {} {}".format(code, login))
        if not first.startswith("381"):
            return first
        return self.exchange(stream, "XREDEEM PASS " + password)

    def login_and_post(self, login, password, message_id):
        with self.tls() as client:
            self.assertTrue(self.exchange(client, "AUTHINFO USER " + login).startswith("381"))
            reply = self.exchange(client, "AUTHINFO PASS " + password)
            if not reply.startswith("281"):
                return reply
            first, final = client.post(article(
                message_id, sender=login + "@friend.example", groups="local.general",
                subject="hello", date=None))
            self.assertTrue(first.startswith(b"340"), first)
            return final.decode("ascii", "replace").strip()

    def scram_login_and_post(self, login, password, message_id):
        """SCRAM-SHA-256 (RFC 4643 2.4, RFC 7677) as LOGIN on a new TLS
        connection, then one POST: the POST's final status, or the failed
        login's line."""
        with self.tls() as client:
            final, scram, _ = scram_login(client.command, client.command, login, password)
            status, data = status_data(final)
            print("NATIVE-ACCOUNTS AUTHINFO SASL SCRAM-SHA-256 ->", status)
            if status != "283":
                return final.decode("ascii", "replace").strip()
            self.assertTrue(scram.server_final_ok(data), final)
            first, done = client.post(article(
                message_id, sender=login + "@friend.example", groups="local.general",
                subject="hello", date=None))
            self.assertTrue(first.startswith(b"340"), first)
            return done.decode("ascii", "replace").strip()

    def invite(self):
        result = self.ok("account", "invite", "--expires", "3600")
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, text(result))
        return codes[0].decode("ascii")

    def fn_redeem(self, *words, password="correct-horse"):  # FAKE-SECRET: a test fixture's password
        # `fn redeem` (the stranger rehearsal's stop 10): no openssl, no
        # hand-typed XREDEEM.  The password comes on standard input.
        return subprocess.run([str(IMAGE), "--fn", "redeem", *words], cwd=ROOT,
                              env=self.node.environment(), input=(password + "\n").encode(),
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=120, check=False, start_new_session=True)

    def test_fn_redeem_over_starttls_and_tls(self):
        self.node.start()
        cert = str(self.root / "cert.pem")
        # STARTTLS on the reader port (the default), the node's own
        # self-signed certificate trusted by --cafile.
        code = self.invite()
        done = self.fn_redeem("127.0.0.1:{}".format(self.port), code, "wren", "--cafile", cert)
        self.assertEqual(done.returncode, 0, text(done))
        self.assertIn(b"redeemed: the account wren is ready", done.stdout)
        self.assertTrue(self.login_and_post("wren", "correct-horse",
                                            "<wren-1@friend.example>").startswith("240"))
        # Implicit TLS on the TLS port.
        code = self.invite()
        done = self.fn_redeem("127.0.0.1:{}".format(self.tls_port), code, "finch",
                              "--tls", "--cafile", cert)
        self.assertEqual(done.returncode, 0, text(done))
        # A used code: refused by name, exit 1, with the server's line.
        again = self.fn_redeem("127.0.0.1:{}".format(self.tls_port), code, "finch2",
                               "--tls", "--cafile", cert)
        self.assertEqual(again.returncode, 1, text(again))
        self.assertIn(b"refused redeem code: ", again.stderr)
        self.assertIn(b"the server said: 48", again.stderr)
        # No trust anchor for a self-signed node: the handshake is refused,
        # never an unchecked session.
        untrusted = self.fn_redeem("127.0.0.1:{}".format(self.tls_port), code, "finch3", "--tls")
        self.assertEqual(untrusted.returncode, 1, text(untrusted))
        self.assertIn(b"refused redeem tls: ", untrusted.stderr)
        self.assertNotIn(b"redeemed", untrusted.stdout)
        self.stop()

    def capabilities(self, client):
        first, body = client.multiline(b"CAPABILITIES")
        self.assertTrue(first.startswith(b"101"), first)
        return body.split(b"\r\n")[:-1]

    def test_authinfo_is_offered_after_starttls_before_any_account(self):
        # The public node's deploy finding D1 (RFC 4643 s2.2), in its
        # configuration: protected_only, `policy set anonymous none`, no
        # auth.toml and no account redeemed yet.  In clear, STARTTLS and no
        # AUTHINFO; after STARTTLS, and on the TLS port, AUTHINFO USER
        # (books/nntp-auth.lisp fn-auth-access-capability-lines: a login is
        # required, so the mechanism is offered with no credential yet).
        self.ok("policy", "set", "anonymous", "none")
        self.node.start()
        clear = self.node.session(greeting=None)
        self.addCleanup(clear.close)
        # The AUTHINFO line's arguments (RFC 4643 section 2.2: USER, and SASL
        # beside it since NNT-056), never an exact-line match.
        def authinfo(labels):
            return [set(l.split()[1:]) for l in labels if l.split()[:1] == [b"AUTHINFO"]]
        listed = self.capabilities(clear)
        self.assertIn(b"STARTTLS", listed)
        self.assertEqual(authinfo(listed), [])
        self.assertTrue(clear.starttls().startswith(b"382"))
        listed = self.capabilities(clear)
        self.assertEqual(len(authinfo(listed)), 1, listed)
        self.assertIn(b"USER", authinfo(listed)[0])
        self.assertNotIn(b"STARTTLS", listed)
        overtls = authinfo(self.capabilities(self.tls()))
        self.assertEqual(len(overtls), 1, overtls)
        self.assertIn(b"USER", overtls[0])
        self.stop()

    def test_fn_redeem_to_an_unreachable_node_is_uncertain_never_refused(self):
        # The OpenBSD rehearsal's finding 8 (packet C): nothing listens on
        # the port.  ACL2's fn-redeem-lost at :connect, exit 3 (fenced), the
        # words say unreachable, and no password prompt is printed when the
        # password comes on standard input.
        closed = free_port()
        lost = self.fn_redeem("127.0.0.1:{}".format(closed), "0" * 32, "wren", "--tls",
                              "--cafile", str(self.root / "cert.pem"))
        self.assertEqual(lost.returncode, 3, text(lost))
        self.assertIn(b"unreachable redeem: ", lost.stderr)
        self.assertNotIn(b"refused redeem", lost.stderr)
        self.assertNotIn(b"Password for the new account", lost.stderr)
        self.assertEqual(lost.stdout, b"")

    def test_a_redeemed_login_is_bound_and_keeps_its_binding(self):
        principal = "55" * 32
        self.node.start()
        self.assertTrue(self.redeem(self.invite(), "robin", "correct-horse").startswith("281"))
        self.ok("policy", "set", "posting-policy", "bound-logins")
        # Live: the owner publishes the account's binding.
        bound = self.ok("principal", "bind", "robin", principal)
        self.assertIn(b"accepted operator account", bound.stderr)
        reply = self.login_and_post("robin", "correct-horse", "<robin-b1@friend.example>")
        self.assertTrue(reply.startswith("441"), reply)
        self.assertIn("signed by its bound principal", reply)
        self.assertIn("binding robin " + principal,
                      self.ok("account", "list").stdout.decode("ascii"))
        # The binding is an obligation: the account cannot be deleted.
        held = self.operator("account", "delete", "robin")
        self.assertEqual(held.returncode, 1, text(held))
        # Neither the file's login nor an account's: refused by name.
        nobody = self.operator("principal", "bind", "nobody", principal)
        self.assertEqual(nobody.returncode, 1, text(nobody))
        self.assertIn(b"unknown-login", nobody.stderr)
        # A restart keeps it: the start publication leaves an account's binding.
        self.stop()
        self.node.start()
        reply = self.login_and_post("robin", "correct-horse", "<robin-b2@friend.example>")
        self.assertTrue(reply.startswith("441"), reply)
        # Unbind (live), then the unsigned post is accepted again.
        self.ok("principal", "unbind", "robin")
        reply = self.login_and_post("robin", "correct-horse", "<robin-b3@friend.example>")
        self.assertTrue(reply.startswith("240"), reply)
        # Offline: bound while no owner runs, in force at the next start.
        self.stop()
        offline = self.ok("principal", "bind", "robin", principal)
        self.assertIn(b"accepted operator account", offline.stderr)
        self.node.start()
        reply = self.login_and_post("robin", "correct-horse", "<robin-b4@friend.example>")
        self.assertTrue(reply.startswith("441"), reply)
        self.stop()

    def test_a_code_invited_while_the_node_is_stopped_redeems(self):
        # PRF-374, bug M1 (lane node-migrate): an invitation made while no
        # owner runs is stamped by the offline configuration record, whose
        # clock is in SECONDS; the expiry was computed as if it were
        # milliseconds, so the code was born expired and XREDEEM answered
        # 482.  books/accounts.lisp fn-acct-offline-invite-reading names the
        # unit; the expiry is now + expires in milliseconds on both paths,
        # and since PRF-378 the record stamp is milliseconds too, so the
        # redeem record is admitted by the same comparison the plan made.
        stopped = self.invite()
        self.node.start()
        running = self.invite()
        self.assertTrue(self.redeem(stopped, "sparrow", "correct-horse").startswith("281"))
        self.assertTrue(self.redeem(running, "starling", "battery-staple").startswith("281"))
        listed = self.ok("account", "list").stdout.decode("ascii")
        self.assertIn("redeemed sparrow ", listed)
        self.assertIn("redeemed starling ", listed)
        self.stop()

    def test_a_friend_redeems_a_code_once_across_a_crash(self):
        self.node.start()
        code = self.invite()
        # Cleartext on the protected listener: 483, nothing taken.
        with self.node.session(greeting=None) as plain:
            self.assertTrue(self.exchange(plain, "XREDEEM {} robin".format(code))
                            .startswith("483"))
        self.assertTrue(self.redeem(code, "robin", "correct-horse").startswith("281"))
        reply = self.login_and_post("robin", "correct-horse", "<robin-1@friend.example>")
        self.assertTrue(reply.startswith("240"), reply)
        # The redeemed account's verifier serves SCRAM too (the redeem wrote
        # the SCRAM keys with the digest).
        reply = self.scram_login_and_post("robin", "correct-horse", "<robin-scram@friend.example>")
        self.assertTrue(reply.startswith("240"), reply)
        self.assertTrue(self.redeem(code, "mallory", "x").startswith("482"))
        self.assertTrue(self.redeem(code, "robin", "correct-horse").startswith("281"))
        self.assertTrue(self.redeem("0" * 32, "eve", "x").startswith("482"))
        listed = self.ok("account", "list").stdout.decode("ascii")
        self.assertIn("redeemed robin ", listed)
        self.assertNotIn(code, listed)
        # The crash cut between the publication and the reply (developer image).
        second = self.invite()
        log = self.stop()
        self.assertNotIn(code, log)
        self.assertNotIn(second, log)
        if DEVELOPER:
            crashed = self.node.start(image=IMAGE,
                                      env={"FN_ACCOUNT_TEST_STOP_AFTER_PUBLISH": "1"})
            client = self.tls()
            self.addCleanup(client.close, quit=False)
            self.assertTrue(self.exchange(client, "XREDEEM {} robin2".format(second))
                            .startswith("381"))
            client.send(b"XREDEEM PASS battery-staple\r\n")
            try:
                lost = client.line()
            except (OSError, ssl.SSLError, EOFError):
                lost = b""
            self.assertEqual(lost, b"")
            self.assertEqual(crashed.wait(timeout=60), 137)
            crashed.finish()
            self.node.start()
            self.assertTrue(self.redeem(second, "robin2", "battery-staple")
                            .startswith("281"))
            reply = self.login_and_post("robin2", "battery-staple",
                                        "<robin2-1@friend.example>")
            self.assertTrue(reply.startswith("240"), reply)
            self.stop()
        # PKT-440: an image from before accounts refuses this store, and
        # (the control) opens a store that never issued a code.  Its fn.toml
        # names only the store and a listener, which that image parses.
        if OLD_IMAGE:
            def old_status(store, name):
                config = self.root / (name + ".toml")
                config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
                                  'port = {}\n'.format(store, free_port()), encoding="ascii")
                result = run([OLD_IMAGE, "--fn", "operator", config, "status"], timeout=240)
                print("NATIVE-ACCOUNTS old-image status", name, "->", result.returncode,
                      text(result)[-160:].replace("\n", " "))
                return result
            fresh_node = Node(self, IMAGE, launcher=FRIEND_FN, root=self.root / "fresh",
                                    control=False)
            fresh = fresh_node.store_path
            made = fresh_node.operator("init", *(SMALL_PROFILE if FRIEND_FN else ()),
                                       "local.general", timeout=240)
            self.assertEqual(made.returncode, 0, text(made))
            self.assertEqual(old_status(fresh, "fresh").returncode, 0)
            refused = old_status(self.store, "redeemed")
            self.assertNotEqual(refused.returncode, 0)
            self.assertNotIn("usage", text(refused))
