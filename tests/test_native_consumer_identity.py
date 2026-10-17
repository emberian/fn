"""SCN-160: local consumers bound to accounts (PRF-234, CNS-006).

One node with two invitation-code accounts: alice has no access rule and bob
reads `fn.*,!fn.private.*`.  alice posts a mixed stream over NNTP: two
articles in fn.private.x, two in fn.public and one cross-posted to both.
Four local consumers are registered over the owner's 0600 control socket
and the operator binds three of them live with `consumer bind NAME
--account LOGIN`:

  bob-pub     fn.public     bound to bob
  bob-priv    fn.private.x  bound to bob
  alice-priv  fn.private.x  bound to alice
  operator    fn.private.x  unbound (the operator's, as before)

Each bound consumer polls and acks with its account's password
(`consumer bound-poll` / `bound-ack`, the password read from a file) and is
served only the events of a group its account reads: bob-pub the public
and cross-posted articles, alice-priv the private and cross-posted ones,
bob-priv nothing (refused, its position kept).  A wrong password is
refused; the plain poll of a bound consumer is refused; the unbound
consumer is served everything as before.  An owner restart keeps every
cursor; widening bob's rule lets bob-priv resume from where it stopped
(nothing was skipped); `consumer unbind` returns a consumer to the
operator.  The scenario runs on the production image (FN_NATIVE_HOST) and on
the developer image (FN_NATIVE_DEVELOPER_HOST).

The decisions are ACL2's: books/consumer-bound.lisp fn-cbind-poll /
fn-cbind-ack (the binding, the credential, the read rule) and
fn-cbind-plain-poll / fn-cbind-plain-ack; the binding is the
configuration's (books/config.lisp fn-cfg-consumer-bind, delta code 24).

Run: FN_NATIVE_HOST=<production launcher> FN_NATIVE_DEVELOPER_HOST=<developer
launcher> python3 -m unittest -v tests.test_native_consumer_identity
"""

import os
import re
import unittest

from tests.native_harness import ROOT, Client, Node, article, client_context, native_image

IMAGES = [("production", native_image("FN_NATIVE_HOST")),
          ("developer", native_image("FN_NATIVE_DEVELOPER_HOST"))]
READY = all(p.is_file() and os.access(p, os.X_OK) for _, p in IMAGES)


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace").strip()


class ConsumerIdentitySourceTests(unittest.TestCase):
    def test_the_host_calls_the_bound_decisions(self):
        host = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        # The polls read the live arena (records flip, flip-L6-2) inside the
        # withdrawal page (PKT-710, fn-cwd-page).
        for call in ("(fn-cbind-plain-poll-over (fn-owner-ocfg state) consumer",
                     "(fn-cbind-plain-ack (fn-owner-ocfg state) cursor-octets)",
                     "(fn-cbind-poll-over (fn-owner-ocfg state) (fn-owner-auth state)",
                     "(fn-cwd-page (fn-ocfg-owner (fn-owner-ocfg state)) consumer",
                     "(fn-cbind-ack (fn-owner-ocfg state) (fn-owner-auth state)"):
            self.assertIn(call, host)


MESSAGES = (("fn.private.x", "secret1"), ("fn.public", "pub1"),
            ("fn.private.x", "secret2"), ("fn.public", "pub2"),
            ("fn.public,fn.private.x", "cross"))


@unittest.skipUnless(READY, "the production and developer images are required")
class NativeConsumerIdentityTests(unittest.TestCase):
    def node(self, image):
        node = Node(self, image).use_tls()
        node.secrets = {}
        for login in ("alice", "bob"):
            path = node.root / ("secret-" + login)
            path.write_bytes(("pw-" + login + "\n").encode("ascii"))
            os.chmod(path, 0o600)
            node.secrets[login] = path
        wrong = node.root / "secret-wrong"
        wrong.write_bytes(b"pw-nobody\n")
        node.secrets["wrong"] = wrong
        return node

    def native(self, node, *words):
        result = node.invoke(*words, timeout=240)
        print("NATIVE-CONSUMER-IDENTITY", " ".join(map(str, words[:3])), "->",
              result.returncode)
        return result

    def operator(self, node, *words):
        return self.native(node, "operator", node.config, *words)

    def ok(self, node, *words):
        result = self.operator(node, *words)
        self.assertEqual(result.returncode, 0, text(result))
        return result

    def consumer(self, node, verb, *args):
        return self.native(node, "consumer", verb, node.control, *args)

    def tls(self, node):
        client = Client(node.tls_port, implicit_tls=client_context(), greeting=None)
        self.addCleanup(client.close, quit=False)
        return client

    @staticmethod
    def line(client, command):
        return client.command(command).decode("ascii", "replace").rstrip("\r\n")

    def account(self, node, login):
        result = self.ok(node, "account", "invite", "--expires", "3600")
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, text(result))
        stream = self.tls(node)
        self.assertTrue(self.line(stream, "XREDEEM {} {}".format(
            codes[0].decode("ascii"), login)).startswith("381"))
        self.assertTrue(self.line(stream, "XREDEEM PASS pw-" + login).startswith("281"))

    def post_all(self, node):
        stream = self.tls(node)
        self.assertTrue(self.line(stream, "AUTHINFO USER alice").startswith("381"))
        self.assertTrue(self.line(stream, "AUTHINFO PASS pw-alice").startswith("281"))
        for groups, tag in MESSAGES:
            first, final = stream.post(article(
                "<{}@example.invalid>".format(tag), groups=groups, subject=tag,
                sender="alice@example.invalid", date=None))
            self.assertTrue(first.startswith(b"340"), first)
            self.assertTrue(final.startswith(b"240"), (tag, final))

    def poll(self, node, name, secret=None):
        """(exit code, message tag or None, cursor path)."""
        cursor = node.root / ("cursor-" + name + "-" + os.urandom(4).hex())
        report = node.root / ("report-" + name + "-" + os.urandom(4).hex())
        if secret is None:
            result = self.consumer(node, "poll", name, cursor, report)
        else:
            result = self.consumer(node, "bound-poll", name, node.secrets[secret],
                                   cursor, report)
        if result.returncode != 0:
            self.assertFalse(cursor.exists())
            return result.returncode, None, None
        found = re.findall(rb"<([a-z0-9]+)@example\.invalid>", report.read_bytes())
        return 0, (found[0].decode("ascii") if found else None), cursor

    def ack(self, node, cursor, secret=None):
        if secret is None:
            return self.consumer(node, "ack", cursor).returncode
        return self.consumer(node, "bound-ack", cursor,
                             node.secrets[secret]).returncode

    def drain(self, node, name, secret, limit=16):
        """Poll and ack until an empty page; the tags served, in order."""
        seen = []
        for _ in range(limit):
            code, tag, cursor = self.poll(node, name, secret)
            self.assertEqual(code, 0, name)
            self.assertEqual(self.ack(node, cursor, secret), 0, name)
            if tag is None:
                return seen
            seen.append(tag)
        self.fail("no empty page after {} polls".format(limit))

    def scenario(self, image):
        node = self.node(image)
        self.ok(node, "init", "local.general")
        for group in ("fn.public", "fn.private.x"):
            self.ok(node, "group", "create", group)
        node.start()
        self.account(node, "alice")
        self.account(node, "bob")
        self.ok(node, "account", "access", "bob", "--read", "fn.*,!fn.private.*",
                "--post", "fn.*")

        boot = self.consumer(node, "bootstrap")
        self.assertEqual(boot.returncode, 0, text(boot))
        for name, group in (("bob-pub", "fn.public"), ("bob-priv", "fn.private.x"),
                            ("alice-priv", "fn.private.x"),
                            ("operator", "fn.private.x")):
            result = self.consumer(node, "register", name, group,
                                   node.root / ("registered-" + name))
            self.assertEqual(result.returncode, 0, text(result))
        # A binding names a consumer and a login; a malformed one is refused.
        self.assertNotEqual(self.operator(node, "consumer", "bind", "bob-pub",
                                          "--account", "b b").returncode, 0)
        for name, login in (("bob-pub", "bob"), ("bob-priv", "bob"),
                            ("alice-priv", "alice")):
            self.ok(node, "consumer", "bind", name, "--account", login)
        shown = text(self.ok(node, "consumer", "show"))
        self.assertIn("consumer bob-pub account bob", shown)
        self.assertIn("consumer alice-priv account alice", shown)
        self.assertNotIn("pending", shown)
        self.assertNotIn("redeemed", shown)

        self.post_all(node)

        # The refusals: wrong password, the plain poll of a bound consumer,
        # the bound poll of the unbound one, bob's private consumer.
        self.assertEqual(self.poll(node, "bob-pub", "wrong")[0], 1)
        self.assertEqual(self.poll(node, "bob-pub")[0], 1)
        self.assertEqual(self.poll(node, "operator", "bob")[0], 1)
        self.assertEqual(self.poll(node, "bob-priv", "bob")[0], 1)
        self.assertEqual(self.poll(node, "alice-priv", "bob")[0], 1)

        # bob-pub: one event, acked; then an owner restart; the rest.
        code, tag, cursor = self.poll(node, "bob-pub", "bob")
        self.assertEqual((code, tag), (0, "pub1"))
        self.assertEqual(self.ack(node, cursor, "wrong"), 1)
        self.assertEqual(self.ack(node, cursor), 1)
        self.assertEqual(self.ack(node, cursor, "bob"), 0)
        code, tag, _ = self.poll(node, "alice-priv", "alice")
        self.assertEqual((code, tag), (0, "secret1"))  # served, not acked
        node.stop()
        node.start()
        self.assertEqual(self.drain(node, "bob-pub", "bob"), ["pub2", "cross"])
        self.assertEqual(self.drain(node, "alice-priv", "alice"),
                         ["secret1", "secret2", "cross"])
        # The unbound consumer is the operator's, unchanged: everything in
        # its group.
        self.assertEqual(self.drain(node, "operator", None),
                         ["secret1", "secret2", "cross"])
        # bob-priv was refused throughout; widening bob's rule serves it
        # from where it stopped: nothing was skipped.
        self.assertEqual(self.poll(node, "bob-priv", "bob")[0], 1)
        self.ok(node, "account", "access", "bob", "--read", "*", "--post", "*")
        self.assertEqual(self.drain(node, "bob-priv", "bob"),
                         ["secret1", "secret2", "cross"])
        # Unbind returns a consumer to the operator's plain form.
        self.ok(node, "consumer", "unbind", "bob-pub")
        self.assertEqual(self.poll(node, "bob-pub", "bob")[0], 1)
        code, tag, _ = self.poll(node, "bob-pub")
        self.assertEqual((code, tag), (0, None))
        node.stop()

    def test_two_accounts_two_bound_consumers(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.scenario(image)


if __name__ == "__main__":
    unittest.main()
