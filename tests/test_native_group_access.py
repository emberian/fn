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
import re
import unittest

from tests.native_harness import ROOT, Client, Node, article, client_context, native_image

IMAGES = [("production", native_image("FN_NATIVE_HOST")),
          ("developer", native_image("FN_NATIVE_DEVELOPER_HOST"))]
READY = all(p.is_file() and os.access(p, os.X_OK) for _, p in IMAGES)


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


@unittest.skipUnless(READY, "the production and developer images are required")
class NativeGroupAccessTests(unittest.TestCase):
    def node(self, image):
        return Node(self, image).use_tls()

    def operator(self, node, *words):
        result = node.operator(*words, timeout=240)
        print("NATIVE-ACCESS", " ".join(words[:3]), "->", result.returncode)
        return result

    def ok(self, node, *words):
        result = self.operator(node, *words)
        self.assertEqual(result.returncode, 0, text(result))
        return result

    def tls(self, node):
        client = Client(node.tls_port, implicit_tls=client_context(), greeting=None)
        self.addCleanup(client.close, quit=False)
        return client

    @staticmethod
    def line(client, command):
        return client.command(command).decode("ascii", "replace").rstrip("\r\n")

    def multi(self, client, command):
        status, body = client.multiline(command)
        status = status.decode("ascii", "replace").rstrip("\r\n")
        rows = body.decode("ascii", "replace").split("\r\n")[:-1] if status[:1] == "2" else []
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

    def post(self, client, groups, tag):
        first, final = client.post(article(
            "<{}@example.invalid>".format(tag), groups=groups, subject=tag,
            sender=tag + "@example.invalid", date=None))
        if final is None:
            return first.decode("ascii", "replace").rstrip("\r\n")
        return final.decode("ascii", "replace").rstrip("\r\n")

    def listed(self, stream, command):
        status, rows = self.multi(stream, command)
        self.assertTrue(status.startswith("215"), status)
        return [row.split()[0] for row in rows if row.strip()]

    def scenario(self, image):
        node = self.node(image)
        self.ok(node, "init", "local.general")
        for group in ("fn.public", "fn.private.x"):
            self.ok(node, "group", "create", group)
        node.start()
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
                node.stop()
                node.start()
        node.stop()

    def test_two_accounts_one_private_group(self):
        for name, image in IMAGES:
            with self.subTest(image=name):
                self.scenario(image)


if __name__ == "__main__":
    unittest.main()
