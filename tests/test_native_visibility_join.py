"""Native witness for NNT-019 (SCN-060): a lost POST reply, then withdrawal.

The mandate's section 5.1 sequence on a developer image: a POST of a stable
source and Message-ID whose reply is lost (FN_NATIVE_POST_FAULT
`log-fenced:kill`: on the record log, the cut after the batch's barrier and
before any member's reply -- the commit durable, the reply never written;
the member's finish cuts precede the append in a served commit quantum, so
at them the record is not yet durable, tests/campaign/native_cuts.py
POST_LOG_CUTS), an authorized cancel that withdraws the target, a
reconnect whose lookup answers 430, and the reconciliation: the client
re-sends the SAME article, the node answers `441 ... already stored here`
(books/visibility-join.lisp `fn-vj-a-completion-keeps-a-held-message-id-
answered` over host/native/owner.lisp `fnn-owner-attempt`), no transaction
and no article number is allocated, and the client reports accepted with the
original outcome kept, through tools/fn_client.py (`post --draft`,
`reconcile`).

The authorization case: on a protected node the poster's login loses its
posting permission after the lost reply; the re-send is refused by a policy
that is not the Store's answer, and the client says `unresolved` (exit 4)
while the article is still served.

The reclaimed-tombstone case has no native run: no host verb reclaims an
article on dev (planning/now.md, reclamation); its theorem is
`fn-vj-reclamation-keeps-a-held-message-id-answered`.

Run: FN_NATIVE_HOST=<developer launcher> FN_TEST_OPENSSL=<openssl 3.5>
     python3 -m unittest -v tests.test_native_visibility_join
"""

import json
import os
import sys
import unittest

from tests import native_log_observation
from tests.native_harness import (
    EXIT_OK, ROOT, Client, Node, environment, native_image, requires, run, scratch)

# A developer image: the lost reply is FN_NATIVE_POST_FAULT, a developer
# selector a production image refuses to start with (tools/native_env.py:
# FN_NATIVE_HOST always names the production image).
IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
FAULT = "log-fenced:kill"
CLIENT = [sys.executable, str(ROOT / "tools" / "fn_client.py")]
PRINCIPAL = bytes([85]) * 32


def cancel_article(message_id, target):
    return ("From: moderator@example.invalid\r\nNewsgroups: fn.test\r\n"
            "Subject: cmsg cancel {t}\r\nDate: Fri, 25 Sep 2026 03:00:00 +0000\r\n"
            "Message-ID: {m}\r\nControl: cancel {t}\r\n\r\nwithdrawn\r\n").format(
                m=message_id, t=target).encode("ascii")


@requires(IMAGE)
class NativeVisibilityJoinTests(unittest.TestCase):
    def setUp(self):
        self.base = scratch(self, "fn-native-vj-")
        self.env = environment()
        self.witness = {}

    # ------------------------------------------------------------ harness

    def command(self, arguments, expected=EXIT_OK, env=None, stdin=None):
        result = run(arguments, env=env or self.env, input=stdin, timeout=300)
        if expected is not None:
            self.assertEqual(result.returncode, expected, result)
        return result

    def initialize(self, name, protected=False):
        """A node whose store `store init` made; PROTECTED: STARTTLS with a
        fresh certificate for 127.0.0.1 and required, protected-only login."""
        node = Node(self, IMAGE, root=self.base / name, name=name)
        self.command([IMAGE, "--fn", "store", node.store_path, "init", "fn.test",
                      "control.cancel"])
        if protected:
            cert, key = node.root / "cert.pem", node.root / "key.pem"
            run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", key,
                 "-out", cert, "-sha256", "-days", "1", "-nodes", "-subj", "/CN=localhost",
                 "-addext", "subjectAltName=IP:127.0.0.1"], timeout=60).check_returncode()
            node.cert = cert
            node.write_config(extra=(
                'tls_cert = "{}"\ntls_key = "{}"\n'
                '[auth]\nrequired = true\nprotected_only = true\npath = "{}"\n').format(
                    cert, key, node.root / "credentials.toml"))
        return node

    def start(self, node, fault=False):
        node.start(ready=b"LISTENING ", env={"FN_NATIVE_POST_FAULT": FAULT} if fault else None)

    def killed(self, node):
        """The owner's exit after its fault cut killed it."""
        rc = node.process.wait(timeout=120)
        node.process.finish()
        return rc

    def stop(self, node):
        node.stop(expect=None)

    def transactions(self, node):
        # The committed history read by the image.
        return native_log_observation.committed_history(IMAGE, node.store_path,
                                                        env=self.env, cwd=ROOT)

    def first_line(self, node, command):
        with Client(node.port, timeout=30, greeting=(b"200",)) as client:
            client.send(command)
            return client.line().decode().strip()

    def client(self, node, *arguments, stdin=None, credentials=None):
        connection = ["--node", "127.0.0.1:%d" % node.port, "--json"]
        connection += (["--cafile", str(node.cert), "--credentials", str(credentials)]
                       if credentials else ["--plain"])
        result = self.command(CLIENT + list(arguments[:1]) + connection + list(arguments[1:]),
                              expected=None, stdin=stdin)
        document = json.loads(result.stdout.decode()) if result.stdout.strip() else {}
        return result.returncode, document

    def enroll(self, node):
        """Enroll P (generation 1) on the running node; return its key files."""
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        root = node.root
        principal, ed_public, ed_secret = (root / "principal.bin", root / "ed-public.bin",
                                           root / "ed-secret.bin")
        principal.write_bytes(PRINCIPAL)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ml_private, ml_public = root / "ml-private.pem", root / "ml-public.pem"
        self.command([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out", ml_private])
        self.command([openssl, "pkey", "-in", ml_private, "-pubout", "-out", ml_public])
        self.command([IMAGE, "--fn", "hybrid-enroll", node.control, "1", principal,
                      ed_public, ml_public])
        return principal, ed_public, ed_secret, ml_public, ml_private

    def withdraw(self, node, targets):
        """Grant P cancel over fn.test and file one signed cancel per target."""
        root = node.root
        principal, ed_public, ed_secret, ml_public, ml_private = self.enroll(node)
        self.command([IMAGE, "--fn", "operator", node.config, "control", "grant",
                      PRINCIPAL.hex(), "cancel", "fn.test"])
        for i, target in enumerate(targets):
            source = root / ("cancel-%d.eml" % i)
            source.write_bytes(cancel_article("<vj-cancel-%d@example.invalid>" % i, target))
            signed = self.command([IMAGE, "--fn", "hybrid-sign", principal, ed_public,
                                   ed_secret, ml_public, ml_private, source])
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig, ml_sig = root / ("cancel-%d.ed" % i), root / ("cancel-%d.ml" % i)
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            self.command([IMAGE, "--fn", "hybrid-author", node.control, "1", source,
                          ed_sig, ml_sig, ml_public])

    # ------------------------------------------------------------ cases

    def test_lost_reply_then_withdrawal_reconciles_to_already_stored(self):
        node = self.initialize("withdrawn")
        draft = node.root / "draft.json"
        # 1. fn_client: the POST commits and the owner dies before the reply.
        self.start(node, fault=True)
        rc, posted = self.client(node, "post", "fn.test", "--subject", "lost reply",
                                 "--draft", str(draft), stdin=b"the source kept exactly\n")
        self.assertEqual(rc, 3, posted)
        self.assertEqual(posted["outcome"], "uncertain")
        self.assertEqual(self.killed(node), -9)
        kept = json.loads(draft.read_text())
        target = kept["message_id"]
        self.assertEqual(kept["original"]["outcome"], "uncertain")
        # 2. Restart; the target is stored and served.
        self.start(node)
        served_before = {target: self.first_line(node, b"ARTICLE " + target.encode() + b"\r\n")}
        # 3. An authorized cancel withdraws it.
        self.withdraw(node, [target])
        # 4. A fresh reader: 430; the lookup is a visibility observation.
        rc_show, shown = self.client(node, "show", target)
        after_cancel = {target: self.first_line(node, b"ARTICLE " + target.encode() + b"\r\n")}
        before = self.transactions(node)
        group_before = self.first_line(node, b"GROUP fn.test\r\n")
        # 5. Reconciliation re-sends the same article: already stored.
        rc_rec, reconciled = self.client(node, "reconcile", str(draft))
        after = self.transactions(node)
        group_after = self.first_line(node, b"GROUP fn.test\r\n")
        # 6. A second reconcile is idempotent on the node too.
        rc_again, again = self.client(node, "reconcile", str(draft))
        final = json.loads(draft.read_text())
        self.stop(node)
        self.witness = {
            "fn-client-post": [rc, posted.get("outcome"), posted.get("status_lines")],
            "served-before-cancel": served_before,
            "article-after-cancel": after_cancel,
            "fn-client-show": [rc_show, shown.get("detail"), shown.get("visibility")],
            "fn-client-reconcile": [rc_rec, reconciled.get("outcome"),
                                    reconciled.get("settled"), reconciled.get("status_lines")],
            "fn-client-reconcile-again": [rc_again, again.get("outcome"), again.get("settled")],
            "transactions-before-after": [len(before), len(after)],
            "group-before-after": [group_before, group_after],
        }
        print("NATIVE-VISIBILITY-JOIN-WITNESS " + json.dumps(self.witness, sort_keys=True))
        for line in served_before.values():
            self.assertTrue(line.startswith("220"), served_before)
        for line in after_cancel.values():
            self.assertTrue(line.startswith("430"), after_cancel)
        self.assertEqual(rc_show, 1, shown)
        self.assertEqual(shown.get("visibility"), "not-visible", shown)
        self.assertEqual(rc_rec, 0, reconciled)
        self.assertEqual(reconciled["outcome"], "accepted")
        self.assertEqual(reconciled["settled"], "already-stored")
        self.assertIn("441 posting failed; this article is already stored here",
                      reconciled["status_lines"])
        self.assertEqual(rc_again, 0, again)
        self.assertEqual(again["settled"], "already-stored")
        self.assertEqual(before, after)                  # no transaction allocated
        self.assertEqual(group_before, group_after)      # no article number allocated
        self.assertEqual(final["original"]["outcome"], "uncertain")   # never rewritten
        self.assertEqual([r["settled"] for r in final["reconciliations"]],
                         ["already-stored", "already-stored"])
        self.assertEqual(final["message_id"], target)

    def test_lost_reply_then_authorization_change_is_unresolved(self):
        node = self.initialize("authorization", protected=True)
        user, secret = "vj-poster", "visibility-join-secret-3"  # FAKE-SECRET: a test fixture's password
        credentials = node.root / "login"
        credentials.write_text("%s %s\n" % (user, secret))
        credentials.chmod(0o600)
        self.command([IMAGE, "--fn", "operator", node.config, "principal", "set-password",
                      user, "--posting"], stdin="{0}\n{0}\n".format(secret).encode())
        draft = node.root / "draft.json"
        self.start(node, fault=True)
        rc, posted = self.client(node, "post", "fn.test", "--subject", "then revoked",
                                 "--draft", str(draft), stdin=b"posted while allowed\n",
                                 credentials=credentials)
        self.assertEqual(rc, 3, posted)
        self.assertEqual(self.killed(node), -9)
        target = json.loads(draft.read_text())["message_id"]
        # The authorization change: the login may no longer post.
        self.command([IMAGE, "--fn", "operator", node.config, "principal", "set-password",
                      user, "--no-posting"], stdin="{0}\n{0}\n".format(secret).encode())
        self.start(node)
        before = self.transactions(node)
        rc_rec, reconciled = self.client(node, "reconcile", str(draft),
                                         credentials=credentials)
        rc_show, shown = self.client(node, "show", target, credentials=credentials)
        after = self.transactions(node)
        self.stop(node)
        final = json.loads(draft.read_text())
        self.witness = {"post": [rc, posted.get("outcome")],
                        "reconcile": [rc_rec, reconciled.get("outcome"),
                                      reconciled.get("settled"),
                                      reconciled.get("status_lines")],
                        "show": [rc_show, (shown.get("status_lines") or [""])[-1]],
                        "transactions-before-after": [len(before), len(after)]}
        print("NATIVE-VISIBILITY-JOIN-AUTH-WITNESS " + json.dumps(self.witness, sort_keys=True))
        self.assertEqual(rc_rec, 4, reconciled)
        self.assertEqual(reconciled["outcome"], "unresolved")
        self.assertEqual(rc_show, 0, shown)     # still served: it WAS accepted
        self.assertEqual(before, after)
        self.assertEqual(final["original"]["outcome"], "uncertain")
        self.assertEqual(final["reconciliations"][-1]["settled"], "unresolved")

    def test_lost_reply_then_login_rebound_is_unresolved(self):
        """PKT-238: the lost reply, then the login is bound to another principal.

        Under `posting-policy bound-logins` the login is bound to P and posts
        an article signed by P; the owner dies after the commit is durable
        and before the reply (FN_NATIVE_POST_FAULT).  The operator re-binds
        the login to Q (`principal bind`, applied at restart).  The re-send of
        the SAME article is refused by fn-owner-login-gate
        (books/login-binding.lisp fn-lb-owner-gate; the theorem is
        fn-lb-bound-login-other-principal-is-refused) before the Store's
        decision (host/native/owner.lisp fnn-owner-attempt-served calls the
        gate first), so the node never says whether it holds the article and
        `fn_client reconcile` settles it unresolved (exit 4), as the 440 case.
        """
        import fn_client  # noqa: E402  (tools/ is on sys.path above)
        node = self.initialize("rebinding", protected=True)
        user, secret = "vj-bound", "visibility-join-secret-4"  # FAKE-SECRET: a test fixture's password
        credentials = node.root / "login"
        credentials.write_text("%s %s\n" % (user, secret))
        credentials.chmod(0o600)
        self.command([IMAGE, "--fn", "operator", node.config, "principal", "set-password",
                      user, "--posting"], stdin="{0}\n{0}\n".format(secret).encode())
        other = bytes([86]) * 32
        operator = [IMAGE, "--fn", "operator", node.config]
        self.command(operator + ["principal", "bind", user, PRINCIPAL.hex()])
        self.command(operator + ["policy", "set", "posting-policy", "bound-logins"])
        self.start(node)
        principal, ed_public, ed_secret, ml_public, ml_private = self.enroll(node)
        self.stop(node)
        # The article, signed by the login's bound principal P.
        target = "<vj-rebound@example.invalid>"
        source, carried = node.root / "rebound.eml", node.root / "rebound-carried.eml"
        source.write_bytes(
            b"From: bound@example.invalid\r\nDate: Sat, 26 Sep 2026 10:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\nSubject: posted while bound to P\r\n"
            b"Message-ID: " + target.encode() + b"\r\n\r\nsigned by the bound principal\r\n")
        self.command([IMAGE, "--fn", "hybrid-sign-carrier", principal, ed_public, ed_secret,
                      ml_public, ml_private, source, carried])
        lines = carried.read_bytes().decode("ascii").split("\r\n")
        self.assertEqual(lines[-1], "")
        lines = lines[:-1]
        self.assertTrue(any(line.startswith("FN-Authorship: ") for line in lines))
        # 1. The POST commits and the owner dies before the reply: fn_client's
        #    own `post --draft` sequence (tools/fn_client.py run), over the
        #    carrier's exact lines, the draft durable before the first byte.
        self.start(node, fault=True)
        parser = fn_client.build_parser()
        args = parser.parse_args(["post", "fn.test", "--subject", "unused", "--node",
                                  "127.0.0.1:%d" % node.port, "--cafile", str(node.cert),
                                  "--credentials", str(credentials)])
        fn_client.resolve(args, parser)
        draft = node.root / "draft.json"
        kept = {"format": fn_client.DRAFT_FORMAT,
                "node": fn_client.node_name(args.host, args.port), "group": "fn.test",
                "message_id": target, "lines": lines, "original": None,
                "reconciliations": []}
        fn_client.write_draft(draft, kept)
        posted = fn_client.exchange(args, user, secret, lines, target)
        kept["original"] = {"outcome": posted.word, "detail": posted.detail,
                            "status_lines": posted.status_lines}
        fn_client.write_draft(draft, kept)
        self.assertEqual(posted.word, "uncertain", posted.detail)
        self.assertEqual(self.killed(node), -9)
        # 2. The login is re-bound to Q; the credential file is read at start.
        self.command(operator + ["principal", "bind", user, other.hex()])
        self.start(node)
        before = self.transactions(node)
        group_before = self.secure_lines(node, b"GROUP fn.test\r\n", user, secret)[0]
        # 3. Reconciliation re-sends the same article under the same Message-ID.
        rc_rec, reconciled = self.client(node, "reconcile", str(draft),
                                         credentials=credentials)
        rc_show, shown = self.client(node, "show", target, credentials=credentials)
        hdr = self.secure_lines(node, b"HDR :fn-verified " + target.encode() + b"\r\n",
                                 user, secret)
        verdict = hdr[1] if hdr[0].startswith("225") else hdr[0]
        after = self.transactions(node)
        group_after = self.secure_lines(node, b"GROUP fn.test\r\n", user, secret)[0]
        self.stop(node)
        final = json.loads(draft.read_text())
        self.witness = {"post": [posted.word, posted.status_lines],
                        "reconcile": [rc_rec, reconciled.get("outcome"),
                                      reconciled.get("settled"),
                                      reconciled.get("status_lines")],
                        "show": [rc_show, (shown.get("status_lines") or [""])[-1]],
                        "hdr-fn-verified": verdict,
                        "transactions-before-after": [len(before), len(after)],
                        "group-before-after": [group_before, group_after]}
        print("NATIVE-VISIBILITY-JOIN-REBIND-WITNESS " + json.dumps(self.witness, sort_keys=True))
        self.assertEqual(rc_rec, 4, reconciled)
        self.assertEqual(reconciled["outcome"], "unresolved")
        self.assertEqual(reconciled["settled"], "unresolved")
        self.assertIn("441 posting failed; the login is not bound to this signing principal",
                      reconciled["status_lines"])
        self.assertNotIn("441 posting failed; this article is already stored here",
                         reconciled["status_lines"])
        self.assertEqual(rc_show, 0, shown)     # still served: it WAS accepted, under P
        self.assertEqual(verdict, "0 verified %s keyring 1" % PRINCIPAL.hex())
        self.assertNotIn(other.hex(), verdict)  # never accepted under Q
        self.assertEqual(before, after)         # the Store decided nothing new
        self.assertEqual(group_before, group_after)
        self.assertEqual(final["original"]["outcome"], "uncertain")
        self.assertEqual(final["reconciliations"][-1]["settled"], "unresolved")

    def secure_lines(self, node, command, user, secret):
        """COMMAND over STARTTLS and AUTHINFO (the protected listener serves
        nothing before both): its status line, then any multi-line body."""
        import ssl
        context = ssl.create_default_context(cafile=str(node.cert))
        with Client(node.port, timeout=30) as client:
            self.assertTrue(client.starttls(context).startswith(b"382"))
            self.assertTrue(client.command(b"AUTHINFO USER " + user.encode()).startswith(b"381"))
            self.assertTrue(client.command(b"AUTHINFO PASS " + secret.encode()).startswith(b"281"))
            client.send(command)
            lines = [client.line().decode().strip()]
            if lines[0][:3] in ("225", "215", "220", "221", "224"):
                while True:
                    line = client.line().decode().strip()
                    if line == ".":
                        break
                    lines.append(line)
            return lines

if __name__ == "__main__":
    unittest.main()
