"""Opt-in native witnesses for the operator surface's verdicts (PKT-095,
PKT-102, PKT-103; planning/evidence/operator-verdicts-2026-09-25.md).

- A refused POST leaves one service-log line on either path, rendered by
  books/owner-log.lisp (fn-olog-served-refusal-lines for the served 441,
  fn-olog-control-refusal-line for the operator's article).
- `principal set-password` answers from the store's writer lock, through
  ACL2's fn-native-auth-admin-effect-word: `effective-at-next-start' with no
  owner, `applied' while one runs: the running owner reloads the credential
  file (host/native/auth.lisp fnn-native-auth-reload-config, control request
  14), so the next login takes the new password and the old one is refused,
  with no restart (lane friend-path-2).
- The developer `store ROOT init' reads the operator's profile flags
  (fn-nop-developer-init) and refuses a flag-shaped group word.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest tests.test_native_operator_verdicts
"""

import unittest

import tests.test_native_control_filing as base
from tests.native_harness import EXIT, native_image, scratch
from tests.test_native_control_filing import READY, article

IMAGE = native_image("FN_NATIVE_HOST")

SECRET = b"correct-horse-battery\ncorrect-horse-battery\n"
SECOND = b"staple-battery-horse\nstaple-battery-horse\n"


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativeOperatorVerdictTests(base.NativeControlFilingTests):
    # The parent's cases are not re-run here.
    test_served_post = None
    test_transit_ihave = None
    test_signed_author = None

    def set_password(self, node, secret=SECRET):
        result = node.operator("principal", "set-password", "alice", "--posting",
                               input=secret, timeout=600, expect=EXIT.OK)
        return result.stderr.decode("utf-8", "replace")

    def test_refused_posts_are_logged_on_both_paths(self):
        node = self.initialize("refusals", ["fn.test"])
        node.start()
        served_id = "<ov-served-refused@example.invalid>"
        payload = article(served_id, "x").replace(b"Newsgroups: fn.test",
                                                  b"Newsgroups: not.carried")
        reply = self.post(node, payload)
        control_id = "<ov-control-refused@example.invalid>"
        source = node.root / "control-article"
        source.write_bytes(article(control_id, "y").replace(b"Newsgroups: fn.test",
                                                            b"Newsgroups: not.carried"))
        refused = node.operator("post", "--message-id", control_id, "--payload", source,
                                "--group", "not.carried")
        accepted = self.post(node, article("<ov-served-ok@example.invalid>", "z"))
        log = self.stop(node)
        lines = [line for line in log.splitlines() if " post " in line]
        print("NATIVE-REFUSAL-LOG " + repr(lines) + " control-exit="
              + str(refused.returncode) + " " + refused.stderr.decode().strip())
        self.assertEqual(reply, b"441 posting failed; a named newsgroup is not carried here\r\n")
        self.assertNotEqual(refused.returncode, 0, refused)
        self.assertTrue(accepted.startswith(b"240"), accepted)
        self.assertTrue(any(line.startswith("refused post path=served connection=")
                            and "reason=unknown-group" in line for line in lines), lines)
        self.assertTrue(any(line.startswith("refused post path=control message-id="
                                            + control_id)
                            and " reason=" in line for line in lines), lines)
        self.assertTrue(any(line.startswith("accepted post path=served")
                            for line in lines), lines)

    def login(self, node, secret):
        """AUTHINFO USER alice / PASS the secret's first line on a new connection."""
        replies = self.session(node, [b"AUTHINFO USER alice\r\n",
                                      b"AUTHINFO PASS " + secret.split(b"\n")[0] + b"\r\n"])
        return replies[-1][:3]

    def test_set_password_answers_from_the_owner(self):
        node = self.initialize("principal", ["fn.test"])
        offline = self.set_password(node)
        node.start()
        before = self.login(node, SECRET)
        online = self.set_password(node, SECOND)
        new_login = self.login(node, SECOND)
        old_login = self.login(node, SECRET)
        self.stop(node)
        print("NATIVE-PRINCIPAL offline={!r} online={!r} logins before={!r} new={!r} "
              "old={!r}".format(offline.strip(), online.strip(), before, new_login,
                                old_login))
        self.assertIn("accepted operator principal set-password effective-at-next-start",
                      offline)
        self.assertIn("accepted operator principal set-password applied", online)
        self.assertNotIn("restart-required", online)
        # The password the node started with logs in; after the live change the
        # new one does and the old one is refused, with no restart between.
        self.assertEqual(before, b"281")
        self.assertEqual(new_login, b"281")
        self.assertEqual(old_login, b"481")

    def test_developer_init_reads_profile_flags_and_refuses_flag_groups(self):
        store = scratch(self) / "dev-store"
        bad = self.command([IMAGE, "--fn", "store", store, "init", "--no-such-flag",
                            "fn.test"], expected=5)
        self.assertFalse(store.exists() and any(store.iterdir()), bad)
        self.command([IMAGE, "--fn", "store", store, "init",
                      "--profile", "default", "--max-article-octets", "65536",
                      "fn.test"])
        status = self.command([IMAGE, "--fn", "store", store, "status"])
        text = (status.stdout + status.stderr).decode("utf-8", "replace")
        print("NATIVE-DEV-INIT refused={!r} status={!r}".format(
            bad.stderr.decode().strip(), text.strip()))
        self.assertIn(b"flag-word-as-group", bad.stderr)
        self.assertIn("max-article-octets=65536", text)
        self.assertNotIn("--max-article-octets", text)


if __name__ == "__main__":
    unittest.main()
