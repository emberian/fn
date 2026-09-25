"""Opt-in native witnesses for the operator surface's verdicts (PKT-095,
PKT-102, PKT-103; planning/evidence/operator-verdicts-2026-09-25.md).

- A refused POST leaves one service-log line on either path, rendered by
  books/owner-log.lisp (fn-olog-served-refusal-lines for the served 441,
  fn-olog-control-refusal-line for the operator's article).
- `principal set-password` answers from the store's writer lock, through
  ACL2's fn-native-auth-admin-effect-word: `effective-at-next-start' with no
  owner, `restart-required' while one runs.
- The developer `store ROOT init' reads the operator's profile flags
  (fn-nop-developer-init) and refuses a flag-shaped group word.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest tests.test_native_operator_verdicts
"""

import subprocess
import unittest

import tests.test_native_control_filing as base
from tests.test_native_control_filing import IMAGE, READY, ROOT, article

SECRET = b"correct-horse-battery\ncorrect-horse-battery\n"


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativeOperatorVerdictTests(base.NativeControlFilingTests):
    # The parent's cases are not re-run here.
    test_served_post = None
    test_transit_ihave = None
    test_signed_author = None

    def set_password(self, node):
        result = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "principal",
             "set-password", "alice", "--posting"],
            cwd=ROOT, env=self.env, input=SECRET, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=600, check=False)
        self.assertEqual(result.returncode, 0, result)
        return result.stderr.decode("utf-8", "replace")

    def test_refused_posts_are_logged_on_both_paths(self):
        node = self.initialize("refusals", ["fn.test"])
        self.start(node)
        served_id = "<ov-served-refused@example.invalid>"
        payload = article(served_id, "x").replace(b"Newsgroups: fn.test",
                                                  b"Newsgroups: not.carried")
        reply = self.post(node, payload)
        control_id = "<ov-control-refused@example.invalid>"
        source = node["root"] / "control-article"
        source.write_bytes(article(control_id, "y").replace(b"Newsgroups: fn.test",
                                                            b"Newsgroups: not.carried"))
        refused = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "post",
             "--message-id", control_id, "--payload", str(source),
             "--group", "not.carried"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=180, check=False)
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

    def test_set_password_answers_from_the_owner(self):
        node = self.initialize("principal", ["fn.test"])
        offline = self.set_password(node)
        self.start(node)
        online = self.set_password(node)
        self.stop(node)
        print("NATIVE-PRINCIPAL offline={!r} online={!r}".format(offline.strip(),
                                                                 online.strip()))
        self.assertIn("accepted operator principal set-password effective-at-next-start",
                      offline)
        self.assertIn("accepted operator principal set-password restart-required", online)

    def test_developer_init_reads_profile_flags_and_refuses_flag_groups(self):
        store = self.base / "dev-store"
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

    def operator(self, node, *words, expected=0):
        return self.command([IMAGE, "--fn", "operator", node["config"], *words],
                            expected=expected)

    def test_needs_upgrade_and_rollback_check(self):
        """PKT-099: `store needs-upgrade' is the no-argument upgrade's own
        verdict (fn-profile-needs-upgrade-verdict); `store rollback-check'
        is fn-profile-rollback-verdict over the kept config.json and the
        committed transaction lengths.  With FN_OLD_NATIVE_HOST (a format-7
        image), the store starts at format 7."""
        import os
        import shutil
        old_image = os.environ.get("FN_OLD_NATIVE_HOST")
        node = self.initialize("upgrade", ["fn.test"])
        if old_image:
            shutil.rmtree(node["root"] / "store")
            self.command([old_image, "--fn", "store", node["root"] / "store", "init",
                          "fn.test"])
        before = self.operator(node, "store", "needs-upgrade")
        kept = node["root"] / "config.json.kept"
        shutil.copy2(node["root"] / "store" / "config.json", kept)
        self.start(node)
        self.assertTrue(self.post(node, article("<ov-upgrade@example.invalid>", "u"))
                        .startswith(b"240"))
        self.stop(node)
        upgraded = self.operator(node, "store", "upgrade-profile",
                                 expected=0 if old_image else 1)
        after = self.operator(node, "store", "needs-upgrade")
        sound = self.operator(node, "store", "rollback-check", kept)
        garbage = node["root"] / "garbage.json"
        garbage.write_bytes(b"not a profile")
        refused = self.operator(node, "store", "rollback-check", garbage, expected=1)
        print("NATIVE-UPGRADE " + repr([x.stdout.decode().strip() for x in
                                        (before, upgraded, after, sound, refused)]))
        self.assertEqual(before.stdout.strip(),
                         b"needs-upgrade" if old_image else b"current")
        self.assertEqual(after.stdout.strip(), b"current")
        self.assertTrue(sound.stdout.startswith(b"rollback sound transactions="), sound)
        self.assertIn(b"rollback refused invalid-rollback-profile", refused.stdout)


if __name__ == "__main__":
    unittest.main()
