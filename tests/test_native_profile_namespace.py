"""D27, PRF-102: configuration generations and credentials are the operator's.

On a real image: a format-8 store made with the pre-D27 credential cap (128)
and a small configuration-generation bound refuses the next generation and
the 129th login by name; `store upgrade-profile` raises both fields,
`status` prints them, the refused publication and the 129th login then
succeed, the owner loads the 129-credential file, and a shrink is refused
naming the field.  The ACL2 side is books/native-config-observation.lisp,
books/native-admin.lisp, books/native-auth-profile.lisp,
books/native-auth-admin.lisp and books/store-profile-namespace.lisp.
"""
import subprocess
import unittest

from tests import test_native_profile_upgrade as upgrade
from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
EXIT_OK, EXIT_REFUSED = verbs.EXIT_OK, verbs.EXIT_REFUSED

PRINCIPAL = "0" * 64
SALT = "0" * 32
DIGEST = "1" * 64


def credentials_file(count):
    """COUNT canonical credential tables, u1 .. uCOUNT."""
    lines = ["# fn AUTHINFO credentials, written by the PRF-102 native test"]
    for k in range(1, count + 1):
        lines += ['[login."u{}"]'.format(k),
                  'principal = "{}"'.format(PRINCIPAL),
                  'salt = "{}"'.format(SALT),
                  'digest = "{}"'.format(DIGEST),
                  "posting = false", ""]
    return ("\n".join(lines) + "\n").encode("ascii")


class NativeProfileNamespaceTests(upgrade.ProfileUpgradeFixture):
    profile_line = upgrade.OperatorFieldsTests.profile_line

    def set_password(self, login):
        return subprocess.run(
            [str(self.image), "--fn", "operator", str(self.config), "principal",
             "set-password", login, "--no-posting"], cwd=ROOT,
            env=verbs.environment(), input=b"a-password\na-password\n",
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180,
            check=False)

    def test_the_operator_raises_credentials_and_generations(self):
        created = self.op("init", "--max-credentials", "128",
                          "--max-config-generations", "3", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        profile = self.profile_line()
        self.assertEqual(profile["max-credentials"], 128)
        self.assertEqual(profile["max-config-generations"], 3)

        # Generation 2 is within the bound.  Generation 3, the last, is the
        # content release's (PRF-138, books/store-capacity-config.lisp): a
        # group is refused it by name, `retention set' is admitted there,
        # and generation 4 is refused to every record.
        second = self.op("group", "create", "fn.two")
        self.assertEqual(second.returncode, EXIT_OK, second.stderr.decode())
        third = self.op("group", "create", "fn.three")
        self.assertEqual(third.returncode, EXIT_REFUSED, third.stderr.decode())
        self.assertIn("max-config-generations",
                      (third.stdout + third.stderr).decode().lower())
        release = self.op("retention", "set", "released-by-all-holders")
        self.assertEqual(release.returncode, EXIT_OK, release.stderr.decode())
        again = self.op("retention", "set", "keep-forever")
        self.assertEqual(again.returncode, EXIT_REFUSED, again.stderr.decode())
        self.assertIn("max-config-generations",
                      (again.stdout + again.stderr).decode().lower())
        # The store still opens: the writer never outgrew the listing bound.
        self.assertEqual(self.op("status").returncode, EXIT_OK)

        # 128 credentials, the pre-D27 cap: the 129th login is refused.
        (self.store / "auth.toml").write_bytes(credentials_file(128))
        refused = self.set_password("u129")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn("too-many-credentials",
                      (refused.stdout + refused.stderr).decode().lower())

        raised = self.op("store", "upgrade-profile", "--max-credentials", "200",
                         "--max-config-generations", "9000")
        self.assertEqual(raised.returncode, EXIT_OK, raised.stderr.decode())
        profile = self.profile_line()
        self.assertEqual(profile["max-credentials"], 200)
        self.assertEqual(profile["max-config-generations"], 9000)

        # Above the old cap: the 129th login, and the third generation.
        accepted = self.set_password("u129")
        self.assertEqual(accepted.returncode, EXIT_OK, accepted.stderr.decode())
        listed = self.op("principal", "list")
        self.assertEqual(listed.returncode, EXIT_OK, listed.stderr.decode())
        self.assertEqual(len(listed.stdout.decode().strip().splitlines()), 129)
        third = self.op("group", "create", "fn.three")
        self.assertEqual(third.returncode, EXIT_OK, third.stderr.decode())

        # The owner installs the 129-credential file at startup.
        owner = self.start_owner(self.image)
        self.stop(owner)

        shrunk = self.op("store", "upgrade-profile", "--max-credentials", "150")
        self.assertEqual(shrunk.returncode, EXIT_REFUSED, shrunk.stderr.decode())
        self.assertIn("max-credentials", (shrunk.stdout + shrunk.stderr).decode())
        self.assertEqual(self.profile_line()["max-credentials"], 200)


if __name__ == "__main__":
    unittest.main()
