"""The offline store-profile upgrade (M5), through both entries.

`operator CONFIG store upgrade-profile PROFILE` and the developer
`store ROOT upgrade-profile PROFILE` open the store as `recover` does (the
exclusive writer lock, the old profile's bounds, full replay), ask ACL2's
`fn-profile-upgrade-verdict` (books/store-profile-upgrade.lisp) and write the
frame it returns through `fnn-upgrade-profile-write`, the byte program
`fn-bs-profile-program` (books/byte-store-profile-program.lisp).

The witnesses:

* a development store with three articles is upgraded to scale; `status`
  then reads budget 4096 with 3 used, and the owner accepts the next POST;
* the same profile, a downgrade and a locked store are refused and write
  nothing;
* at every cut of the program (tests/campaign/native_cuts.py PROFILE_CUTS),
  SIGKILL or EIO, through either entry, the store reopens with the old or the
  new profile frame, byte for byte, and its budget is 128 or 4096 as the
  cut's candidate column says; a following `recover` and a retried upgrade
  end at scale.
"""
import fcntl
import hashlib
import os
from pathlib import Path
import signal
import subprocess
import unittest

from tests.campaign import native_cuts
from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
IMAGE = verbs.IMAGE
DEVELOPER = verbs.DEVELOPER
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN = verbs.EXIT_OK, verbs.EXIT_REFUSED, verbs.EXIT_UNCERTAIN

# The two metadata frames `init` writes (planning/evidence/m5-capacity-2026-09-24.md).
DEVELOPMENT_FRAME = "dcbd90d34e72bd7271891f7ada6fccd39a03dd66e76111f07e4f25dab189e9fc"
SCALE_FRAME = "bf6e6df94c6dbf75704366a84ad09229f42f80cc2e10a8dfccc432e4c93ba1b9"
BUDGET = {"old": {128}, "new": {4096}, "either": {128, 4096}}
FRAME = {128: DEVELOPMENT_FRAME, 4096: SCALE_FRAME}


class ProfileUpgradeSourceTests(unittest.TestCase):
    def test_the_verb_is_acl2s_and_the_host_writes_the_program(self):
        model = (ROOT / "books" / "native-operator.lisp").read_text(encoding="ascii")
        host = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        store_host = (ROOT / "host" / "store-host.lisp").read_text(encoding="ascii")
        self.assertIn("(defun fn-nop-parse-store (words config)", model)
        self.assertIn('"store") :upgrade-profile)', model)
        self.assertIn("(fn-profile-upgrade-verdict current target)", store_host)
        command = native_cuts.host_function(host, "fnn-command-upgrade-profile")
        self.assertIn("(fnn-open-live-store root t (fnn-profile-test-fault))", command)
        self.assertIn("'fn-store-profile-upgrade-verdict", command)
        self.assertIn("(fnn-upgrade-profile-write store", command)
        # The replay bound is ACL2's, not a host comparison.
        records = native_cuts.host_function(host, "fnn-durable-records")
        self.assertIn("'fn-store-profile-replay-within-bound", records)
        self.assertNotIn("fnn-config-max-recovery", host)
        native_cuts.verify_profile_cut_map()


class ProfileUpgradeFixture(verbs.NativeOperatorVerbFixture):
    image = IMAGE

    def setUp(self):
        if not verbs.executable(self.image):
            self.skipTest("{} is required".format(self.image))
        super().setUp()
        self.control = self.root / "control.sock"
        self.port = verbs.free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")

    start_owner = verbs.NativeOperatorUncertainOutcomeTests.start_owner
    reap = verbs.NativeOperatorUncertainOutcomeTests.reap
    headroom = verbs.NativeOperatorCapacityTests.headroom
    post_many = verbs.NativeOperatorCapacityTests.post_many
    stop = verbs.NativeOperatorCapacityTests.stop

    def op(self, *words, env=None):
        return self.operator(*words, image=self.image, env=env)

    def store_cli(self, *words, env=None):
        return subprocess.run(
            [str(self.image), "--fn", "store", str(self.store), *words],
            cwd=ROOT, env=env or verbs.environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)

    def upgrade(self, entry, profile, env=None):
        if entry == "operator":
            return self.op("store", "upgrade-profile", profile, env=env)
        return self.store_cli("upgrade-profile", profile, env=env)

    def frame(self):
        return hashlib.sha256((self.store / "config.json").read_bytes()).hexdigest()

    def init(self):
        created = self.op("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertEqual(self.frame(), DEVELOPMENT_FRAME)


class ProfileUpgradeTests(ProfileUpgradeFixture):
    def test_three_articles_then_scale_then_the_next_post(self):
        self.init()
        owner = self.start_owner(self.image)
        ids = ["<up-{}@example.invalid>".format(n) for n in range(4)]
        self.assertEqual(self.post_many(ids[:3]), ["240 article received OK"] * 3)
        self.stop(owner)
        before = self.headroom()
        self.assertEqual((before["transactions-used"], before["transactions-budget"]), (3, 128))

        upgraded = self.upgrade("operator", "scale")
        self.assertEqual(upgraded.returncode, EXIT_OK, upgraded.stderr.decode())
        self.assertIn(b"upgraded profile=scale transactions-used=3 "
                      b"transactions-budget=4096 previous-budget=128", upgraded.stdout)
        self.assertEqual(self.frame(), SCALE_FRAME)
        after = self.headroom()
        self.assertEqual((after["transactions-used"], after["transactions-budget"]), (3, 4096))
        self.assertEqual(after["charge-reserved"], before["charge-reserved"])

        owner = self.start_owner(self.image)
        self.assertEqual(self.post_many(ids[3:]), ["240 article received OK"])
        self.stop(owner)
        final = self.headroom()
        self.assertEqual((final["transactions-used"], final["transactions-budget"]), (4, 4096))

    def test_same_profile_and_downgrade_write_nothing(self):
        self.init()
        for entry in ("operator", "store"):
            same = self.upgrade(entry, "development")
            self.assertEqual(same.returncode, EXIT_REFUSED, same.stderr.decode())
            self.assertIn(b"same-profile", same.stderr)
            self.assertEqual(self.frame(), DEVELOPMENT_FRAME)
        self.assertEqual(self.upgrade("store", "scale").returncode, EXIT_OK)
        for entry in ("operator", "store"):
            down = self.upgrade(entry, "development")
            self.assertEqual(down.returncode, EXIT_REFUSED, down.stderr.decode())
            self.assertIn(b"not-an-upgrade", down.stderr)
            again = self.upgrade(entry, "scale")
            self.assertEqual(again.returncode, EXIT_REFUSED, again.stderr.decode())
            self.assertIn(b"same-profile", again.stderr)
            self.assertEqual(self.frame(), SCALE_FRAME)
        # An unknown word is usage at the operator and a refusal at the store.
        self.assertEqual(self.op("store", "upgrade-profile", "huge").returncode,
                         verbs.EXIT_USAGE)
        unknown = self.store_cli("upgrade-profile", "huge")
        self.assertEqual(unknown.returncode, EXIT_REFUSED, unknown.stderr.decode())
        self.assertIn(b"unknown-profile", unknown.stderr)

    def test_a_running_owner_refuses_the_upgrade(self):
        self.init()
        lock = os.open(str(self.store / "writer.lock"), os.O_RDWR)
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            refused = self.upgrade("operator", "scale")
            self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
            self.assertIn(b"already locked", refused.stderr)
        finally:
            os.close(lock)
        self.assertEqual(self.frame(), DEVELOPMENT_FRAME)
        owner = self.start_owner(self.image)
        refused = self.upgrade("store", "scale")
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"already locked", refused.stderr)
        self.stop(owner)
        self.assertEqual(self.frame(), DEVELOPMENT_FRAME)


class ProfileUpgradeCutTests(ProfileUpgradeFixture):
    """Every PROFILE_CUTS cut, SIGKILL and EIO, through both entries."""
    image = DEVELOPER

    def run_cut(self, cut, action, entry):
        self.init()
        env = verbs.environment()
        env["FN_NATIVE_PROFILE_FAULT"] = "{}:{}".format(cut.name, action)
        died = self.upgrade(entry, "scale", env=env)
        if action == "kill":
            self.assertEqual(died.returncode, -signal.SIGKILL, died.stderr.decode())
        else:
            expected = EXIT_REFUSED if cut.candidate == "old" else EXIT_UNCERTAIN
            self.assertEqual(died.returncode, expected, died.stderr.decode())
        # The next process reads the old frame or the new one, byte for byte.
        room = self.headroom()
        self.assertEqual(room["transactions-used"], 0)
        self.assertIn(room["transactions-budget"], BUDGET[cut.candidate])
        self.assertEqual(self.frame(), FRAME[room["transactions-budget"]])
        recovered = self.op("recover")
        self.assertEqual(recovered.returncode, EXIT_OK, recovered.stderr.decode())
        self.assertEqual(list((self.store / "staging").iterdir()), [])
        retried = self.upgrade(entry, "scale")
        if room["transactions-budget"] == 4096:
            self.assertEqual(retried.returncode, EXIT_REFUSED, retried.stderr.decode())
            self.assertIn(b"same-profile", retried.stderr)
        else:
            self.assertEqual(retried.returncode, EXIT_OK, retried.stderr.decode())
        self.assertEqual(self.headroom()["transactions-budget"], 4096)
        self.assertEqual(self.frame(), SCALE_FRAME)
        return room["transactions-budget"]

    def test_every_cut_reopens_with_the_old_or_the_new_profile(self):
        seen = {}
        for cut in native_cuts.PROFILE_CUTS:
            for action in ("kill", "eio"):
                for entry in ("operator", "store"):
                    with self.subTest(cut=cut.name, action=action, entry=entry):
                        # A fresh store per case: the fixture's directory.
                        if self.store.exists():
                            subprocess.run(["rm", "-rf", str(self.store)], check=True)
                        seen[(cut.name, action, entry)] = self.run_cut(cut, action, entry)
        print("profile cuts:", sorted(seen.items()))


if __name__ == "__main__":
    unittest.main()
