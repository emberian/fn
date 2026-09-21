"""Saved-image witnesses for ACL2-owned native administrative configuration.

The test talks only to the native image's public `operator CONFIG` entry (and
the existing read-only `store config` diagnostic).  Python is test harness
plumbing here; it neither parses fn.toml nor builds configuration records.
"""

import os
from pathlib import Path
import select
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeAdminTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-admin-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.store = self.base / "store"
        self.config = self.base / "fn.toml"
        self.payload = self.base / "article"
        self.payload.write_bytes(b"native admin retained article\r\n")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.native("store", self.store, "init", "fn.letters")
        self.config.write_text('[store]\npath = "{}"\n'.format(self.store),
                               encoding="ascii")

    def native(self, *args, expected=0, env=None, timeout=60):
        result = subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
            env=env or self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, check=False)
        self.assertEqual(result.returncode, expected,
                         "native {} returned {}\nstdout={}\nstderr={}".format(
                             args, result.returncode, result.stdout.decode("utf-8", "replace"),
                             result.stderr.decode("utf-8", "replace")))
        return result

    def operator(self, *words, **kwargs):
        return self.native("operator", self.config, *words, **kwargs)

    def config_report(self):
        return self.native("store", self.store, "config").stdout.decode("ascii")

    def start_owner(self):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "owner", "run", str(self.store), "0", "0", "8"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        ready = select.select([process.stdout], [], [], 60)[0]
        self.assertTrue(ready, "native owner did not announce a port")
        line = process.stdout.readline()
        if not line.startswith(b"LISTENING "):
            self.fail("native owner failed: {} {}".format(
                line, process.stderr.read().decode("utf-8", "replace")))
        self.addCleanup(self.stop_owner, process)
        return process

    @staticmethod
    def stop_owner(process):
        if process.poll() is None:
            process.terminate()
            process.wait(timeout=15)
        process.stdout.close()
        process.stderr.close()

    def test_create_capacity_retire_reopen_preserves_history(self):
        created = self.operator("group", "create", "fn.admin")
        self.assertIn(b"configured generation=2 record=00000002.cfg verification=verified",
                      created.stdout)
        capacity = self.operator("capacity", "2048")
        self.assertIn(b"configured generation=3 record=00000003.cfg verification=verified",
                      capacity.stdout)

        message_id = "<native-admin-retained@example.invalid>"
        self.native("store", self.store, "post", message_id, self.payload,
                    "-", "-", "fn.admin")
        retired = self.operator("group", "retire", "fn.admin")
        self.assertIn(b"configured generation=4 record=00000004.cfg verification=verified",
                      retired.stdout)

        report = self.config_report()
        served, domain = report.split(" served=", 1)[1].split(" domain=", 1)
        self.assertNotIn("fn.admin", served.split(","))
        self.assertIn("fn.admin", domain.split(","))
        # Retirement removes service eligibility but not historical article
        # obligations or the allocation-domain identity they rely on.
        self.native("store", self.store, "inspect", message_id)

    def test_running_owner_refuses_offline_administration(self):
        self.start_owner()
        refused = self.operator("group", "create", "fn.locked", expected=1)
        self.assertIn(b"already locked", refused.stderr)

    def test_uncertain_publication_recovers_and_sweeps_admitted_stage_residue(self):
        uncertain_env = dict(self.env)
        uncertain_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "namespace"
        uncertain = self.operator("group", "create", "fn.recover",
                                  expected=3, env=uncertain_env)
        self.assertIn(b"publication is uncertain", uncertain.stderr)
        self.assertTrue((self.store / "config" / "00000002.cfg").is_file())

        # The shared publisher and the ACL2 sweep use the one `.stage-`
        # namespace.  This emulates an interrupted ephemeral stage without
        # inventing a separate administrative recovery rule.
        residue = self.store / "staging" / ".stage-native-admin-residue"
        residue.write_bytes(b"interrupted configuration stage")
        recovered = self.operator("recover")
        self.assertEqual(recovered.returncode, 0)
        self.assertFalse(residue.exists())
        self.assertIn("generation=2", self.config_report())

    def test_two_administrators_have_no_post_publish_generation_race(self):
        # Start two independent public writers.  The nonblocking Store lock
        # permits either order; every result remains an explicit success or
        # lock refusal, never a false fault from a later generation observed
        # after the first command relinquishes its authority.
        first = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config),
             "group", "create", "fn.race"], cwd=ROOT, env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        second = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "capacity", "4096"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        first_stdout, first_stderr = first.communicate(timeout=60)
        second_stdout, second_stderr = second.communicate(timeout=60)
        self.assertIn(first.returncode, (0, 1), first_stderr.decode("utf-8", "replace"))
        self.assertIn(second.returncode, (0, 1), second_stderr.decode("utf-8", "replace"))
        self.assertIn(0, (first.returncode, second.returncode))

        # A later independent writer can advance after the first releases the
        # lock.  The earlier durable result has already returned success and
        # is never reclassified against this later generation.
        later = self.operator("capacity", "8192")
        self.assertIn(b"verification=verified", later.stdout)
        self.assertNotIn(b"generation differs", first_stderr + second_stderr)


if __name__ == "__main__":
    unittest.main()
