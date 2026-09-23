"""Saved-image witnesses for ACL2-owned native administrative configuration.

The test talks only to the native image's public `operator CONFIG` entry (and
the existing read-only `store config` diagnostic).  Python is test harness
plumbing here; it neither parses fn.toml nor builds configuration records.
"""

import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests.native_process import wait_for_announcement


ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
CORE = Path(str(IMAGE) + ".core") if IMAGE is not None else None
IMAGE_SOURCE_SHA = os.environ.get("FN_NATIVE_IMAGE_SOURCE_SHA")
LAUNCHER_SHA256 = os.environ.get("FN_NATIVE_LAUNCHER_SHA256")
CORE_SHA256 = os.environ.get("FN_NATIVE_CORE_SHA256")


def file_digest(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


ACTUAL_LAUNCHER_SHA256 = (
    file_digest(IMAGE) if IMAGE is not None and IMAGE.is_file() else None)
ACTUAL_CORE_SHA256 = (
    file_digest(CORE) if CORE is not None and CORE.is_file() else None)
IMAGE_READY = bool(
    IMAGE_TEXT and IMAGE is not None and CORE is not None
    and IMAGE.is_file() and os.access(IMAGE, os.X_OK) and CORE.is_file()
    and IMAGE_SOURCE_SHA and LAUNCHER_SHA256 and CORE_SHA256
    and ACTUAL_LAUNCHER_SHA256 == LAUNCHER_SHA256
    and ACTUAL_CORE_SHA256 == CORE_SHA256)


@unittest.skipUnless(
    IMAGE_READY,
    "set explicit FN_NATIVE_HOST/source and matching launcher/core SHA-256 values",
)
class NativeAdminTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        print("native-admin launcher-sha256={} core-sha256={} declared-source={}".format(
            ACTUAL_LAUNCHER_SHA256, ACTUAL_CORE_SHA256, IMAGE_SOURCE_SHA))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-admin-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.store = self.base / "store"
        self.config = self.base / "fn.toml"
        self.payload = self.base / "article"
        self.payload.write_bytes(
            b"From: admin@example.invalid\r\n"
            b"Newsgroups: fn.admin\r\n"
            b"Subject: native admin retained article\r\n"
            b"Message-ID: <native-admin-retained@example.invalid>\r\n"
            b"\r\nnative admin retained article\r\n")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.native("store", self.store, "init", "fn.letters")
        self.config.write_text('[store]\npath = "{}"\n'.format(self.store),
                               encoding="ascii")

    def native(self, *args, expected=0, env=None, timeout=60, image=None):
        result = subprocess.run(
            [str(image or IMAGE), "--fn", *map(str, args)], cwd=ROOT,
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

    def start_owner(self, env=None, image=None):
        process = subprocess.Popen(
            [str(image or IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env or self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        wait_for_announcement(process, b"LISTENING ", timeout=60)
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
        self.assertIn(b"configured generation=2 record=00000002.cfg verification=VERIFIED",
                      created.stdout)
        capacity = self.operator("capacity", "2048")
        self.assertIn(b"configured generation=3 record=00000003.cfg verification=VERIFIED",
                      capacity.stdout)

        message_id = "<native-admin-retained@example.invalid>"
        owner = self.start_owner()
        self.operator("post", "--message-id", message_id, "--payload",
                      self.payload, "--group", "fn.admin")
        self.stop_owner(owner)
        retired = self.operator("group", "retire", "fn.admin")
        self.assertIn(b"configured generation=4 record=00000004.cfg verification=VERIFIED",
                      retired.stdout)

        report = self.config_report()
        served, domain = report.split(" served=", 1)[1].split(" domain=", 1)
        self.assertNotIn("fn.admin", served.split(","))
        self.assertIn("fn.admin", domain.strip().split(","))
        # Retirement removes service eligibility but not historical article
        # obligations or the allocation-domain identity they rely on.
        self.native("store", self.store, "inspect", message_id)

    def test_policy_set_path_identity_is_a_durable_configuration_record(self):
        # RFC 5537 section 3.2: the node's own <path-identity>, written as a
        # `:set-policy` record like a group or a peer, so the owner's replay
        # sees it at open and `fn-peer-local-identity` stops reading "".
        written = self.operator("policy", "set", "path-identity", "a.gate.example.invalid")
        self.assertIn(b"configured generation=2 record=00000002.cfg verification=VERIFIED",
                      written.stdout)
        self.assertIn("generation=2", self.config_report())
        refused = self.operator("policy", "set", "path-identity", ".not.an.identity",
                                expected=5)
        self.assertNotIn(b"configured generation=3", refused.stdout)
        self.assertIn("generation=2", self.config_report())

    def test_running_owner_applies_policy_set_path_identity(self):
        process = self.start_owner()
        written = self.operator("policy", "set", "path-identity", "live.gate.example.invalid")
        self.assertIn(b"accepted operator policy", written.stderr)
        self.stop_owner(process)
        self.assertIn("generation=2", self.config_report())

    def test_peer_add_and_remove_use_public_native_admin(self):
        added = self.operator("peer", "add", "far", "far.example.invalid",
                              "192.0.2.44", "1119", "fn.*", "fn.*",
                              "192.0.2.44", "true")
        self.assertIn(b"configured generation=2 record=00000002.cfg verification=VERIFIED",
                      added.stdout)
        self.assertIn("generation=2", self.config_report())
        removed = self.operator("peer", "remove", "far")
        self.assertIn(b"configured generation=3 record=00000003.cfg verification=VERIFIED",
                      removed.stdout)
        self.assertIn("generation=3", self.config_report())

    def test_running_owner_applies_durable_administration(self):
        process = self.start_owner()
        changed = self.operator("group", "create", "fn.live")
        self.assertIn(b"accepted operator group", changed.stderr)
        self.stop_owner(process)
        self.assertIn("generation=2", self.config_report())

    def test_running_owner_applies_symmetric_peer_add_and_remove(self):
        process = self.start_owner()
        added = self.operator("peer", "add", "near", "path-id",
                              "host.example", "119", "*", "*",
                              "198.51.100.5", "true")
        self.assertIn(b"accepted operator peer", added.stderr)
        removed = self.operator("peer", "remove", "near")
        self.assertIn(b"accepted operator peer", removed.stderr)
        self.stop_owner(process)
        self.assertIn("generation=3", self.config_report())

    def test_live_uncertain_publication_fences_and_recovers(self):
        fault_env = dict(self.env)
        fault_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "namespace"
        process = self.start_owner(env=fault_env, image=DEVELOPER)
        uncertain = self.operator("group", "create", "fn.live-recover", expected=3)
        self.assertIn(b"uncertain operator group", uncertain.stderr)
        self.assertEqual(process.wait(timeout=15), 3)
        self.assertIn("generation=2", self.config_report())

    def test_uncertain_publication_recovers_and_sweeps_admitted_stage_residue(self):
        uncertain_env = dict(self.env)
        uncertain_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "namespace"
        uncertain = self.operator("group", "create", "fn.recover",
                                  expected=3, env=uncertain_env, image=DEVELOPER)
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
        self.assertIn(b"verification=VERIFIED", later.stdout)
        self.assertNotIn(b"generation differs", first_stderr + second_stderr)


if __name__ == "__main__":
    unittest.main()
