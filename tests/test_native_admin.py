"""Saved-image witnesses for ACL2-owned native administrative configuration.

The test talks only to the native image's public `operator CONFIG` entry (and
the existing read-only `store config` diagnostic).  Python is test harness
plumbing here; it neither parses fn.toml nor builds configuration records.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import unittest

from tests.native_harness import EXIT_FAULT, EXIT_UNCERTAIN, ROOT, Node, native_image


IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
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
        self.node = Node(self, IMAGE, listener=False, control=False)
        self.base, self.store, self.config = self.node.root, self.node.store_path, self.node.config
        self.payload = self.base / "article"
        self.payload.write_bytes(
            b"From: admin@example.invalid\r\n"
            b"Newsgroups: fn.admin\r\n"
            b"Subject: native admin retained article\r\n"
            b"Message-ID: <native-admin-retained@example.invalid>\r\n"
            b"\r\nnative admin retained article\r\n")
        self.native("store", self.store, "init", "fn.letters")

    def native(self, *args, expected=0, env=None, timeout=60, image=None):
        return self.node.invoke(*args, expect=expected, env=env, timeout=timeout, image=image)

    def operator(self, *words, **kwargs):
        return self.native("operator", self.config, *words, **kwargs)

    def config_report(self):
        return self.native("store", self.store, "config").stdout.decode("ascii")

    def test_create_capacity_retire_reopen_preserves_history(self):
        created = self.operator("group", "create", "fn.admin")
        self.assertIn(b"configured generation=2 record=00000002.cfg verification=VERIFIED",
                      created.stdout)
        capacity = self.operator("capacity", "2048")
        self.assertIn(b"configured generation=3 record=00000003.cfg verification=VERIFIED",
                      capacity.stdout)

        message_id = "<native-admin-retained@example.invalid>"
        self.node.start(timeout=60)
        self.operator("post", "--message-id", message_id, "--payload",
                      self.payload, "--group", "fn.admin")
        self.node.stop()
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
        self.node.start(timeout=60)
        written = self.operator("policy", "set", "path-identity", "live.gate.example.invalid")
        self.assertIn(b"accepted operator policy", written.stderr)
        self.node.stop()
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
        self.node.start(timeout=60)
        changed = self.operator("group", "create", "fn.live")
        self.assertIn(b"accepted operator group", changed.stderr)
        self.node.stop()
        self.assertIn("generation=2", self.config_report())

    def test_running_owner_applies_symmetric_peer_add_and_remove(self):
        self.node.start(timeout=60)
        added = self.operator("peer", "add", "near", "path-id",
                              "host.example", "119", "*", "*",
                              "198.51.100.5", "true")
        self.assertIn(b"accepted operator peer", added.stderr)
        removed = self.operator("peer", "remove", "near")
        self.assertIn(b"accepted operator peer", removed.stderr)
        self.node.stop()
        self.assertIn("generation=3", self.config_report())

    def test_live_uncertain_publication_fences_and_recovers(self):
        self.node.start(env={"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "namespace"},
                        image=DEVELOPER, timeout=60)
        uncertain = self.operator("group", "create", "fn.live-recover",
                                  expected=EXIT_UNCERTAIN)
        self.assertIn(b"uncertain operator group", uncertain.stderr)
        self.node.exited(EXIT_UNCERTAIN, timeout=15)
        self.assertIn("generation=2", self.config_report())

    def test_uncertain_publication_recovers_and_sweeps_admitted_stage_residue(self):
        uncertain = self.operator("group", "create", "fn.recover", expected=EXIT_UNCERTAIN,
                                  env={"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "namespace"},
                                  image=DEVELOPER)
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
             "group", "create", "fn.race"], cwd=ROOT, env=self.node.environment(),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        second = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "capacity", "4096"],
            cwd=ROOT, env=self.node.environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
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



class AdminSectionStructureTests(unittest.TestCase):
    """Lane ACTORS (rebuild step 0, the admin pilot): every owner quantum in
    host/native/admin.lisp is a declared section (def-section
    fnn-quantum-control) and no function of the file classifies a condition
    itself; ACL2 decides at the one envelope (books/failure-scope.lisp)."""

    SOURCE = ROOT / "host/native/admin.lisp"
    OWNER = ROOT / "host/native/owner.lisp"
    SECTIONS = ("compaction", "inspect", "export", "reclaim", "reclaim-instant",
                "limit-carry", "limit", "admin")
    # The offline command executors: no owner section; the command scope is
    # the generator's next piece (planning/handoff-2026-10-03/failure-scope.md).
    OFFLINE = ("fnn-admin-verify-under-lock",)

    def functions(self, text):
        from tests.campaign.native_cuts import host_function
        import re as _re
        return {name: host_function(text, name)
                for name in _re.findall(r"^\(defun ([a-z0-9-]+)", text, _re.M)}

    def test_every_owner_section_site_is_the_declared_control_section(self):
        text = self.SOURCE.read_text(encoding="utf-8")
        owner = self.OWNER.read_text(encoding="utf-8")
        self.assertIn("(def-section fnn-quantum-control", owner)
        decl = owner[owner.index("(def-section fnn-quantum-control"):]
        decl = decl[:decl.index(":doc")]
        self.assertIn(":actors (:control :command)", decl)
        self.assertIn(":admits :live", decl)
        body = re.sub(r";[^\n]*", "", text)
        for transitional in ("(fnn-owner-serialized ", "(fnn-owner-gated ",
                             "(fnn-owner-transit-serialized ", "(fnn-section-run "):
            self.assertNotIn(transitional, body, transitional)
        self.assertEqual(body.count("(fnn-quantum-control"), len(self.SECTIONS))
        for section in self.SECTIONS:
            self.assertIn('(fnn-admin-test-fault "{}")'.format(section), body, section)

    def test_no_function_of_the_file_classifies_a_condition_by_a_parent_class(self):
        text = self.SOURCE.read_text(encoding="utf-8")
        for name, source in self.functions(text).items():
            if name in self.OFFLINE:
                continue
            arms = re.findall(r"\(\s*(error|serious-condition|fnn-store-error)\s+\(", source)
            if name == "fnn-owner-live-reconfigure-locked":
                # Its one arm re-signals (ACL2's refusal un-stages, the
                # condition goes on as itself): a cleanup, not a decision.
                self.assertEqual(arms, ["fnn-store-error"], name)
                self.assertIn("(error e)", source)
                continue
            if arms:
                self.fail("{} decides the kind of a failure by a parent-class arm {}".format(
                    name, arms))

    def test_the_cache_refresh_leaves_its_failure_to_the_section(self):
        from tests.campaign.native_cuts import host_function
        text = self.SOURCE.read_text(encoding="utf-8")
        refresh = host_function(text, "fnn-owner-refresh-config-cache")
        if "handler-case" in refresh:
            self.fail("fnn-owner-refresh-config-cache recasts every failure after the publication as uncertain")
        self.assertNotIn("fnn-store-fenced", refresh)

    def test_admin_is_a_strict_lock_check_enclave(self):
        contracts = json.loads((ROOT / "tools/lock_discipline_contracts.json").read_text())
        enclave = contracts["enclave"]
        self.assertIn("host/native/admin.lisp", enclave["files"])
        excepted = enclave.get("files_except", {}).get("host/native/admin.lisp", {})
        self.assertEqual(sorted(excepted), ["fnn-admin-execute", "fnn-admin-query"])


@unittest.skipUnless(DEVELOPER is not None and DEVELOPER.is_file(),
                     "FN_NATIVE_DEVELOPER_HOST names the developer image")
class AdminSectionBoundaryTests(unittest.TestCase):
    """FN_NATIVE_ADMIN_FAULT=SECTION:fault|uncertain raises inside the named
    owner section of host/native/admin.lisp; the declared envelope classifies
    it and the owner stops (exit 4) or fences (exit 3) before the mutex is
    released.  Never run at the lane's wind-down (2026-10-04): the first run
    is the successor's, on an image of this source."""

    def setUp(self):
        self.node = Node(self, DEVELOPER)
        self.node.init("fn.test")

    def injected(self, section, kind, words, exit_code, line):
        owner = self.node.start(env={"FN_NATIVE_ADMIN_FAULT": "{}:{}".format(section, kind)})
        request = self.node.operator(*words, expect=None)
        self.assertNotEqual(request.returncode, 0, request.stdout + request.stderr)
        self.node.exited(exit_code, timeout=180, process=owner)
        log = owner.stderr.since(0)
        self.assertIn(line, log, log.decode("utf-8", "replace"))

    def test_a_fault_in_the_inspect_section_stops_the_owner_as_a_fault(self):
        self.injected("inspect", "fault", ("store", "inspect", "<absent@example.invalid>"),
                      EXIT_FAULT, b"owner quantum fault; process stopped")

    def test_an_uncertain_outcome_in_the_inspect_section_fences_the_owner(self):
        self.injected("inspect", "uncertain", ("store", "inspect", "<absent@example.invalid>"),
                      EXIT_UNCERTAIN, b"owner quantum uncertain; owner fenced")

    def test_a_fault_in_the_compaction_section_stops_the_owner_as_a_fault(self):
        self.injected("compaction", "fault", ("store", "compact"),
                      EXIT_FAULT, b"owner quantum fault; process stopped")

    def test_a_fault_in_the_admin_section_stops_the_owner_as_a_fault(self):
        self.injected("admin", "fault", ("group", "create", "fn.injected"),
                      EXIT_FAULT, b"owner quantum fault; process stopped")


if __name__ == "__main__":
    unittest.main()
