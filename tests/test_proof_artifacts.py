"""Set-level proof artifacts: declared profiles and ACL2 load rejection."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import certs  # noqa: E402
import proof_artifacts  # noqa: E402
from tests.test_certs import manifest_for, worktree  # noqa: E402


class ProfileTests(unittest.TestCase):
    def test_default_and_dtn_are_distinct_declared_images(self):
        default = proof_artifacts.PROFILES["default"]
        dtn = proof_artifacts.PROFILES["dtn"]
        self.assertEqual((default.build, default.image),
                         ("host/native/build.lisp", "build/fn-host"))
        self.assertEqual((dtn.build, dtn.image),
                         ("host/native/build-dtn.lisp", "build/fn-host-dtn"))
        default_roots = proof_artifacts.profile_roots(ROOT, "default")
        dtn_roots = proof_artifacts.profile_roots(ROOT, "dtn")
        # The common owner now consumes BP application state even in the
        # default image. DTN transport is the profile distinction, not this
        # shared logical dependency.
        self.assertIn("books/bp-node", default_roots)
        self.assertIn("books/bp-node", dtn_roots)
        # Owner fault isolation is now included by owner-config. Assert it
        # remains in each complete artifact set, not necessarily a direct root.
        self.assertIn("books/owner-fault", certs.required_closure(ROOT, default_roots))
        self.assertIn("books/owner-fault", certs.required_closure(ROOT, dtn_roots))

    def test_deployed_owner_host_additions_join_the_artifact_set(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "host/native").mkdir(parents=True)
            (root / "host/native/build.lisp").write_text(
                '(include-book "books/native")\n', encoding="utf-8")
            (root / "host/owner-host.lisp").write_text(
                '(include-book "../books/owner-fault")\n'
                '(include-book "../books/future-owner-root")\n', encoding="utf-8")
            with mock.patch.dict(proof_artifacts.PROFILES, {
                    "default": proof_artifacts.NativeProfile(
                        "default", "host/native/build.lisp", "build/fn-host",
                        ("host/owner-host.lisp",))}):
                self.assertEqual(proof_artifacts.profile_roots(root, "default"), [
                    "books/future-owner-root", "books/native", "books/owner-fault"])


class AcquisitionTests(unittest.TestCase):
    TOOLCHAIN = b"test acl2 image"

    def acl2(self, root: Path) -> Path:
        runtime = root / "fake-sbcl"
        runtime.write_bytes(self.TOOLCHAIN)
        runtime.chmod(0o755)
        core = root / "saved_acl2.core"
        core.write_bytes(b"test core")
        launcher = root / "acl2"
        launcher.write_text(
            '#!/bin/sh\nexec "{}" --core "{}" "$@"\n'.format(runtime, core))
        launcher.chmod(0o755)
        return launcher

    def publish_set(self, source: Path, cache: Path, origin: str,
                    fingerprint):
        names = ["books/base", "books/mid"]
        manifest = manifest_for(source, names, write=False)
        manifest["acl2_compatibility"] = fingerprint.compatibility
        manifest["acl2_toolchain_identity"] = fingerprint.identity
        manifest["acl2_toolchain"] = fingerprint.provenance
        certs.publish(source, cache, [manifest], names, origin=origin,
                      origin_kind="run")

    def test_a_load_failure_rejects_the_whole_set_and_tries_the_next(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            cache = base / "cache"
            target = worktree(str(base / "target"))
            acl2 = self.acl2(target)
            fingerprint = proof_artifacts.acl2_toolchain.fingerprint(acl2)
            for number in (1, 2):
                source = worktree(str(base / f"source-{number}"),
                                  certified=["books/base", "books/mid"])
                self.publish_set(source, cache, f"/farm/run-{number}", fingerprint)

            calls = 0

            def fake_run(*args, **kwargs):
                nonlocal calls
                calls += 1
                output = (b"ACL2 Error in include-book: incompatible absolute origin\n"
                          if calls == 1 else
                          b"FN_ARTIFACT_SET_LOADED\n")
                return subprocess.CompletedProcess(args[0], 0, output, b"")

            with mock.patch.object(proof_artifacts, "profile_roots",
                                   return_value=["books/mid"]):
                result = proof_artifacts.acquire(
                    target, cache, acl2, "default", run=fake_run)
            self.assertTrue(result.ok, result.reason)
            self.assertEqual(len(result.rejected), 1)
            self.assertEqual(len(result.attempts), 2)
            self.assertIn("ACL2 load printed", result.attempts[0])
            self.assertIn("loaded", result.attempts[1])

    def test_an_uncertified_warning_is_a_load_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            acl2 = root / "acl2"
            acl2.write_bytes(self.TOOLCHAIN)

            def fake_run(*args, **kwargs):
                return subprocess.CompletedProcess(
                    args[0], 0,
                    b"ACL2 Warning [Uncertified] FN_ARTIFACT_SET_LOADED\n", b"")

            result = proof_artifacts.validate(
                root, acl2, ["books/base"], run=fake_run)
            self.assertFalse(result.ok)
            self.assertIn("Uncertified", result.reason)


if __name__ == "__main__":
    unittest.main()
