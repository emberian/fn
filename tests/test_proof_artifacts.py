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
        # The verified guard events must be in each saved image's ACL2 world.
        self.assertIn("books/bp-node-machine-guards", default_roots)
        self.assertIn("books/bp-node-machine-guards", dtn_roots)
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
                    "books/native", "books/owner-fault", "books/future-owner-root"])

    def test_roots_keep_the_image_load_order(self):
        # An attachment must precede the generic it attaches (the payload
        # arena): the check loads the roots in the build script's order,
        # following each ld where it occurs, never sorted.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "host/native").mkdir(parents=True)
            (root / "host/native/build.lisp").write_text(
                '(include-book "books/zeta")\n'
                '(include-book "books/payload-arena-attach")\n'
                '(ld "host/store-host.lisp" :ld-error-action :error)\n'
                '(include-book "books/alpha")\n', encoding="utf-8")
            (root / "host/store-host.lisp").write_text(
                '(include-book "../books/store-intern")\n'
                '(include-book "../books/zeta")\n', encoding="utf-8")
            with mock.patch.dict(proof_artifacts.PROFILES, {
                    "default": proof_artifacts.NativeProfile(
                        "default", "host/native/build.lisp", "build/fn-host", ())}):
                self.assertEqual(proof_artifacts.profile_roots(root, "default"), [
                    "books/zeta", "books/payload-arena-attach",
                    "books/store-intern", "books/alpha"])


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

            # The synthetic .cert fixtures are not ACL2-readable; the
            # acquisition path still exercises real candidate selection.
            with mock.patch.object(proof_artifacts, "profile_roots",
                                   return_value=["books/mid"]), \
                 mock.patch.object(certs.cert_alists, "acl2_certificate_pairs",
                                   side_effect=lambda paths, pairs, acl2, root:
                                       {pair: (True, True) for pair in pairs}):
                result = proof_artifacts.acquire(
                    target, cache, acl2, "default", run=fake_run)
            self.assertTrue(result.ok, result.reason)
            self.assertEqual(len(result.rejected), 1)
            self.assertEqual(len(result.attempts), 2)
            self.assertIn("ACL2 load printed", result.attempts[0])
            self.assertIn("loaded", result.attempts[1])

    def test_a_failed_acquire_names_each_candidate_and_why(self):
        # obstructions-5 item 44: the refusal was one line, rejected=0.
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            cache = base / "cache"
            target = worktree(str(base / "target"))
            acl2 = self.acl2(target)
            fingerprint = proof_artifacts.acl2_toolchain.fingerprint(acl2)
            source = worktree(str(base / "source-1"), certified=["books/base", "books/mid"])
            self.publish_set(source, cache, "/farm/run-1", fingerprint)

            def fake_run(*args, **kwargs):
                return subprocess.CompletedProcess(
                    args[0], 0, b"ACL2 Error in include-book: bad\n", b"")
            with mock.patch.object(proof_artifacts, "profile_roots",
                                   return_value=["books/mid"]), \
                 mock.patch.object(certs.cert_alists, "acl2_certificate_pairs",
                                   side_effect=lambda paths, pairs, acl2, root:
                                       {pair: (True, True) for pair in pairs}):
                result = proof_artifacts.acquire(target, cache, acl2, "default", run=fake_run)
                empty = proof_artifacts.acquire(target, base / "empty-cache", acl2, "default",
                                                run=fake_run)
        self.assertFalse(result.ok)
        self.assertEqual(result.reason, "no complete current artifact set passed an ACL2 load")
        self.assertTrue(any(line.startswith("candidate ") and "/farm/run-1" in line
                            and "REJECTED by the ACL2 load" in line
                            for line in result.considered), result.considered)
        self.assertFalse(empty.ok)
        self.assertIn("no candidate set at all", "\n".join(empty.considered))

    def test_books_in_no_set_are_named_with_their_cache_story(self):
        from types import SimpleNamespace
        partial = SimpleNamespace(identity="a" * 64, origin_root="/farm/run-9",
                                  origin_kind="run", entries={"books/base": None},
                                  required=("books/base", "books/mid"),
                                  missing=("books/mid",), complete=False)
        lines = proof_artifacts.describe_candidates(
            Path("/t"), Path("/c"), [partial], "tc", {},
            why=lambda root, cache, name, tc: f"why-{name}")
        self.assertIn("1 of 2 books: incomplete: missing books/mid", lines[0])
        self.assertEqual(lines[1], "  in no set: books/mid: why-books/mid")

    def test_why_no_entry_without_a_cache_entry(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory + "/t")
            self.assertEqual(certs.why_no_entry(root, Path(directory) / "c", "books/base"),
                             "no certificate in the cache for these bytes")

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


class FirstFailedBookTests(unittest.TestCase):
    """obstructions-7 item 62: a failed acquire names the first book that
    failed to load."""

    def test_the_book_at_or_after_the_first_marker(self):
        output = ("ACL2 !>\n(include-book \"books/fine\")\nACL2 Error in ( INCLUDE-BOOK "
                  "\"books/owner\" ...):  The certificate\nfile /t/books/owner.cert\n"
                  "ACL2 Error later in books/other\n")
        self.assertEqual(proof_artifacts.first_failed_book(output),
                         'first failed book books/owner (ACL2 Error in ( INCLUDE-BOOK '
                         '"books/owner" ...):  The certificate)')
        after = "HARD ACL2 ERROR in LOAD\nwhile loading /tank/t/books/login-binding.fasl\n"
        self.assertIn("books/login-binding", proof_artifacts.first_failed_book(after))
        self.assertEqual(proof_artifacts.first_failed_book("all fine\n"), "")
        self.assertEqual(proof_artifacts.first_failed_book("Uncertified thing\n"),
                         "first failure: Uncertified thing")

    def test_validate_puts_it_in_the_reason(self):
        def run(*_args, **_kwargs):
            return subprocess.CompletedProcess(
                [], 0, b'ACL2 Error in ( INCLUDE-BOOK "books/owner" ...)\n')
        with tempfile.TemporaryDirectory() as directory:
            loaded = proof_artifacts.validate(Path(directory), Path("/bin/true"),
                                              ["books/x"], run=run)
        self.assertFalse(loaded.ok)
        self.assertIn("first failed book books/owner", loaded.reason)


if __name__ == "__main__":
    unittest.main()
