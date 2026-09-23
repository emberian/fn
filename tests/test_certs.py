"""Unit checks for the certificate cache: what may be cached, and under what key.

Two defects drove these tests, and each has a case here.  A `.cert` lying next
to a book proves nothing about that book -- after a merge it can be the
previous source's certificate -- so nothing is published except against a
certification manifest that ties the certificate to the source it came from.
And a certificate is valid only for a book's whole include closure, so the key
is the closure's hash: same book bytes over a changed dependency is a
different key, not a cache hit ACL2 would then refuse.
"""

import importlib.util
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import threading
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
SPEC = importlib.util.spec_from_file_location("certs", TOOLS / "certs.py")
certs = importlib.util.module_from_spec(SPEC)
sys.modules["certs"] = certs
SPEC.loader.exec_module(certs)


class ACL2AlistProbeTests(unittest.TestCase):
    def test_missing_serialization_package_is_declared_only_in_probe(self):
        calls = []

        def run(*args, **kwargs):
            calls.append(kwargs["input"].decode())
            if len(calls) == 1:
                return mock.Mock(returncode=0, stdout=b'The name "INSTANCE" does not designate any package')
            return mock.Mock(returncode=0, stdout=b'ACL2 !>@@PAIR 0 1 T T\n@@DONE 1\n')

        with mock.patch.object(certs.cert_alists.subprocess, "run", run):
            result = certs.cert_alists.acl2_certificate_pairs(
                [Path("a.cert"), Path("b.cert")], [(0, 1)], Path("acl2"), Path("."))
        self.assertEqual(result, {(0, 1): (True, True)})
        self.assertIn('(defpkg "INSTANCE" nil)', calls[1])
        self.assertNotIn('(defpkg "INSTANCE" nil)', calls[0])

    def test_unreadable_or_incomplete_probe_fails_closed(self):
        paths = [Path("a.cert"), Path("b.cert")]
        for output in (b'@@UNREADABLE 1\n@@PAIR 0 1 NIL NIL\n@@DONE 1\n',
                       b'@@PAIR 0 1 T T\n'):
            with self.subTest(output=output):
                with mock.patch.object(certs.cert_alists.subprocess, "run",
                                       return_value=mock.Mock(returncode=0,
                                                              stdout=output)):
                    with self.assertRaises(ValueError):
                        certs.cert_alists.acl2_certificate_pairs(
                            paths, [(0, 1)], Path("acl2"), Path("."))


# The textual certificate form, which ACL2 before 8.7 wrote and which reads.
TEXT_CERT = ('(IN-PACKAGE "ACL2")\n"ACL2 Version 8.7"\n'
             ":BEGIN-PORTCULLIS-CMDS\n:END-PORTCULLIS-CMDS\n:EXPANSION-ALIST\nNIL\n")
# ACL2 8.7's compact serializer: binary, opening with the `#Z` magic.
SERIALIZED = b"\n#Z(|ACL2|\x00\x01\x02 fake serialized certificate\n"
TEST_COMPATIBILITY = {
    "schema": "fn-acl2-toolchain-v1",
    "launcher_chain_sha256": ["1" * 64],
    "core_sha256": "2" * 64,
    "runtime_sha256": "3" * 64,
    "proof_environment": {
        "ACL2_CUSTOMIZATION": "NONE",
        "ACL2_BOOK_HASH_ALISTP": "NIL",
        "ACL2_SYSTEM_BOOKS": None,
    },
}

# A two-level closure: the test book includes mid, and mid includes base.
BOOKS = {
    "books/base": '(in-package "ACL2")\n(defun fn-b (x) x)\n',
    "books/mid": '(in-package "ACL2")\n(include-book "base")\n(defun fn-m (x) x)\n',
    "tests/acl2/mid-tests": '(in-package "ACL2")\n(include-book "../../books/mid")\n',
}
CLOSURE = {"books/base": [], "books/mid": ["books/base"],
           "tests/acl2/mid-tests": ["books/mid", "books/base"]}


def worktree(directory: str, books: dict[str, str] | None = None,
             certified: list[str] | None = None) -> Path:
    """A throwaway worktree: books, and a certificate pair for some of them."""
    root = Path(directory).resolve()
    (root / "books").mkdir(parents=True, exist_ok=True)
    (root / "tests" / "acl2").mkdir(parents=True, exist_ok=True)
    for name, text in (books or BOOKS).items():
        (root / f"{name}.lisp").write_text(text)
    for name in certified or []:
        (root / f"{name}.cert").write_bytes(SERIALIZED + name.encode())
        (root / f"{name}.port").write_text(f'(in-package "ACL2") ; {name}\n')
    return root


def manifest_for(root: Path, certified: list[str], status: str = "passed",
                 write: bool = True) -> dict:
    """The manifest `tools/certify_books.py` would have written for that run."""
    sources = {f"{name}.lisp": certs.content_hash(root / f"{name}.lisp")
               for name in BOOKS}
    manifest = {
        "status": status,
        "requested_books": list(certified),
        "source_digests_sha256": sources,
        "source_digests_sha256_after": dict(sources),
        "certificate_digests_sha256": {
            name: certs.content_hash(root / f"{name}.cert") for name in certified},
        "acl2_exit_codes": {name: 0 for name in certified},
        "acl2_version": "ACL2 Version 8.7 test",
        "acl2_executable_sha256": "a" * 64,
        "acl2_compatibility": TEST_COMPATIBILITY,
        "acl2_toolchain_identity": certs.stable_identity(TEST_COMPATIBILITY),
        "acl2_toolchain": {"status": "qualified", "fixture": True},
        "environment": {"ACL2_BOOK_HASH_ALISTP": "NIL"},
    }
    if write:
        run = root / "build" / "acl2" / "certify-20260919T000000Z-1"
        run.mkdir(parents=True, exist_ok=True)
        (run / "manifest.json").write_text(json.dumps(manifest, indent=2))
    return manifest


def entry(cache: Path, root: Path, name: str, origin: Path | None = None) -> Path:
    """Where the pair for one book in one worktree lands in the cache."""
    key, _ = certs.closure_key(root, name)
    return certs.entry_directory(cache, key, str(origin or root))


class ClosureKeyTests(unittest.TestCase):
    def test_the_key_covers_the_whole_transitive_include_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory)
            for name, dependencies in CLOSURE.items():
                found = certs.closure(root, name)
                self.assertCountEqual(found, [name] + dependencies, name)

    def test_a_changed_dependency_changes_the_key_of_an_unchanged_book(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            first = worktree(one)
            second = worktree(two)
            before = certs.closure_key(second, "tests/acl2/mid-tests")[0]
            self.assertEqual(certs.closure_key(first, "tests/acl2/mid-tests")[0],
                             before)
            (second / "books/base.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-b (x) (+ 1 x))\n')
            after = certs.closure_key(second, "tests/acl2/mid-tests")
            self.assertNotEqual(after[0], before)
            # The book's own bytes did not change; the listing shows why.
            self.assertEqual(certs.content_hash(first / "tests/acl2/mid-tests.lisp"),
                             certs.content_hash(second / "tests/acl2/mid-tests.lisp"))
            self.assertEqual(len(after[1]), 3)

    def test_a_system_include_is_not_part_of_the_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            books = dict(BOOKS)
            books["books/base"] = ('(in-package "ACL2")\n'
                                   '(include-book "std/lists/rev" :dir :system)\n')
            root = worktree(directory, books)
            self.assertEqual(sorted(certs.closure(root, "books/base")), ["books/base"])

    def test_a_missing_dependency_is_reported_rather_than_guessed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory)
            (root / "books/base.lisp").unlink()
            with self.assertRaises(certs.UnreadableBook):
                certs.closure_key(root, "books/mid")


class PublishTests(unittest.TestCase):
    def test_interrupted_port_replacement_is_not_a_usable_entry(self):
        """Old metadata cannot bless new port bytes after a process dies."""
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary, certified=["books/mid"])
            cache = root / "cache"
            manifest = manifest_for(root, ["books/mid"], write=False)
            certs.publish(root, cache, [manifest], ["books/mid"])
            key, _ = certs.closure_key(root, "books/mid")
            directory, selected = certs.cached_entries(cache, key)[0]
            self.assertEqual(selected["port_sha256"],
                             certs.content_hash(directory / "book.port"))

            # The writer replaced book.port but died before the metadata
            # commit. The certificate bytes did not change.
            (directory / "book.port").write_bytes(b"different port")
            self.assertEqual(certs.cached_entries(cache, key), [])
            with self.assertRaises(certs.EntryChanged):
                certs.install_entry(directory, selected, root / "copy.cert",
                                    root / "copy.port")

    def test_reader_refuses_a_generation_replaced_after_selection(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary, certified=["books/mid"])
            cache = root / "cache"
            origin = "/farm/same-origin"
            first_manifest = manifest_for(root, ["books/mid"], write=False)
            certs.publish(root, cache, [first_manifest], ["books/mid"], origin)
            key, _ = certs.closure_key(root, "books/mid")
            directory, selected = certs.cached_entries(cache, key)[0]

            (root / "books/mid.cert").write_bytes(SERIALIZED + b"replacement")
            (root / "books/mid.port").write_bytes(b"replacement port")
            second_manifest = manifest_for(root, ["books/mid"], write=False)
            certs.publish(root, cache, [second_manifest], ["books/mid"], origin)
            target_cert = root / "copy.cert"
            target_port = root / "copy.port"
            with self.assertRaises(certs.EntryChanged):
                certs.install_entry(directory, selected, target_cert, target_port)
            self.assertFalse(target_cert.exists())
            current = certs.cached_entries(cache, key)[0][1]
            self.assertTrue(certs.install_entry(directory, current,
                                                target_cert, target_port))
            self.assertEqual(target_cert.read_bytes(), (directory / "book.cert").read_bytes())
            self.assertEqual(target_port.read_bytes(), (directory / "book.port").read_bytes())

    def test_concurrent_publishers_commit_one_matched_pair_and_metadata(self):
        """Two harvests of the same origin cannot share a temp or mix pairs."""
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            first = worktree(str(base / "first"), certified=["books/mid"])
            second = worktree(str(base / "second"), certified=["books/mid"])
            for root, marker in ((first, b"first"), (second, b"second")):
                (root / "books/mid.cert").write_bytes(SERIALIZED + marker)
                (root / "books/mid.port").write_bytes(b"port-" + marker)
            manifests = [manifest_for(root, ["books/mid"], write=False)
                         for root in (first, second)]
            cache = base / "cache"
            origin = "/farm/same-origin"
            first_copy = threading.Event()
            release_first = threading.Event()
            second_started = threading.Event()
            second_copy = threading.Event()
            real_copystat = shutil.copystat

            def paused_copystat(source, target, *args, **kwargs):
                if source == first / "books/mid.cert":
                    first_copy.set()
                    self.assertTrue(release_first.wait(5))
                if source == second / "books/mid.cert":
                    second_copy.set()
                return real_copystat(source, target, *args, **kwargs)

            def publish_second():
                second_started.set()
                return certs.publish(second, cache, [manifests[1]],
                                     ["books/mid"], origin=origin)

            with mock.patch.object(certs.shutil, "copystat", paused_copystat):
                with ThreadPoolExecutor(max_workers=2) as pool:
                    one = pool.submit(certs.publish, first, cache,
                                      [manifests[0]], ["books/mid"], origin)
                    self.assertTrue(first_copy.wait(5))
                    two = pool.submit(publish_second)
                    self.assertTrue(second_started.wait(5))
                    try:
                        self.assertFalse(second_copy.wait(0.1))
                    finally:
                        release_first.set()
                    self.assertEqual(one.result(timeout=5).published, 1)
                    self.assertEqual(two.result(timeout=5).published, 1)

            directory = entry(cache, second, "books/mid", Path(origin))
            meta = certs.read_meta(directory)
            self.assertEqual((directory / "book.cert").read_bytes(),
                             (second / "books/mid.cert").read_bytes())
            self.assertEqual((directory / "book.port").read_bytes(),
                             (second / "books/mid.port").read_bytes())
            self.assertEqual(meta["cert_sha256"],
                             certs.content_hash(directory / "book.cert"))
            self.assertEqual(meta["published_from"], str(second / "books"))
            self.assertEqual(len(certs.cached_entries(cache,
                             certs.closure_key(second, "books/mid")[0])), 1)

    def test_a_manifest_verified_pair_is_stored_under_its_closure_key(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest_for(root, ["books/mid"])
            cache = root / "cache"
            report = certs.publish(root, cache)
            self.assertEqual((report.published, report.manifests), (1, 1))
            self.assertEqual(report.unverified, [])
            key, listing = certs.closure_key(root, "books/mid")
            where = entry(cache, root, "books/mid")
            self.assertTrue((where / "book.cert").is_file())
            self.assertTrue((where / "book.port").is_file())
            meta = certs.read_meta(where)
            self.assertEqual((meta["book"], meta["closure_key"]), ("books/mid", key))
            self.assertEqual(meta["origin_root"], str(root))
            self.assertEqual(meta["closure"], listing)
            self.assertEqual(len(meta["closure"]), 2)
            self.assertEqual(certs.publish(root, cache).already, 1)

    def test_a_certificate_with_no_manifest_is_never_published(self):
        # The poisoning case: a stale pair from another checkout, sitting
        # beside a book nothing in this evidence tree certified.
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            report = certs.publish(root, root / "cache")
            self.assertEqual(report.published, 0)
            self.assertIn("books/mid", report.unverified)

    def test_a_source_edited_after_certification_is_never_published(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest_for(root, ["books/mid"])
            (root / "books/mid.lisp").write_text(
                '(in-package "ACL2")\n(include-book "base")\n(defun fn-m (x) (+ 1 x))\n')
            report = certs.publish(root, root / "cache")
            self.assertEqual((report.published, report.unverified),
                             (0, ["books/mid"]))

    def test_a_dependency_edited_after_certification_is_never_published(self):
        """The book's own source is untouched; its closure is not.

        The key hashes the whole closure, so publishing here would file a
        real certificate under a key describing source it was never produced
        from -- and the next worktree would install it and get a sub-book
        checksum mismatch out of ACL2.  While publishing waited for a wholly
        successful run, the run-wide `sources_unchanged` check covered this;
        publishing a failed run's passing books needs it per book.
        """
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest_for(root, ["books/mid"])
            (root / "books/base.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-b (x) (+ 1 x))\n')
            report = certs.publish(root, root / "cache")
            self.assertEqual(report.published, 0)
            self.assertEqual(
                report.unverified,
                ["books/mid: closure changed since certification: books/base.lisp"])

    def test_a_certificate_replaced_after_certification_is_never_published(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest_for(root, ["books/mid"])
            (root / "books/mid.cert").write_bytes(SERIALIZED + b"from another run")
            report = certs.publish(root, root / "cache")
            self.assertEqual((report.published, report.unverified),
                             (0, ["books/mid"]))

    def test_a_manifest_that_did_not_pass_vouches_for_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest_for(root, ["books/mid"], status="failed")
            self.assertEqual(certs.publish(root, root / "cache").published, 0)

    def test_launcher_only_legacy_manifest_is_not_reusable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest = manifest_for(root, ["books/mid"], write=False)
            manifest.pop("acl2_compatibility")
            manifest["acl2_toolchain"] = {
                "status": "unqualified", "reason": "unknown launcher"}
            report = certs.publish(root, root / "cache", [manifest])
            self.assertEqual(report.published, 0)
            self.assertIn("no qualified ACL2 launcher/core/runtime fingerprint",
                          report.unverified[0])

    def test_a_recorded_closure_error_after_the_run_vouches_for_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest = manifest_for(root, ["books/mid"], write=False)
            manifest["source_digests_sha256_after"] = {"closure-error": "gone"}
            self.assertEqual(certs.publish(root, root / "cache", [manifest]).published, 0)

    def test_an_explicit_manifest_is_the_only_evidence_consulted(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid", "books/base"])
            manifest = manifest_for(root, ["books/base"], write=False)
            report = certs.publish(root, root / "cache", [manifest])
            self.assertEqual(report.published, 1)
            self.assertIn("books/mid", report.unverified)
            self.assertEqual(
                certs.read_meta(entry(root / "cache", root, "books/base"))["book"],
                "books/base")

    def test_valid_looking_accepts_both_certificate_formats(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory)
            cert = root / "books/base.cert"
            for bad in (b"", b"garbage\n", b'(IN-PACKAGE "ACL2")\n'):
                cert.write_bytes(bad)
                self.assertFalse(certs.valid_looking(cert), bad)
            for good in (SERIALIZED, TEXT_CERT.encode()):
                cert.write_bytes(good)
                self.assertTrue(certs.valid_looking(cert), good[:8])


class InstallTests(unittest.TestCase):
    # These publish with a farm origin -- a path that does not exist on this
    # machine -- because that is the case where a pair may be installed into
    # another worktree at all.  `OriginTests` covers the refusal.
    FARM = "/tank/fn/no-such-tree"

    def published(self, directory: str, books: list[str]) -> tuple[Path, Path]:
        root = worktree(directory, certified=books)
        manifest_for(root, books)
        cache = root / "cache"
        certs.publish(root, cache, origin=self.FARM, origin_host="hbox")
        return root, cache

    def test_install_matches_a_worktree_whose_whole_closure_matches(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            _, cache = self.published(one, ["books/mid"])
            target = worktree(two)
            report = certs.install(target, cache)
            self.assertEqual((report.installed, report.kept), (1, 0))
            self.assertCountEqual(report.uncached,
                                  ["books/base", "tests/acl2/mid-tests"])
            self.assertTrue(certs.valid_looking(target / "books/mid.cert"))
            self.assertTrue((target / "books/mid.port").is_file())
            self.assertEqual(certs.install(target, cache).kept, 1)

    def test_a_changed_dependency_is_not_a_cache_hit(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            _, cache = self.published(one, ["books/mid"])
            target = worktree(two)
            (target / "books/base.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-b (x) (+ 1 x))\n')
            report = certs.install(target, cache)
            self.assertEqual(report.installed, 0)
            self.assertIn("books/mid", report.uncached)
            self.assertFalse((target / "books/mid.cert").exists())

    def test_a_differing_local_certificate_is_replaced_by_the_verified_one(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            _, cache = self.published(one, ["books/mid"])
            target = worktree(two)
            (target / "books/mid.cert").write_bytes(SERIALIZED + b"unverified local")
            self.assertEqual(certs.install(target, cache).installed, 1)
            self.assertNotIn(b"unverified local",
                             (target / "books/mid.cert").read_bytes())

    def test_install_removes_a_port_the_cached_entry_does_not_have(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            root = worktree(one, certified=["books/mid"])
            (root / "books/mid.port").unlink()
            manifest_for(root, ["books/mid"])
            cache = root / "cache"
            certs.publish(root, cache, origin=self.FARM)
            target = worktree(two)
            (target / "books/mid.port").write_text("; left over\n")
            certs.install(target, cache)
            self.assertFalse((target / "books/mid.port").exists())


class OriginTests(unittest.TestCase):
    """A certificate names its sub-books by absolute path, so origin decides."""

    def publish_from(self, directory: str, origin: Path | None = None,
                     host: str | None = None) -> tuple[Path, Path]:
        root = worktree(directory, certified=["books/mid"])
        manifest_for(root, ["books/mid"])
        cache = root / "cache"
        certs.publish(root, cache, origin=str(origin) if origin else None,
                      origin_host=host)
        return root, cache

    def test_publish_records_the_worktree_the_run_happened_in(self):
        with tempfile.TemporaryDirectory() as directory:
            root, cache = self.publish_from(directory)
            meta = certs.read_meta(entry(cache, root, "books/mid"))
            self.assertEqual(meta["origin_root"], str(root))
            # An explicit origin -- a farm run -- is recorded instead.
            root2, cache2 = self.publish_from(directory + "/x" if False else
                                              tempfile.mkdtemp(),
                                              origin=Path("/tank/fn/tree"),
                                              host="hbox")
            meta2 = certs.read_meta(
                entry(cache2, root2, "books/mid", Path("/tank/fn/tree")))
            self.assertEqual((meta2["origin_root"], meta2["origin_host"]),
                             ("/tank/fn/tree", "hbox"))

    def test_an_entry_from_another_live_worktree_is_refused(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source, cache = self.publish_from(one)
            target = worktree(two)
            report = certs.install(target, cache)
            self.assertEqual(report.installed, 0)
            self.assertEqual(report.foreign_local, ["books/mid"])
            self.assertFalse((target / "books/mid.cert").exists())
            self.assertTrue(source.exists())  # the origin is why it was refused

    def test_an_entry_whose_origin_is_gone_installs_anywhere(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            _, cache = self.publish_from(one, origin=Path("/tank/fn/no-such-tree"))
            target = worktree(two)
            report = certs.install(target, cache)
            self.assertEqual((report.installed, report.foreign_local), (1, []))
            self.assertTrue(certs.valid_looking(target / "books/mid.cert"))

    def test_this_worktrees_own_entry_wins_over_a_relocatable_one(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            _, cache = self.publish_from(one, origin=Path("/tank/fn/no-such-tree"))
            target = worktree(two, certified=["books/mid"])
            manifest_for(target, ["books/mid"])
            certs.publish(target, cache)  # the target's own pair, distinct bytes
            key, _ = certs.closure_key(target, "books/mid")
            self.assertEqual(len(certs.cached_entries(cache, key)), 2)
            chosen = certs.choose_entry(certs.cached_entries(cache, key),
                                        str(target))
            self.assertEqual(chosen[1]["origin_root"], str(target))
            self.assertEqual(certs.install(target, cache).kept, 1)

    def test_a_pair_installed_from_a_live_worktree_earlier_is_removed(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source, cache = self.publish_from(one)
            target = worktree(two)
            # What the previous, origin-blind install left behind.
            (target / "books/mid.cert").write_bytes(
                (source / "books/mid.cert").read_bytes())
            (target / "books/mid.port").write_text("; foreign\n")
            report = certs.install(target, cache)
            self.assertEqual((report.removed_foreign, report.installed), (1, 0))
            self.assertEqual(report.foreign_local, ["books/mid"])
            self.assertFalse((target / "books/mid.cert").exists())
            self.assertFalse((target / "books/mid.port").exists())

    def test_status_counts_foreign_local_entries_separately(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            _, cache = self.publish_from(one)
            target = worktree(two)
            report = certs.status(target, cache)
            self.assertEqual(report.foreign_local, ["books/mid"])
            self.assertTrue(any("foreign-local 1" in line for line in report.lines()))


class SnapshotOriginTests(unittest.TestCase):
    """A gate directory and a farm run root are not live worktrees.

    The origin rule refuses an entry whose origin tree still exists here,
    because ACL2 would follow that tree's absolute sub-book paths.  On a farm
    box every gate directory and every lane root is still on disk, so the
    rule refused the box its own cache: the measured cost was a lane
    certifying a whole dependency closure that the box had already certified.
    A gate directory is built from one commit by one run and never certified
    into again, so its pairs carry `origin_kind` and install anywhere.
    """

    def gate(self, directory: str, kind: str | None = "gate") -> tuple[Path, Path]:
        root = worktree(directory, certified=["books/mid"])
        manifest_for(root, ["books/mid"])
        cache = root / "cache"
        certs.publish(root, cache, origin_kind=kind)
        return root, cache

    def test_a_gate_entry_installs_where_the_gate_directory_still_exists(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            gate, cache = self.gate(one)
            self.assertEqual(
                certs.read_meta(entry(cache, gate, "books/mid"))["origin_kind"],
                "gate")
            target = worktree(two)
            report = certs.install(target, cache)
            # The same publish without the kind is `test_an_entry_from_another
            # _live_worktree_is_refused`: one field is the whole difference.
            self.assertTrue(gate.is_dir())
            self.assertEqual((report.installed, report.foreign_local), (1, []))
            self.assertTrue(certs.valid_looking(target / "books/mid.cert"))

    def test_this_worktrees_own_entry_still_wins_over_a_snapshot(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            _, cache = self.gate(one)
            target = worktree(two, certified=["books/mid"])
            manifest_for(target, ["books/mid"])
            certs.publish(target, cache)
            chosen = certs.choose_entry(
                certs.cached_entries(cache, certs.closure_key(target, "books/mid")[0]),
                str(target))
            self.assertEqual(chosen[1]["origin_root"], str(target))

    def test_the_label_is_corrected_on_a_pair_already_in_the_cache(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            root, cache = self.gate(one, kind=None)
            self.assertEqual(
                certs.read_meta(entry(cache, root, "books/mid"))["origin_kind"],
                "worktree")
            # The same bytes, published again by a run that knows its tree is
            # a snapshot.  Nothing is copied; the classification changes.
            again = certs.publish(root, cache, origin_kind="run")
            self.assertEqual((again.published, again.already, again.relabelled),
                             (0, 1, 1))
            self.assertEqual(
                certs.read_meta(entry(cache, root, "books/mid"))["origin_kind"],
                "run")
            self.assertEqual(certs.install(worktree(two), cache).installed, 1)

    def test_the_farm_runners_environment_supplies_the_kind(self):
        with tempfile.TemporaryDirectory() as one:
            with mock.patch.dict(os.environ, {"FN_CERT_ORIGIN_KIND": "run"}):
                root, cache = self.gate(one, kind=None)
            self.assertEqual(
                certs.read_meta(entry(cache, root, "books/mid"))["origin_kind"],
                "run")
            # An unknown value is not a licence to relocate certificates.
            with mock.patch.dict(os.environ, {"FN_CERT_ORIGIN_KIND": "wishful"}):
                self.assertEqual(certs.default_origin_kind(), "worktree")


class ArtifactSetTests(unittest.TestCase):
    """A closure is installed from one origin/toolchain, or not at all."""

    TOOLCHAIN = certs.stable_identity(TEST_COMPATIBILITY)

    def publish(self, source: Path, cache: Path, books: list[str], origin: str):
        manifest = manifest_for(source, books, write=False)
        certs.publish(source, cache, [manifest], books, origin=origin,
                      origin_kind="run")

    def age(self, cache: Path, source: Path, origin: str, when: str) -> None:
        """Back-date every entry ``origin`` published."""
        for meta_path in cache.glob("*/*/meta.json"):
            meta = json.loads(meta_path.read_text())
            if meta.get("origin_root") == origin:
                meta["published_at"] = when
                meta_path.write_text(json.dumps(meta))

    def test_two_snapshot_origins_compose_one_set(self):
        """Each book current in a different snapshot origin: one composed set.

        Measured on persvati 2026-09-23 (certificate-cache-2026-09-23.md):
        ACL2 accepts a parent from one origin over a child from another,
        because it compares sub-books by familiar name, annotations and
        book-hash, never by full-book-name.
        """
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base"])
            second = worktree(two, certified=["books/mid"])
            self.publish(first, cache, ["books/base"], "/farm/run-a")
            self.publish(second, cache, ["books/mid"], "/farm/run-b")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertIsNotNone(report.artifact_set)
            self.assertEqual(report.artifact_origin, certs.COMPOSED)
            self.assertEqual(report.origins, {"/farm/run-a": 1, "/farm/run-b": 1})
            self.assertEqual((report.installed, report.uncached), (2, []))
            self.assertEqual((target / "books/base.cert").read_bytes(),
                             (first / "books/base.cert").read_bytes())
            self.assertEqual((target / "books/mid.cert").read_bytes(),
                             (second / "books/mid.cert").read_bytes())
            line = report.lines()[1]
            self.assertIn("origin composed", line)
            self.assertIn("; origins /farm/run-a=1,/farm/run-b=1", line)

    def test_each_pair_keeps_the_bytes_its_own_origin_wrote(self):
        """The case the single-origin rule was written for, now composed.

        The certificate bytes model ACL2's post-alist: the parent from B names
        B's child, while the only cached child is from A.  On 2026-09-21 two
        farm runs failed with messages naming exactly such paths, and the
        rule was read off those messages; ACL2 prints them only after a
        book-hash or annotation mismatch, and lists every entry by name when
        the names differ.  A mixture of current pairs includes cleanly
        (certificate-cache-2026-09-23.md, cases 1 to 3 and the extension).
        """
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base"])
            second = worktree(two, certified=["books/mid"])
            (first / "books/base.cert").write_bytes(
                SERIALIZED + b" FULL-BOOK /farm/run-a/books/base.lisp")
            (second / "books/mid.cert").write_bytes(
                SERIALIZED + b" REQUIRES /farm/run-b/books/base.lisp")
            self.publish(first, cache, ["books/base"], "/farm/run-a")
            self.publish(second, cache, ["books/mid"], "/farm/run-b")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual(report.artifact_origin, certs.COMPOSED)
            self.assertIn(b"/farm/run-a/books/base.lisp",
                          (target / "books/base.cert").read_bytes())
            self.assertIn(b"/farm/run-b/books/base.lisp",
                          (target / "books/mid.cert").read_bytes())

    def test_a_single_complete_origin_is_preferred_to_a_composition(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            whole = worktree(one, certified=["books/base", "books/mid"])
            self.publish(whole, cache, ["books/base", "books/mid"], "/farm/whole")
            newer = worktree(two, certified=["books/base"])
            (newer / "books/base.cert").write_bytes(SERIALIZED + b" newer base")
            self.publish(newer, cache, ["books/base"], "/farm/newer")
            self.age(cache, whole, "/farm/whole", "2026-01-01T00:00:00+00:00")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual(report.artifact_origin, "/farm/whole")
            self.assertEqual(report.origins, {"/farm/whole": 2})

    def test_the_newest_pair_is_taken_for_each_book(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as three, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            old = worktree(one, certified=["books/base"])
            (old / "books/base.cert").write_bytes(SERIALIZED + b" old base")
            self.publish(old, cache, ["books/base"], "/farm/old")
            new = worktree(two, certified=["books/base"])
            (new / "books/base.cert").write_bytes(SERIALIZED + b" new base")
            self.publish(new, cache, ["books/base"], "/farm/new")
            mid = worktree(three, certified=["books/mid"])
            self.publish(mid, cache, ["books/mid"], "/farm/mid")
            self.age(cache, old, "/farm/old", "2026-01-01T00:00:00+00:00")
            self.age(cache, new, "/farm/new", "2026-09-01T00:00:00+00:00")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual(report.origins, {"/farm/new": 1, "/farm/mid": 1})
            self.assertIn(b"new base", (target / "books/base.cert").read_bytes())

    def test_a_live_worktree_still_on_disk_is_not_composed(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            live = worktree(one, certified=["books/base"])
            certs.publish(live, cache, [manifest_for(live, ["books/base"], write=False)],
                          ["books/base"], origin=str(live), origin_kind="worktree")
            snapshot = worktree(two, certified=["books/mid"])
            self.publish(snapshot, cache, ["books/mid"], "/farm/run-b")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertIsNone(report.artifact_set)
            self.assertEqual(report.uncached, ["books/base"])
            self.assertFalse((target / "books/base.cert").exists())
            self.assertFalse((target / "books/mid.cert").exists())

    def test_a_snapshot_origin_whose_directory_is_gone_still_installs(self):
        """ACL2 never opens the origin's files (the experiment's case 2)."""
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            gone = Path(one) / "gate"
            gate = worktree(str(gone), certified=["books/base"])
            certs.publish(gate, cache, [manifest_for(gate, ["books/base"], write=False)],
                          ["books/base"], origin=str(gate), origin_kind="gate")
            snapshot = worktree(two, certified=["books/mid"])
            self.publish(snapshot, cache, ["books/mid"], "/farm/run-b")
            shutil.rmtree(gone)
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual(report.origins, {str(gate): 1, "/farm/run-b": 1})
            self.assertTrue((target / "books/base.cert").is_file())

    def test_require_origin_keeps_the_single_origin_rule(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base"])
            second = worktree(two, certified=["books/mid"])
            self.publish(first, cache, ["books/base"], "/farm/run-a")
            self.publish(second, cache, ["books/mid"], "/farm/run-b")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN,
                require_origin="/farm/run-b")
            self.assertIsNone(report.artifact_set)
            self.assertEqual(report.uncached, ["books/base"])

    def test_a_composition_never_mixes_toolchains(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base"])
            manifest = manifest_for(first, ["books/base"], write=False)
            manifest["acl2_compatibility"] = dict(TEST_COMPATIBILITY, core_sha256="9" * 64)
            certs.publish(first, cache, [manifest], ["books/base"],
                          origin="/farm/run-a", origin_kind="run")
            second = worktree(two, certified=["books/mid"])
            self.publish(second, cache, ["books/mid"], "/farm/run-b")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(target, cache, ["books/mid"])
            self.assertIsNone(report.artifact_set)

    def test_one_complete_origin_is_installed_as_a_unit(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source = worktree(one, certified=["books/base", "books/mid"])
            cache = Path(one) / "cache"
            self.publish(source, cache, ["books/base", "books/mid"],
                         "/farm/coherent")
            target = worktree(two)
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertIsNotNone(report.artifact_set)
            self.assertEqual(report.artifact_origin, "/farm/coherent")
            self.assertEqual(report.installed, 2)
            self.assertTrue((target / "books/base.cert").is_file())
            self.assertTrue((target / "books/mid.cert").is_file())

    def test_toolchain_is_part_of_the_set_identity(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source = worktree(one, certified=["books/base", "books/mid"])
            cache = Path(one) / "cache"
            self.publish(source, cache, ["books/base", "books/mid"],
                         "/farm/coherent")
            target = worktree(two)
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], "b" * 64)
            self.assertIsNone(report.artifact_set)
            self.assertCountEqual(report.uncached, ["books/base", "books/mid"])

    def test_runner_and_reader_hashes_are_provenance_not_compatibility(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            source = worktree(one, certified=["books/base", "books/mid"])
            for name, marker in (("books/base", "a"), ("books/mid", "b")):
                manifest = manifest_for(source, [name], write=False)
                manifest["runner_sha256"] = marker * 64
                manifest["reader_sha256"] = marker.upper() * 64
                certs.publish(source, cache, [manifest], [name],
                              origin="/farm/coherent", origin_kind="run")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual(report.artifact_origin, "/farm/coherent")
            self.assertEqual(report.installed, 2)
            key, _ = certs.closure_key(target, "books/base")
            base_meta = certs.cached_entries(cache, key)[0][1]
            self.assertEqual(
                base_meta["certification_provenance"]["runner_sha256"], "a" * 64)

    def test_incremental_install_requires_the_origin_it_will_extend(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base", "books/mid"])
            second = worktree(two, certified=["books/base", "books/mid"])
            for root, label in ((first, b"/farm/run-a"), (second, b"/farm/run-b")):
                for name in ("books/base", "books/mid"):
                    (root / f"{name}.cert").write_bytes(
                        SERIALIZED + b" FULL-BOOK " + label + b"/" + name.encode())
            self.publish(first, cache, ["books/base", "books/mid"], "/farm/run-a")
            self.publish(second, cache, ["books/base", "books/mid"], "/farm/run-b")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN,
                require_origin="/farm/run-a")
            self.assertEqual(report.artifact_origin, "/farm/run-a")
            self.assertIn(b"/farm/run-a/books/base",
                          (target / "books/base.cert").read_bytes())
            self.assertIn(b"/farm/run-a/books/mid",
                          (target / "books/mid.cert").read_bytes())

    def test_incremental_set_needs_dependencies_not_the_changed_root(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            source = worktree(one, certified=["books/base"])
            self.publish(source, cache, ["books/base"], "/farm/canonical")
            target = worktree(destination + "/target")
            report = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN,
                require_origin="/farm/canonical", dependencies_only=True)
            self.assertEqual(report.artifact_origin, "/farm/canonical")
            self.assertEqual(report.books, 1)
            self.assertTrue((target / "books/base.cert").exists())
            self.assertFalse((target / "books/mid.cert").exists())

    def test_closure_recertification_purges_every_stale_pair_on_miss(self):
        with tempfile.TemporaryDirectory() as directory:
            target = worktree(directory, certified=["books/base", "books/mid"])
            report = certs.install_artifact_set(
                target, target / "empty-cache", ["books/mid"], self.TOOLCHAIN,
                require_origin=str(target), purge_on_miss=True)
            self.assertIsNone(report.artifact_set)
            self.assertEqual(report.removed_foreign, 4)
            for name in ("books/base", "books/mid"):
                self.assertFalse((target / f"{name}.cert").exists())
                self.assertFalse((target / f"{name}.port").exists())


class PartialInstallTests(unittest.TestCase):
    """`install-partial`: every cached book installs, the rest are named."""

    TOOLCHAIN = ArtifactSetTests.TOOLCHAIN
    publish = ArtifactSetTests.publish

    @staticmethod
    def install(*args):
        # The synthetic certificate fixtures are not ACL2-readable.  The
        # real ACL2 alist reader has its own integration test below.
        return certs.install_partial(
            *args, acl2=Path("/fixture/acl2"),
            pair_checker=lambda paths, pairs, acl2, root:
                {pair: (True, True) for pair in pairs})

    def test_a_cached_bottom_installs_and_the_uncached_top_is_named(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            source = worktree(one, certified=["books/base", "books/mid"])
            self.publish(source, cache, ["books/base", "books/mid"], "/farm/run-a")
            target = worktree(destination + "/target")
            # A stale pair for the uncached root, left from an earlier attempt.
            (target / "tests/acl2/mid-tests.cert").write_bytes(SERIALIZED + b" stale")
            (target / "tests/acl2/mid-tests.port").write_text("; stale\n")
            report = self.install(
                target, cache, ["tests/acl2/mid-tests"], self.TOOLCHAIN)
            self.assertEqual(report.books, 3)
            self.assertEqual(report.installed, 2)
            self.assertEqual(report.uncached, ["tests/acl2/mid-tests"])
            self.assertEqual(report.installed_from,
                             {"books/base": "/farm/run-a", "books/mid": "/farm/run-a"})
            self.assertEqual(report.roots_installed, [])
            self.assertEqual(report.removed_foreign, 2)
            self.assertFalse((target / "tests/acl2/mid-tests.cert").exists())
            self.assertFalse((target / "tests/acl2/mid-tests.port").exists())
            line = report.lines()[1]
            self.assertIn("installed 2, kept 0, missing 1, removed 2; "
                          "roots installed 0 of 1; origins /farm/run-a=2", line)

    def test_a_fully_cached_closure_installs_its_roots_too(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            source = worktree(one, certified=["books/base", "books/mid"])
            self.publish(source, cache, ["books/base", "books/mid"], "/farm/run-a")
            target = worktree(destination + "/target")
            report = self.install(target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual((report.installed, report.uncached), (2, []))
            self.assertEqual(report.roots_installed, ["books/mid"])
            again = self.install(target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual((again.installed, again.kept), (0, 2))

    def test_a_partial_set_draws_each_book_from_its_own_origin(self):
        """Two origins, each with one book of a three-book closure; the third
        (the root) is uncached.  install-set refuses this; install-partial
        installs both and names the root."""
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base"])
            second = worktree(two, certified=["books/mid"])
            self.publish(first, cache, ["books/base"], "/farm/run-a")
            self.publish(second, cache, ["books/mid"], "/farm/run-b")
            target = worktree(destination + "/target")
            refused = certs.install_artifact_set(
                target, cache, ["tests/acl2/mid-tests"], self.TOOLCHAIN)
            self.assertIsNone(refused.artifact_set)
            report = self.install(
                target, cache, ["tests/acl2/mid-tests"], self.TOOLCHAIN)
            self.assertEqual(report.origins, {"/farm/run-a": 1, "/farm/run-b": 1})
            self.assertEqual(report.uncached, ["tests/acl2/mid-tests"])
            self.assertEqual((target / "books/base.cert").read_bytes(),
                             (first / "books/base.cert").read_bytes())
            self.assertEqual((target / "books/mid.cert").read_bytes(),
                             (second / "books/mid.cert").read_bytes())

    def test_same_source_different_acl2_hash_selects_matching_older_child(self):
        """The hbox replay failure had exactly this parent/child shape."""
        with tempfile.TemporaryDirectory() as one, \
                tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base", "books/mid"])
            second = worktree(two, certified=["books/base"])
            self.publish(first, cache, ["books/base", "books/mid"], "/farm/first")
            self.publish(second, cache, ["books/base"], "/farm/second")
            target = worktree(destination + "/target")
            older_base = entry(cache, target, "books/base", Path("/farm/first"))
            newer_base = entry(cache, target, "books/base", Path("/farm/second"))

            def acl2_pairs(paths, pairs, acl2, root):
                self.assertEqual(acl2, Path("/fixture/acl2"))
                return {pair: (True, paths[pair[1]].parent == older_base)
                        for pair in pairs}

            report = certs.install_partial(
                target, cache, ["books/mid"], self.TOOLCHAIN,
                acl2=Path("/fixture/acl2"), pair_checker=acl2_pairs)
            self.assertEqual(report.uncached, [])
            self.assertEqual(report.installed_from["books/base"], "/farm/first")
            self.assertEqual(report.installed_from["books/mid"], "/farm/first")
            self.assertNotEqual(older_base, newer_base)

    def test_compatible_cascade_can_move_one_conflict_before_resolving(self):
        """A child switch may first move the mismatch to another parent."""
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory)
            options = {
                "books/base": [(Path("base-new"), {}), (Path("base-old"), {})],
                "books/mid": [(Path("mid-new"), {}), (Path("mid-old"), {})],
                "tests/acl2/mid-tests": [(Path("test"), {})],
            }

            def probe(paths, pairs, acl2, probe_root):
                self.assertEqual(probe_root, root)
                def matches(parent, child):
                    p, c = paths[parent].parent.name, paths[child].parent.name
                    if p == "test" and c.startswith("mid-"):
                        return c == "mid-old"
                    if p.startswith("mid-") and c.startswith("base-"):
                        return p.removeprefix("mid-") == c.removeprefix("base-")
                    return True
                return {pair: (True, matches(*pair)) for pair in pairs}

            selected = certs.compatible_partial_choices(
                root, options, Path("acl2"), pair_checker=probe)
            self.assertEqual(selected["books/base"][0], Path("base-old"))
            self.assertEqual(selected["books/mid"][0], Path("mid-old"))
            self.assertEqual(selected["tests/acl2/mid-tests"][0], Path("test"))

    def test_incompatible_cached_parent_is_recertified_if_no_child_matches(self):
        with tempfile.TemporaryDirectory() as one, \
                tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            parent = worktree(one, certified=["books/mid"])
            child = worktree(two, certified=["books/base"])
            self.publish(parent, cache, ["books/mid"], "/farm/parent")
            self.publish(child, cache, ["books/base"], "/farm/child")
            target = worktree(destination + "/target")
            report = certs.install_partial(
                target, cache, ["books/mid"], self.TOOLCHAIN,
                acl2=Path("/fixture/acl2"),
                pair_checker=lambda paths, pairs, acl2, root:
                    {pair: (True, False) for pair in pairs})
            self.assertEqual(report.uncached, ["books/mid"])
            self.assertEqual(report.installed_from,
                             {"books/base": "/farm/child"})

    def test_a_cached_parent_over_an_uncached_child_is_recertified(self):
        """The new child's ACL2 book-hash is unknown until certification."""
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            source = worktree(one, certified=["books/mid"])
            self.publish(source, cache, ["books/mid"], "/farm/run-a")
            target = worktree(destination + "/target")
            report = self.install(target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual(report.uncached, ["books/base", "books/mid"])
            self.assertEqual(report.roots_installed, [])

    def test_another_toolchain_and_a_live_worktree_are_never_drawn_from(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two, \
                tempfile.TemporaryDirectory() as destination:
            cache = Path(destination) / "cache"
            first = worktree(one, certified=["books/base"])
            manifest = manifest_for(first, ["books/base"], write=False)
            manifest["acl2_compatibility"] = dict(TEST_COMPATIBILITY, core_sha256="9" * 64)
            certs.publish(first, cache, [manifest], ["books/base"],
                          origin="/farm/run-a", origin_kind="run")
            live = worktree(two, certified=["books/mid"])
            certs.publish(live, cache, [manifest_for(live, ["books/mid"], write=False)],
                          ["books/mid"], origin=str(live), origin_kind="worktree")
            target = worktree(destination + "/target")
            report = self.install(target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertEqual(report.uncached, ["books/base", "books/mid"])
            self.assertEqual(report.installed, 0)

    def test_the_command_line_requires_a_toolchain(self):
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch("sys.stderr"):
            root = worktree(directory)
            with self.assertRaises(SystemExit):
                certs.main(["--root", str(root), "--cache", str(root / "c"),
                            "install-partial", "books/mid"])


class StatusAndRemoteTests(unittest.TestCase):
    def test_status_reports_local_and_cached_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, certified=["books/mid"])
            manifest_for(root, ["books/mid"])
            cache = root / "cache"
            certs.publish(root, cache)
            report = certs.status(root, cache)
            self.assertEqual((report.books, report.certified_locally), (3, 1))
            self.assertCountEqual(report.uncached,
                                  ["books/base", "tests/acl2/mid-tests"])
            self.assertTrue(any("in the cache" in line for line in report.lines()))
            self.assertEqual(report.origins, {str(root): 1})

    def test_remote_target_uses_this_projects_farm_paths(self):
        self.assertEqual(certs.remote_target("hbox"), "hbox:/tank/fn/certcache")
        self.assertEqual(certs.remote_target("persvati"), "persvati:~/fn-certcache")
        self.assertEqual(certs.remote_target("box:/x/y"), "box:/x/y")
        with self.assertRaises(ValueError):
            certs.remote_target("unknown-box")

    def test_mirror_makes_the_remote_directory_then_rsyncs(self):
        commands = []
        certs.mirror(Path("/cache"), "hbox",
                     run=lambda command, **kwargs: commands.append(command))
        self.assertEqual(commands[0], ["ssh", "hbox", "mkdir -p /tank/fn/certcache"])
        self.assertEqual(commands[1],
                         ["rsync", "-a", "/cache/", "hbox:/tank/fn/certcache/"])


if __name__ == "__main__":
    unittest.main()
