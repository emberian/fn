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
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
SPEC = importlib.util.spec_from_file_location("certs", TOOLS / "certs.py")
certs = importlib.util.module_from_spec(SPEC)
sys.modules["certs"] = certs
SPEC.loader.exec_module(certs)


# The textual certificate form, which ACL2 before 8.7 wrote and which reads.
TEXT_CERT = ('(IN-PACKAGE "ACL2")\n"ACL2 Version 8.7"\n'
             ":BEGIN-PORTCULLIS-CMDS\n:END-PORTCULLIS-CMDS\n:EXPANSION-ALIST\nNIL\n")
# ACL2 8.7's compact serializer: binary, opening with the `#Z` magic.
SERIALIZED = b"\n#Z(|ACL2|\x00\x01\x02 fake serialized certificate\n"

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

    TOOLCHAIN = "a" * 64

    def publish(self, source: Path, cache: Path, books: list[str], origin: str):
        manifest = manifest_for(source, books, write=False)
        certs.publish(source, cache, [manifest], books, origin=origin,
                      origin_kind="run")

    def test_two_individually_current_origins_do_not_make_one_set(self):
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
            self.assertIsNone(report.artifact_set)
            self.assertCountEqual(report.uncached, ["books/base"])
            self.assertFalse((target / "books/base.cert").exists())
            self.assertFalse((target / "books/mid.cert").exists())

    def test_source_identical_parent_and_child_from_different_absolute_origins_refuse(self):
        """Regression for the full-book-name conflict seen in the farm logs.

        Both source trees have byte-identical books.  Their certificate bytes
        model ACL2's absolute post-alist: the parent from B requires B's child,
        while the only cached child is from A.  The legacy per-book installer
        assembles that invalid pair; set installation refuses it before ACL2.
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

            legacy = certs.install(target, cache, ["books/base", "books/mid"])
            self.assertEqual(legacy.installed, 2)
            self.assertIn(b"/farm/run-a/books/base.lisp",
                          (target / "books/base.cert").read_bytes())
            self.assertIn(b"/farm/run-b/books/base.lisp",
                          (target / "books/mid.cert").read_bytes())

            (target / "books/base.cert").unlink()
            (target / "books/mid.cert").unlink()
            refused = certs.install_artifact_set(
                target, cache, ["books/mid"], self.TOOLCHAIN)
            self.assertIsNone(refused.artifact_set)
            self.assertFalse((target / "books/base.cert").exists())
            self.assertFalse((target / "books/mid.cert").exists())

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
