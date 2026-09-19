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
from pathlib import Path
import sys
import tempfile
import unittest


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
    }
    if write:
        run = root / "build" / "acl2" / "certify-20260919T000000Z-1"
        run.mkdir(parents=True, exist_ok=True)
        (run / "manifest.json").write_text(json.dumps(manifest, indent=2))
    return manifest


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
            self.assertTrue((cache / key / "book.cert").is_file())
            self.assertTrue((cache / key / "book.port").is_file())
            meta = certs.read_meta(cache / key)
            self.assertEqual((meta["book"], meta["closure_key"]), ("books/mid", key))
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
            self.assertEqual(certs.read_meta(
                root / "cache" / certs.closure_key(root, "books/base")[0])["book"],
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
    def published(self, directory: str, books: list[str]) -> tuple[Path, Path]:
        root = worktree(directory, certified=books)
        manifest_for(root, books)
        cache = root / "cache"
        certs.publish(root, cache)
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
            certs.publish(root, cache)
            target = worktree(two)
            (target / "books/mid.port").write_text("; left over\n")
            certs.install(target, cache)
            self.assertFalse((target / "books/mid.port").exists())


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
