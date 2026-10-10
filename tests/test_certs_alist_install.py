"""`certs.py install` composes by ACL2's criterion, not by origin.

A book's certificate is installable iff, for every dependency, the entry its
post-alist requires equals that dependency's installed certificate's own
entry (include-book-alist-subsetp: familiar name, annotations, book-hash; the
full path is ignored, measured 2026-09-23).  Origins are provenance only
(coordinator ruling, 2026-10-07).  Here ACL2 is stood in for by `hashes`: a
parent certificate's bytes name the digest of the child certificate it was
certified over, and the pair agrees iff the installed child has that digest.
"""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from tests.test_certs import (SERIALIZED, TEST_COMPATIBILITY, certs, install,
                              manifest_for, worktree)

ORIGIN_A = "/tank/fn/no-such-origin-a"
ORIGIN_B = "/tank/fn/no-such-origin-b"


def digest(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def hashes(paths, pairs, acl2, root):
    """ACL2 stand-in: a parent's post-alist entry for a child is the
    `over:<sha256>` its bytes carry; it agrees iff the child is that file."""
    out = {}
    for p, c in pairs:
        parent = Path(paths[p]).read_bytes()
        required = b"over:" in parent
        out[(p, c)] = (required, not required
                       or f"over:{digest(paths[c])}".encode() in parent)
    return out


class AlistInstallTests(unittest.TestCase):
    def publish(self, directory: str, cache: Path, certs_by_book: dict[str, bytes],
                origin: str, published_at: str = "2026-10-01T00:00:00+00:00",
                books: dict[str, str] | None = None) -> Path:
        root = worktree(directory, books=books, certified=list(certs_by_book))
        for name, data in certs_by_book.items():
            (root / f"{name}.cert").write_bytes(data)
        manifest_for(root, list(certs_by_book), books=books)
        certs.publish(root, cache, origin=origin, origin_host="hbox")
        for name in certs_by_book:
            meta_path = (certs.entry_directory(cache, certs.closure_key(root, name)[0], origin)
                         / "meta.json")
            meta = json.loads(meta_path.read_text())
            meta["published_at"] = published_at
            meta_path.write_text(json.dumps(meta))
        return root

    @staticmethod
    def base(tag: str) -> bytes:
        return SERIALIZED + b"base " + tag.encode()

    @staticmethod
    def mid_over(base_cert: bytes, tag: str = "") -> bytes:
        return SERIALIZED + b"mid " + tag.encode() + b" over:" + \
            hashlib.sha256(base_cert).hexdigest().encode()

    def test_a_pair_certified_in_this_tree_over_resident_dependencies_is_kept(self):
        # CERT-INSTALL-DELETES-IN-TREE-PAIR (train 10): base installed from
        # origin B; mid certified IN this tree over it and published with this
        # tree as origin.  The one-origin rule deleted it; ACL2's criterion
        # keeps it, because mid's entry for base is the base that is here.
        with tempfile.TemporaryDirectory() as b, tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            base_b = self.base("B")
            self.publish(b, cache, {"books/base": base_b}, ORIGIN_B)
            target = worktree(target_dir)
            install(target, cache, ["books/base"], pair_checker=hashes)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_b)
            fresh = self.mid_over(base_b, "certified here")
            worktree(target_dir, certified=["books/mid"])
            (target / "books/mid.cert").write_bytes(fresh)
            manifest_for(target, ["books/mid"])
            certs.publish(target, cache, names=["books/mid"], origin=str(target),
                          origin_host="hbox")
            report = install(target, cache, pair_checker=hashes)
            self.assertTrue((target / "books/mid.cert").exists(),
                            "install deleted the pair certified in this tree")
            self.assertEqual((target / "books/mid.cert").read_bytes(), fresh)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_b)
            self.assertNotIn("books/mid", report.uncached)

    def test_a_pair_over_another_version_of_its_dependency_is_refused_whatever_its_origin(self):
        # One origin, A, holds both books, but A's mid was certified over a
        # base whose certificate is not the one A published (a recertify in
        # between): same origin, different hash.  The old rule installed it.
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            base_a = self.base("A")
            stale = self.mid_over(self.base("A, before a recertify"))
            self.publish(a, cache, {"books/base": base_a, "books/mid": stale}, ORIGIN_A)
            target = worktree(target_dir)
            report = install(target, cache, pair_checker=hashes)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_a)
            self.assertFalse((target / "books/mid.cert").exists())
            self.assertIn("books/mid", report.uncached)

    def test_pairs_from_two_origins_compose_when_their_hashes_agree(self):
        # The case the one-origin rule refused by name (no single origin).
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            base_b = self.base("B")
            self.publish(b, cache, {"books/base": base_b}, ORIGIN_B)
            self.publish(a, cache, {"books/mid": self.mid_over(base_b, "A")}, ORIGIN_A)
            target = worktree(target_dir)
            report = install(target, cache, pair_checker=hashes)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_b)
            self.assertTrue((target / "books/mid.cert").exists())
            self.assertEqual(report.installed, 2)

    def test_the_search_starts_at_the_resident_pair_not_the_newest(self):
        # Two cached bases; the newer (origin B) is not the one this tree's
        # resident mid was certified over; the resident pair stays.  A
        # regression check, not a tooth: in a closure this small the greedy
        # search's child switch also recovers; the drop it guards against
        # (acquire 1159/1173, 2026-10-07) needed hbox's whole closure.
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            base_a, base_b = self.base("A"), self.base("B, newer")
            mid_a = self.mid_over(base_a, "A")
            self.publish(a, cache, {"books/base": base_a, "books/mid": mid_a}, ORIGIN_A,
                         "2026-10-01T00:00:00+00:00")
            self.publish(b, cache, {"books/base": base_b}, ORIGIN_B,
                         "2026-10-07T00:00:00+00:00")
            target = worktree(target_dir)
            (target / "books/base.cert").write_bytes(base_a)
            (target / "books/mid.cert").write_bytes(mid_a)
            install(target, cache, pair_checker=hashes)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_a)
            self.assertEqual((target / "books/mid.cert").read_bytes(), mid_a)

    def test_install_without_acl2_refuses_rather_than_guess(self):
        with tempfile.TemporaryDirectory() as target_dir, \
                tempfile.TemporaryDirectory() as cache_dir:
            with self.assertRaises(ValueError):
                certs.install(worktree(target_dir), Path(cache_dir))


class ResidentParentTests(unittest.TestCase):
    """A smaller closure's install must not strand a resident parent outside it.

    persvati 2026-10-10 (native-eefe81c43a0d-r2): the default profile's acquire
    installed image-world-part-1 over one bp-recovery-profile; the dtn
    profile's acquire, whose closure holds bp-recovery-profile but not
    image-world-part-1, then installed the newest one.  Every pair each
    install chose was accepted by ACL2 in its own closure; the resident parent
    outside it was not asked.  Here mid plays image-world-part-1 and base
    plays bp-recovery-profile."""
    TOOLCHAIN = certs.stable_identity(TEST_COMPATIBILITY)
    publish = AlistInstallTests.publish
    base = staticmethod(AlistInstallTests.base)
    mid_over = staticmethod(AlistInstallTests.mid_over)

    def scene(self, a, b, cache, target_dir, origin_b=ORIGIN_B, resident_b=False):
        base_a, base_b = self.base("A"), self.base("B")
        mid_a = self.mid_over(base_a, "A")
        self.publish(a, cache, {"books/base": base_a, "books/mid": mid_a}, ORIGIN_A,
                     "2026-10-01T00:00:00+00:00")
        self.publish(b, cache, {"books/base": base_b}, origin_b,
                     "2026-10-02T00:00:00+00:00")
        target = worktree(target_dir)
        (target / "books/base.cert").write_bytes(base_b if resident_b else base_a)
        (target / "books/mid.cert").write_bytes(mid_a)
        return target, base_a, base_b, mid_a

    def test_install_set_of_a_smaller_closure_keeps_the_child_its_resident_parent_needs(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            target, base_a, base_b, mid_a = self.scene(
                a, b, cache, target_dir, origin_b=str(Path(target_dir).resolve()))
            report = certs.install_artifact_set(
                target, cache, ["books/base"], self.TOOLCHAIN,
                acl2=Path("/fixture/acl2"), pair_checker=hashes)
            self.assertIsNotNone(report.artifact_set)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_a)
            self.assertEqual((target / "books/mid.cert").read_bytes(), mid_a)
            self.assertNotEqual(base_a, base_b)

    def test_install_partial_of_a_smaller_closure_keeps_the_child_its_resident_parent_needs(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            target, base_a, _, mid_a = self.scene(a, b, cache, target_dir, resident_b=True)
            certs.install_partial(target, cache, ["books/base"], self.TOOLCHAIN,
                                  acl2=Path("/fixture/acl2"), pair_checker=hashes)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_a)
            self.assertEqual((target / "books/mid.cert").read_bytes(), mid_a)

    def test_a_resident_parent_with_includes_outside_the_closure_is_kept(self):
        # train 86, hbox: protocol_emit --wire installs books/wire-export's
        # closure; image-world includes it AND books outside it, which the
        # search counted as unchosen children, so every image-world
        # certificate the run had just certified was removed.  Here mid
        # includes base (installed) and side (outside the closure).
        books = {"books/base": '(in-package "ACL2")\n(defun fn-b (x) x)\n',
                 "books/side": '(in-package "ACL2")\n(defun fn-s (x) x)\n',
                 "books/mid": '(in-package "ACL2")\n(include-book "base")\n'
                              '(include-book "side")\n(defun fn-m (x) x)\n',
                 "tests/acl2/mid-tests": '(in-package "ACL2")\n(include-book "../../books/mid")\n'}
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            base_a, side = self.base("A"), SERIALIZED + b"side"
            mid_a = self.mid_over(base_a, "A")
            self.publish(a, cache, {"books/base": base_a, "books/side": side, "books/mid": mid_a},
                         ORIGIN_A, "2026-10-01T00:00:00+00:00", books=books)
            self.publish(b, cache, {"books/base": self.base("B")}, ORIGIN_B,
                         "2026-10-02T00:00:00+00:00", books=books)
            target = worktree(target_dir, books=books)
            for name, data in (("books/base", base_a), ("books/side", side), ("books/mid", mid_a)):
                (target / f"{name}.cert").write_bytes(data)
            certs.install_partial(target, cache, ["books/base"], self.TOOLCHAIN,
                                  acl2=Path("/fixture/acl2"), pair_checker=hashes)
            self.assertEqual((target / "books/mid.cert").read_bytes(), mid_a)
            self.assertEqual((target / "books/base.cert").read_bytes(), base_a)
            self.assertEqual((target / "books/side.cert").read_bytes(), side)

    def test_a_resident_parent_no_cached_child_fits_is_removed_not_left_stale(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            base_a = self.base("A")
            mid_a = self.mid_over(base_a, "A")
            self.publish(a, cache, {"books/mid": mid_a}, ORIGIN_A)
            self.publish(b, cache, {"books/base": self.base("B")}, ORIGIN_B)
            target = worktree(target_dir)
            (target / "books/mid.cert").write_bytes(mid_a)
            certs.install_partial(target, cache, ["books/base"], self.TOOLCHAIN,
                                  acl2=Path("/fixture/acl2"), pair_checker=hashes)
            self.assertEqual((target / "books/base.cert").read_bytes(), self.base("B"))
            self.assertFalse((target / "books/mid.cert").exists())


if __name__ == "__main__":
    unittest.main()
