"""One origin per composed set: `certs.py install` never mixes origins.

A certificate names its sub-books by the path it was certified under; ACL2
refuses a book whose certificate requires origin A's dependency once origin
B's copy of it is included (hbox, 2026-10-07).  X is books/mid, Y is books/base.
"""

import json
from pathlib import Path
import tempfile
import unittest

from tests.test_certs import SERIALIZED as certs_bytes, certs, manifest_for, worktree

ORIGIN_A = "/tank/fn/no-such-origin-a"
ORIGIN_B = "/tank/fn/no-such-origin-b"


class OneOriginInstallTests(unittest.TestCase):
    def publish(self, directory: str, cache: Path, books: list[str], origin: str,
                published_at: str) -> None:
        root = worktree(directory, certified=books)
        for name in books:  # each origin's certificate bytes differ, as real ones do
            (root / f"{name}.cert").write_bytes(
                certs_bytes + name.encode() + origin.encode())
        manifest_for(root, books)
        certs.publish(root, cache, origin=origin, origin_host="hbox")
        key = certs.closure_key
        for name in books:
            meta_path = certs.entry_directory(cache, key(root, name)[0], origin) / "meta.json"
            meta = json.loads(meta_path.read_text())
            meta["published_at"] = published_at
            meta_path.write_text(json.dumps(meta))

    def test_dependency_comes_from_the_origin_of_the_book_over_it(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            self.publish(a, cache, ["books/base", "books/mid"], ORIGIN_A,
                         "2026-10-01T00:00:00+00:00")
            # Origin B holds only Y, and is the newer.
            self.publish(b, cache, ["books/base"], ORIGIN_B, "2026-10-07T00:00:00+00:00")
            target = worktree(target_dir)
            report = certs.install(target, cache)
            from_a = certs.entry_directory(
                cache, certs.closure_key(target, "books/base")[0], ORIGIN_A)
            self.assertEqual((target / "books/base.cert").read_bytes(),
                             (from_a / "book.cert").read_bytes())
            self.assertEqual((report.installed, report.uncached), (2, ["tests/acl2/mid-tests"]))
            self.assertEqual(report.mixed_origin, [])

    def test_no_single_origin_leaves_the_book_uncertified_and_names_both(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            self.publish(a, cache, ["books/mid"], ORIGIN_A, "2026-10-01T00:00:00+00:00")
            self.publish(b, cache, ["books/base"], ORIGIN_B, "2026-10-07T00:00:00+00:00")
            target = worktree(target_dir)
            report = certs.install(target, cache)
            self.assertFalse((target / "books/mid.cert").exists())
            self.assertTrue((target / "books/base.cert").exists())
            [line] = report.mixed_origin
            self.assertIn("books/mid", line)
            self.assertIn(ORIGIN_A, line)
            self.assertIn(ORIGIN_B, line)
            self.assertTrue(any("mixed-origin" in text for text in report.lines()))

    def test_resident_pair_of_unknown_origin_refuses_the_book_over_it_by_name(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            self.publish(a, cache, ["books/mid"], ORIGIN_A, "2026-10-01T00:00:00+00:00")
            target = worktree(target_dir, certified=["books/base"])
            report = certs.install(target, cache)
            self.assertFalse((target / "books/mid.cert").exists())
            [line] = report.mixed_origin
            self.assertIn("books/mid", line)
            self.assertIn("books/base", line)
            self.assertTrue((target / "books/base.cert").exists())

    def test_partial_install_places_the_assigned_origin_for_dependencies_outside_names(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b, \
                tempfile.TemporaryDirectory() as cache_dir, \
                tempfile.TemporaryDirectory() as target_dir:
            cache = Path(cache_dir)
            self.publish(a, cache, ["books/base", "books/mid"], ORIGIN_A,
                         "2026-10-01T00:00:00+00:00")
            self.publish(b, cache, ["books/base"], ORIGIN_B, "2026-10-07T00:00:00+00:00")
            target = worktree(target_dir)
            certs.install(target, cache)  # whole tree from origin A
            from_b = certs.entry_directory(
                cache, certs.closure_key(target, "books/base")[0], ORIGIN_B)
            (target / "books/base.cert").write_bytes((from_b / "book.cert").read_bytes())
            report = certs.install(target, cache, ["books/mid"])
            from_a = certs.entry_directory(
                cache, certs.closure_key(target, "books/base")[0], ORIGIN_A)
            self.assertEqual((target / "books/base.cert").read_bytes(),
                             (from_a / "book.cert").read_bytes())
            self.assertEqual(report.mixed_origin, [])


if __name__ == "__main__":
    unittest.main()
