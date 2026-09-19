"""Unit checks for the content-addressed certificate cache.

The cache's promise is narrow and the tests hold it to exactly that: a pair is
stored under the hash of the book *content* that produced it, installed only
into a worktree whose book hashes the same, and never installed over a local
certificate that already matches its book.  A certificate older than the book
beside it is not published at all.
"""

import importlib.util
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest


SPEC = importlib.util.spec_from_file_location(
    "certs", Path(__file__).resolve().parents[1] / "tools" / "certs.py"
)
certs = importlib.util.module_from_spec(SPEC)
sys.modules["certs"] = certs
SPEC.loader.exec_module(certs)


CERT = ('(IN-PACKAGE "ACL2")\n"ACL2 Version 8.7"\n'
        ":BEGIN-PORTCULLIS-CMDS\n:END-PORTCULLIS-CMDS\n:EXPANSION-ALIST\nNIL\n")


def worktree(directory: str, books: dict[str, str], certified: list[str]) -> Path:
    """A throwaway worktree: books, and a plausible certificate for some."""
    root = Path(directory).resolve()
    (root / "books").mkdir(parents=True, exist_ok=True)
    (root / "tests" / "acl2").mkdir(parents=True, exist_ok=True)
    for name, text in books.items():
        (root / f"{name}.lisp").write_text(text)
    for name in certified:
        (root / f"{name}.cert").write_text(CERT + f'; {name}\n')
        (root / f"{name}.port").write_text(f'(in-package "ACL2") ; {name}\n')
        future = time.time() + 2
        os.utime(root / f"{name}.cert", (future, future))
        os.utime(root / f"{name}.port", (future, future))
    return root


BOOKS = {"books/alpha": '(in-package "ACL2")\n(defun a (x) x)\n',
         "books/beta": '(in-package "ACL2")\n(defun b (x) x)\n',
         "tests/acl2/alpha-tests": '(in-package "ACL2")\n'}


class PublishTests(unittest.TestCase):
    def test_publish_stores_the_pair_under_the_book_content_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, BOOKS, ["books/alpha"])
            cache = root / "cache"
            report = certs.publish(root, cache)
            self.assertEqual((report.published, report.books), (1, 3))
            self.assertCountEqual(report.uncached,
                                  ["books/beta", "tests/acl2/alpha-tests"])
            digest = certs.content_hash(root / "books/alpha.lisp")
            entry = cache / digest / "books--alpha"
            self.assertTrue((entry / "book.cert").is_file())
            self.assertTrue((entry / "book.port").is_file())
            meta = certs.read_meta(entry)
            self.assertEqual((meta["book"], meta["book_sha256"]),
                             ("books/alpha", digest))
            # Publishing again is not a second copy.
            self.assertEqual(certs.publish(root, cache).published, 0)
            self.assertEqual(certs.publish(root, cache).already, 1)

    def test_a_certificate_is_published_by_content_regardless_of_mtime(self):
        """Under ACL2_BOOK_HASH_ALISTP=NIL the certificate records the book's
        checksum, so a fresh checkout (book newer than its certificate) is
        still a valid pair; ACL2 refuses a real mismatch at include time."""
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, BOOKS, ["books/alpha"])
            book = root / "books/alpha.lisp"
            cert = root / "books/alpha.cert"
            later = cert.stat().st_mtime + 100
            os.utime(book, (later, later))
            report = certs.publish(root, root / "cache")
            self.assertEqual(report.published, 1)
            self.assertEqual(report.stale, [])

    def test_an_empty_or_truncated_certificate_is_not_valid_looking(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, BOOKS, [])
            for text in ("", "(IN-PACKAGE \"ACL2\")\n", "garbage\n"):
                (root / "books/alpha.cert").write_text(text)
                self.assertFalse(certs.valid_looking(root / "books/alpha.cert"))
            (root / "books/alpha.cert").write_text(CERT)
            self.assertTrue(certs.valid_looking(root / "books/alpha.cert"))


class InstallTests(unittest.TestCase):
    def test_install_matches_by_content_across_worktrees(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source = worktree(one, BOOKS, ["books/alpha"])
            cache = Path(one) / "cache"
            certs.publish(source, cache)
            target = worktree(two, BOOKS, [])
            report = certs.install(target, cache)
            self.assertEqual(report.installed, 1)
            self.assertEqual(report.kept, 0)
            self.assertCountEqual(report.uncached,
                                  ["books/beta", "tests/acl2/alpha-tests"])
            self.assertTrue(certs.valid_looking(target / "books/alpha.cert"))
            self.assertTrue((target / "books/alpha.port").is_file())
            # The installed certificate is newer than the book it certifies,
            # so this worktree can publish it onward.
            self.assertGreaterEqual((target / "books/alpha.cert").stat().st_mtime,
                                    (target / "books/alpha.lisp").stat().st_mtime)
            self.assertEqual(certs.install(target, cache).kept, 1)

    def test_a_changed_book_gets_no_certificate_from_the_cache(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source = worktree(one, BOOKS, ["books/alpha"])
            cache = Path(one) / "cache"
            certs.publish(source, cache)
            target = worktree(two, BOOKS, [])
            (target / "books/alpha.lisp").write_text('(in-package "ACL2")\n(defun a (x) (+ 1 x))\n')
            report = certs.install(target, cache)
            self.assertEqual(report.installed, 0)
            self.assertIn("books/alpha", report.uncached)
            self.assertFalse((target / "books/alpha.cert").exists())

    def test_install_never_overwrites_a_newer_local_certificate(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source = worktree(one, BOOKS, ["books/alpha"])
            cache = Path(one) / "cache"
            certs.publish(source, cache)
            target = worktree(two, BOOKS, ["books/alpha"])
            local = (target / "books/alpha.cert")
            local.write_text(CERT + "; locally certified\n")
            newer = time.time() + 60
            os.utime(local, (newer, newer))
            report = certs.install(target, cache)
            self.assertEqual((report.installed, report.kept), (0, 1))
            self.assertIn("locally certified", local.read_text())

    def test_install_removes_a_port_the_cached_entry_does_not_have(self):
        with tempfile.TemporaryDirectory() as one, tempfile.TemporaryDirectory() as two:
            source = worktree(one, BOOKS, ["books/alpha"])
            (source / "books/alpha.port").unlink()
            cache = Path(one) / "cache"
            certs.publish(source, cache)
            target = worktree(two, BOOKS, [])
            (target / "books/alpha.port").write_text("; left over\n")
            certs.install(target, cache)
            self.assertFalse((target / "books/alpha.port").exists())


class StatusAndRemoteTests(unittest.TestCase):
    def test_status_reports_local_and_cached_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = worktree(directory, BOOKS, ["books/alpha"])
            cache = root / "cache"
            certs.publish(root, cache)
            report = certs.status(root, cache)
            self.assertEqual((report.books, report.certified_locally), (3, 1))
            self.assertCountEqual(report.uncached,
                                  ["books/beta", "tests/acl2/alpha-tests"])
            self.assertTrue(any("in the cache" in line for line in report.lines()))

    def test_two_books_with_the_same_bytes_do_not_share_one_entry(self):
        with tempfile.TemporaryDirectory() as directory:
            twins = {"books/alpha": '(in-package "ACL2")\n',
                     "books/beta": '(in-package "ACL2")\n'}
            root = worktree(directory, twins, ["books/alpha", "books/beta"])
            cache = root / "cache"
            self.assertEqual(certs.publish(root, cache).published, 2)
            digest = certs.content_hash(root / "books/alpha.lisp")
            self.assertCountEqual([p.name for p in (cache / digest).iterdir()],
                                  ["books--alpha", "books--beta"])

    def test_remote_target_uses_this_projects_farm_paths(self):
        self.assertEqual(certs.remote_target("hbox"), "hbox:/tank/fn/certcache")
        self.assertEqual(certs.remote_target("persvati"), "persvati:~/fn-certcache")
        self.assertEqual(certs.remote_target("box:/x/y"), "box:/x/y")
        with self.assertRaises(ValueError):
            certs.remote_target("unknown-box")

    def test_mirror_makes_the_remote_directory_then_rsyncs(self):
        commands = []

        def fake(command, **kwargs):
            commands.append(command)
            return None

        certs.mirror(Path("/cache"), "hbox", run=fake)
        self.assertEqual(commands[0], ["ssh", "hbox", "mkdir -p /tank/fn/certcache"])
        self.assertEqual(commands[1],
                         ["rsync", "-a", "/cache/", "hbox:/tank/fn/certcache/"])


if __name__ == "__main__":
    unittest.main()
