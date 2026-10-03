"""tools/test_roots_check.py: a test book in no Makefile list is red (Q7j)."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))

import test_roots_check  # noqa: E402


class TestRootsCheck(unittest.TestCase):
    def test_an_orphan_test_book_is_named(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests/acl2").mkdir(parents=True)
            for name in ("a-tests", "b-tests", "helper"):
                (root / f"tests/acl2/{name}.lisp").write_text("")
            self.assertEqual(test_roots_check.orphans(root, ["tests/acl2/a-tests"]),
                             ["tests/acl2/b-tests"])
            self.assertEqual(test_roots_check.orphans(
                root, ["tests/acl2/a-tests", "tests/acl2/b-tests"]), [])

    def test_an_unlisted_book_is_an_orphan_and_a_known_red_carries_its_reason(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests/acl2").mkdir(parents=True)
            (root / "tests/acl2/example-tests.lisp").write_text("")
            self.assertEqual(test_roots_check.orphans(root, []), ["tests/acl2/example-tests"])
            self.assertEqual(test_roots_check.orphans(root, ["tests/acl2/example-tests"]), [])
        # each reason names its evidence: the red certify run, or the commit
        # that took the book out of the roots
        for reason in test_roots_check.KNOWN_RED.values():
            self.assertRegex(reason, r"certify-|\b[0-9a-f]{9,}\b")

    def test_an_unhooked_header_is_the_reason(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests/acl2").mkdir(parents=True)
            (root / "tests/acl2/parked-tests.lisp").write_text(
                "; UNHOOKED lane (2026-10-02): its closure never certified.\n(in-package \"ACL2\")\n")
            (root / "tests/acl2/later-tests.lisp").write_text(
                "(in-package \"ACL2\")\n; UNHOOKED below the third line? no: line two counts.\n")
            (root / "tests/acl2/plain-tests.lisp").write_text("(in-package \"ACL2\")\n")
            self.assertEqual(test_roots_check.orphans(root, []), ["tests/acl2/plain-tests"])
            self.assertEqual(test_roots_check.unhooked(root)["tests/acl2/parked-tests"],
                             "lane (2026-10-02): its closure never certified.")

    def test_this_tree_has_no_orphan(self):
        self.assertEqual(test_roots_check.orphans(), [])


if __name__ == "__main__":
    unittest.main()
