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

    def test_a_known_red_book_is_not_an_orphan_and_carries_its_reason(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests/acl2").mkdir(parents=True)
            (root / "tests/acl2/accounts-wire-tests.lisp").write_text("")
            self.assertEqual(test_roots_check.orphans(root, []), [])
        for reason in test_roots_check.KNOWN_RED.values():
            self.assertIn("certify-", reason)

    def test_this_tree_has_no_orphan(self):
        self.assertEqual(test_roots_check.orphans(), [])


if __name__ == "__main__":
    unittest.main()
