"""Small source controls for local include cycles in certification planning."""

import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import certs
import certify_books


class ClosureCycleTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        (self.root / "books").mkdir()
        for name in ("_hash_file", "_plan_file"):
            patch = mock.patch.object(certs, name, return_value=None)
            patch.start()
            self.addCleanup(patch.stop)

    def book(self, name, *includes):
        (self.root / f"books/{name}.lisp").write_text(
            '(in-package "ACL2")\n'
            + "".join(f'(include-book "{target}")\n' for target in includes),
            encoding="utf-8",
        )

    def test_diamond_preserves_acyclic_key_and_reuses_scoped_closure(self):
        self.book("top", "left", "right")
        self.book("left", "shared")
        self.book("right", "shared")
        self.book("shared")
        listing = [
            f"books/{name}.lisp:{certs.form_hash(self.root / f'books/{name}.lisp')}"
            for name in ("left", "right", "shared", "top")
        ]
        previous_key = hashlib.sha256(
            (certs.KEY_VERSION + "\nworld plain\n" + "\n".join(listing)).encode("utf-8")
        ).hexdigest()
        with certs.closure_scope(), mock.patch.object(
            certs, "book_facts", wraps=certs.book_facts
        ) as facts:
            self.assertEqual(certs.closure_key(self.root, "books/top"), (previous_key, listing))
            self.assertEqual(set(certs.closure(self.root, "books/top")),
                             {"books/left", "books/right", "books/shared", "books/top"})
            self.assertEqual(facts.call_count, 4)

    def test_cycle_refuses_keys_and_plans_with_closed_path(self):
        self.book("top", "left")
        self.book("left", "right")
        self.book("right", "left")
        path = r"^local include-book cycle: books/left -> books/right -> books/left$"
        cache = self.root / "unused-cache"
        with certs.closure_scope(), mock.patch.object(certs, "cached_entries") as entries:
            with self.assertRaisesRegex(certs.UnreadableBook, path):
                certs.closure_key(self.root, "books/top")
            with self.assertRaisesRegex(certs.UnreadableBook, path):
                certs.resolve_plan(self.root, cache, ["books/top"], "fixture")
            entries.assert_not_called()
        with mock.patch.object(certify_books, "ROOT", self.root):
            with self.assertRaisesRegex(certs.UnreadableBook, path):
                certify_books.with_dependencies(["books/top"])

    def test_self_include_is_a_closed_path(self):
        self.book("self", "self")
        with self.assertRaisesRegex(certs.UnreadableBook, r"books/self -> books/self$"):
            certs.include_graph(self.root, ["books/self"])


if __name__ == "__main__":
    unittest.main()
