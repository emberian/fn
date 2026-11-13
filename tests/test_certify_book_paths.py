"""The promoted simulator contains ACL2 books, but paths stay repository-local."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import certify_books

class BookPathTests(unittest.TestCase):
    def test_simulator_roots(self):
        self.assertEqual(certify_books.normalize_book("sim/prng.lisp"), "sim/prng")
        self.assertEqual(certify_books.normalize_book("sim/session"), "sim/session")
        for name in ("sim/../host/adapter", "/tmp/sim/prng", "other/prng", "sim/a.b",
                     "sim//prng", "host/native/startup", "sim/prng.lsp"):
            self.assertIsNone(certify_books.BOOK_NAME.fullmatch(name), name)

if __name__ == "__main__":
    unittest.main()
