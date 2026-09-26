"""tools/ascii_check.py: books/ and host/ are ASCII, the debt list only shrinks (PKT-379)."""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import ascii_check  # noqa: E402


class AsciiCheckTests(unittest.TestCase):
    def tree(self, files):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for rel, data in files.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_bytes(data)
        return root

    def test_the_tree_is_clean_but_for_the_listed_debt(self):
        refusals, owed, problems = ascii_check.check()
        self.assertEqual((refusals, problems), ([], []))
        self.assertEqual(owed, ascii_check.load_debt())

    def test_a_stray_character_is_refused_with_file_line_column_and_byte(self):
        root = self.tree({"books/a.lisp": b"(in-package \"ACL2\")\n; see \xc2\xa77\n",
                          "host/h.lisp": b"; ok\n(defun f (x) x) ; \xff\n",
                          "books/clean.lisp": b"; plain\n"})
        refusals, owed, problems = ascii_check.check(root, {})
        self.assertEqual(refusals, [("books/a.lisp", 2, 7, b"\xc2\xa7"),
                                    ("host/h.lisp", 2, 19, b"\xff")])
        self.assertEqual(ascii_check.describe(b"\xc2\xa7"), "U+00A7 SECTION SIGN")
        self.assertEqual(ascii_check.describe(b"\xff"), "not UTF-8")

    def test_debt_is_exact_and_only_shrinks(self):
        root = self.tree({"books/a.lisp": b"; \xc2\xa71\n; \xc2\xa72\n"})
        self.assertEqual(ascii_check.check(root, {"books/a.lisp": 2}), ([], {"books/a.lisp": 2}, []))
        # a new character in a debt file is refused like any other
        (root / "books/a.lisp").write_bytes(b"; \xc2\xa71\n; \xc2\xa72\n; \xe2\x80\x94\n")
        refusals, _, problems = ascii_check.check(root, {"books/a.lisp": 2})
        self.assertEqual(len(refusals), 3)
        self.assertEqual(len(problems), 1)
        # a repaired file must leave the list
        (root / "books/a.lisp").write_bytes(b"; section 1\n")
        refusals, _, problems = ascii_check.check(root, {"books/a.lisp": 2})
        self.assertEqual(refusals, [])
        self.assertIn("lower or remove", problems[0])
        # a listed file that no longer exists is a problem, not silence
        self.assertEqual(len(ascii_check.check(root, {"books/gone.lisp": 1})[2]), 1)


if __name__ == "__main__":
    unittest.main()
