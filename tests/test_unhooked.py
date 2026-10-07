"""tools/unhooked.py and its two readers (certify_books --lane, green_check --gate)."""
import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import certify_books  # noqa: E402
import green_check  # noqa: E402
import unhooked  # noqa: E402


def tree(books, listed):
    root = Path(tempfile.mkdtemp())
    (root / "planning").mkdir()
    (root / "planning" / "decisions.md").write_text(
        "# decisions\n\n### 2026-10-01: D46 — reverted kinds\nbody naming D99\n")
    for book in books:
        (root / f"{book}.lisp").parent.mkdir(parents=True, exist_ok=True)
        (root / f"{book}.lisp").write_text("(in-package \"ACL2\")\n")
    (root / "planning" / "unhooked.json").write_text(json.dumps(
        {"schema": unhooked.SCHEMA, "books": listed}))
    return root


class Check(unittest.TestCase):
    def test_clean(self):
        root = tree(["books/a"], [{"book": "books/a", "decision": "D46"}])
        self.assertEqual(unhooked.findings(root, roots=[]), [])
        self.assertEqual(unhooked.load(root), {"books/a": "D46"})

    def test_must_fail_without_a_decision(self):
        root = tree(["books/a"], [{"book": "books/a"}])
        self.assertEqual(unhooked.findings(root, roots=[]), ["books/a: no decision cited"])

    def test_must_fail_on_a_decision_that_is_no_heading(self):
        # D99 appears in body text only, not in a heading
        root = tree(["books/a"], [{"book": "books/a", "decision": "D99"}])
        self.assertEqual(unhooked.findings(root, roots=[]),
                         ["books/a: D99 is no heading in planning/decisions.md"])

    def test_must_fail_on_a_root_a_missing_source_or_a_duplicate(self):
        root = tree(["books/a"], [{"book": "books/a", "decision": "D46"},
                                  {"book": "books/a", "decision": "D46"},
                                  {"book": "books/gone", "decision": "D46"}])
        found = unhooked.findings(root, roots=["books/a"])
        self.assertIn("books/a: listed twice", found)
        self.assertIn("books/a: is a Makefile root, so it is hooked", found)
        self.assertIn("books/gone: no source books/gone.lisp", found)

    def test_repository_list_is_clean(self):
        self.assertEqual(unhooked.findings(), [])


class Lane(unittest.TestCase):
    def test_unhooked_includer_and_companion_are_left_out(self):
        edges = {"books/x": ["books/t"], "books/u": ["books/t"],
                 "tests/acl2/t-tests": ["books/t"]}
        err = io.StringIO()
        with redirect_stderr(err):
            got = certify_books.lane_selection(
                [], ["books/t"], edges, set(), lambda b: True, [],
                {"books/u": "D46", "tests/acl2/t-tests": "D43"})
        self.assertEqual(got, ["books/t", "books/x"])
        self.assertIn("unhooked (D46): books/u", err.getvalue())
        self.assertIn("unhooked (D43): tests/acl2/t-tests", err.getvalue())

    def test_a_named_unhooked_book_is_still_certified(self):
        got = certify_books.lane_selection(
            [], ["books/u"], {"books/u": []}, set(), lambda b: False, [],
            {"books/u": "D46"})
        self.assertEqual(got, ["books/u"])


class Gate(unittest.TestCase):
    def test_changed_unhooked_book_is_reported_not_red(self):
        report = {"books_by_verdict": {}}
        answer = green_check.gate(report, ["books/u", "tests/acl2/z-tests"], {},
                                  unhooked_books={"books/u": "D46"})
        verdicts = {row["book"]: row["verdict"] for row in answer["rows"]}
        self.assertEqual(verdicts["books/u"], "unhooked (D46)")
        self.assertEqual(verdicts["tests/acl2/z-tests"], "unaudited")
        self.assertEqual(answer["not_green"], ["tests/acl2/z-tests"])


if __name__ == "__main__":
    unittest.main()
