"""tools/null_witness_lint.py (obstructions-6 item 54)."""
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import null_witness_lint as lint  # noqa: E402


def findings(text: str) -> list:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "x-tests.lisp"
        path.write_text(text)
        return [name for name, _ in lint.book_findings(path, "x")]


class NullWitnessTests(unittest.TestCase):
    def test_an_empty_lace_over_a_produced_node_without_a_witness_is_named(self):
        self.assertEqual(findings(
            "(assert-event (equal (fn-stx-lace (fn-step *s0* 1)) nil))\n"), ["fn-stx-lace"])
        self.assertEqual(findings("(assert-event (null (fn-stx-lace (fn-step *s0* 1))))\n"),
                         ["fn-stx-lace"])
        self.assertEqual(findings(
            "(assert-event (equal (len (fn-stx-lace (fn-step *s0* 1))) 0))\n"),
            ["fn-stx-lace"])
        self.assertEqual(findings(
            "(defthm t1 (implies (natp n) (endp (fn-stx-lace (fn-step s n)))))\n"),
            ["fn-stx-lace"])

    def test_a_positive_witness_beside_it_clears_it(self):
        for witness in ("(assert-event (consp (fn-stx-lace (fn-step *s0* 2))))",
                        "(assert-event (not (null (fn-stx-lace (fn-step *s0* 2)))))",
                        "(assert-event (equal (fn-stx-lace (fn-step *s0* 2)) '(1 2)))",
                        "(assert-event (member-equal 3 (fn-stx-lace (fn-step *s0* 2))))",
                        "(assert-event (< 0 (len (fn-stx-lace (fn-step *s0* 2)))))"):
            self.assertEqual(findings(
                "(assert-event (equal (fn-stx-lace (fn-step *s0* 1)) nil))\n" + witness),
                [], witness)

    def test_predicates_literals_hypotheses_and_must_fail_are_not_findings(self):
        self.assertEqual(findings("(assert-event (not (fn-validp (fn-step *s0* 1))))"), [])
        self.assertEqual(findings("(assert-event (equal (fn-article-msgid 7) nil))"), [])
        self.assertEqual(findings("(assert-event (equal (fn-sn-keyring *sni-initial*) nil))"),
                         [])
        self.assertEqual(findings(
            "(defthm t1 (implies (null (fn-lace (fn-step s 1))) (natp n)))"), [])
        self.assertEqual(findings(
            "(must-fail (assert-event (equal (fn-lace (fn-step s 1)) nil)))"), [])

    def test_main_warns_allows_and_names_stale(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests" / "acl2").mkdir(parents=True)
            (root / "tests" / "acl2" / "a-tests.lisp").write_text(
                "(assert-event (equal (fn-lace (fn-step *s0* 1)) nil))\n")
            allow = root / "allow.json"
            allow.write_text(json.dumps({"allow": {}}))
            with mock.patch.object(lint, "ROOT", root), mock.patch.object(lint, "ALLOW", allow):
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    self.assertEqual(lint.main([]), 0)
                    self.assertEqual(lint.main(["--strict"]), 1)
                self.assertIn("WARN tests/acl2/a-tests.lisp:1 fn-lace", out.getvalue())
                allow.write_text(json.dumps({"allow": {
                    "tests/acl2/a-tests.lisp fn-lace": "empty by design",
                    "tests/acl2/a-tests.lisp fn-gone": "was here"}}))
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    self.assertEqual(lint.main(["--strict"]), 1)
                self.assertNotIn("WARN", out.getvalue())
                self.assertIn("STALE tests/acl2/a-tests.lisp fn-gone", out.getvalue())


if __name__ == "__main__":
    unittest.main()
