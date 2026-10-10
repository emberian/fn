"""tools/invariant_risk_check.py: a declared host entry with invariant-risk in the image world fails the step."""
import json
import tempfile
import unittest
from pathlib import Path

from tools import invariant_risk_check as r


def fn(name, risk=False, stobjs=None, calls=()):
    body = ["c", "ACL2::PROGN", [["c", "ACL2::" + c, []] for c in calls]]
    return {"name": "ACL2::" + name, "kind": "defun", "invariant_risk": risk,
            "stobjs_in": stobjs or [], "stobjs_out": [], "body": body}


def decl(name, line=7):
    return {"name": name, "source": "books/x.lisp", "line": line}


class InvariantRiskTests(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp())
        self.addCleanup(lambda: __import__("shutil").rmtree(self.dir, ignore_errors=True))

    def ir(self, functions, name="core.json"):
        path = self.dir / name
        path.write_text(json.dumps({"roots": [], "functions": functions}))
        return path

    def test_a_marked_declared_entry_fails_naming_entry_place_and_cause(self):
        ir = self.ir([fn("FN-BAD", True, calls=["FN-BUF-STEP"]), fn("FN-BUF-STEP", stobjs=["FN-BUF"]),
                      fn("FN-GOOD")])
        problems, marked, unmeasured = r.check([decl("fn-bad"), decl("fn-good", 9)], ir, {"marked": {}})
        self.assertEqual(list(marked), ["fn-bad"])
        self.assertEqual(len(problems), 1)
        self.assertIn("fn-bad (books/x.lisp:7; via fn-buf-step (stobj: fn-buf))", problems[0])
        self.assertEqual(unmeasured, [])

    def test_an_unmarked_declared_entry_passes(self):
        ir = self.ir([fn("FN-GOOD")])
        problems, marked, _ = r.check([decl("fn-good")], ir, {"marked": {}})
        self.assertEqual((problems, marked), ([], {}))

    def test_a_marked_entry_outside_the_registry_is_not_this_gates_business(self):
        ir = self.ir([fn("FN-HELPER", True), fn("FN-GOOD")])
        problems, _, _ = r.check([decl("fn-good")], ir, {"marked": {}})
        self.assertEqual(problems, [])

    def test_the_baseline_only_shrinks(self):
        ir = self.ir([fn("FN-BAD", True), fn("FN-FIXED")])
        listed = {"marked": {"fn-bad": "b: x", "fn-fixed": "b: was marked"}}
        problems, _, _ = r.check([decl("fn-bad"), decl("fn-fixed")], ir, listed)
        self.assertEqual(len(problems), 1)
        self.assertIn("fn-fixed: listed", problems[0])
        problems, _, _ = r.check([decl("fn-bad")], ir, {"marked": {"fn-bad": "b: x"}})
        self.assertEqual(problems, [])

    def test_a_declared_entry_missing_from_the_ir_is_reported_unmeasured(self):
        problems, _, unmeasured = r.check([decl("fn-gone")], self.ir([fn("FN-GOOD")]), {"marked": {}})
        self.assertEqual((problems, unmeasured), ([], ["fn-gone"]))

    def test_absent_empty_unparseable_or_functionless_input_fails_with_a_reason(self):
        for what, make in (("unreadable", lambda: self.dir / "absent.json"),
                           ("empty", lambda: self.write("empty.json", "")),
                           ("does not parse", lambda: self.write("bad.json", "{nope")),
                           ("lists no functions", lambda: self.ir([], "none.json"))):
            problems, marked, _ = r.check([decl("fn-good")], make(), {"marked": {}})
            self.assertEqual(len(problems), 1, what)
            self.assertIn(what, problems[0])
            self.assertEqual(marked, {})

    def test_an_empty_registry_fails(self):
        problems, _, _ = r.check([], self.ir([fn("FN-GOOD")]), {"marked": {}})
        self.assertIn("declares no entries", problems[0])

    def write(self, name, text):
        path = self.dir / name
        path.write_text(text)
        return path


if __name__ == "__main__":
    unittest.main()
