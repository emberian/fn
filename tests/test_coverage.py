"""tools/coverage.py: what the world says about an entry, and the decision rule.

A synthetic world dump (the shape tools/coverage_dump.lisp writes) with a
small call graph, and the registries a tree would have around it.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import coverage  # noqa: E402

BOOK = "/box/tree/books/served.lisp"


def fn(name, callees=(), cls="COMMON-LISP-COMPLIANT", book=BOOK, attachment=None,
       formals=("x",), alias=None):
    """ALIAS: (callee, args) when the body is one application of a function to
    variables, as the dump's `alias` field carries it; None otherwise."""
    return {"name": "ACL2::" + name.upper(), "book": book, "class": "KEYWORD::" + cls,
            "callees": ["ACL2::" + c.upper() if "::" not in c else c for c in callees],
            "attachment": attachment and "ACL2::" + attachment.upper(),
            "formals": ["ACL2::" + f.upper() for f in formals],
            "alias": alias and {"callee": "ACL2::" + alias[0].upper(),
                                "args": ["ACL2::" + a.upper() for a in alias[1]]},
            "body": True, "constrained": False, "non_executable": False}


def thm(name, hyps=(), concl=(), hinted=(), book=BOOK, classes=("REWRITE",)):
    return {"name": "ACL2::" + name.upper(), "book": book,
            "hyps": ["ACL2::" + h.upper() for h in hyps],
            "concl": ["ACL2::" + c.upper() for c in concl],
            "classes": ["KEYWORD::" + c for c in classes], "event": "ACL2::DEFTHM",
            "hinted": ["ACL2::" + h.upper() for h in hinted]}


IF = "COMMON-LISP::IF"
WORLD = {
    "cbd": "/box/tree/books/",
    "functions": [
        # fn-serve: an entry that branches and refuses -> decision
        fn("fn-serve", ["fn-serve-refusal", IF, "fn-field"]),
        fn("fn-serve-refusal", [IF]),
        fn("fn-field", []),                       # straight-line accessor entry
        fn("fn-wrap", ["fn-serve"], cls="PROGRAM", book=None),  # host :program forwarder
        fn("fn-codec-entry", ["fn-decode-x", IF]),
        fn("fn-decode-x", [IF]),
        fn("fn-outer", ["fn-serve", IF]),         # a caller of fn-serve, not an entry
        fn("fn-abstract", [], attachment="fn-concrete"),
        fn("fn-concrete", ["fn-field", IF]),
        fn("fn-scan", [IF, "fn-field"]),          # branches, names no outcome
        fn("fn-route", [IF, "fn-serve"]),         # branches, delegates to fn-serve
        fn("car", [], book=":ground-zero"),
    ],
    "theorems": [
        thm("fn-serve-answers", concl=["fn-serve", "equal"]),
        thm("fn-serve-assumed", hyps=["fn-serve"], concl=["fn-field"]),
        thm("fn-outer-refuses", concl=["fn-outer"], hinted=["fn-serve"]),
        thm("fn-outer-quiet", concl=["fn-outer"]),
        thm("fn-concrete-fields", concl=["fn-concrete"]),
        thm("std-lemma", concl=["fn-serve"], book=":system/std/lists/x.lisp"),
    ],
}

INTERFACES = {"entries": [
    {"name": "fn-serve", "subsystem": "nntp/served", "class": "common-lisp-compliant",
     "keystones": [], "dispatched_from": ["host/native/io.lisp"]},
    {"name": "fn-field", "subsystem": "store", "class": "common-lisp-compliant",
     "keystones": [], "dispatched_from": []},
    {"name": "fn-wrap", "subsystem": "control", "class": "program",
     "keystones": [], "dispatched_from": []},
    {"name": "fn-codec-entry", "subsystem": "store", "class": "common-lisp-compliant",
     "keystones": [], "dispatched_from": []},
    {"name": "fn-abstract", "subsystem": "store", "class": "common-lisp-compliant",
     "keystones": [], "dispatched_from": []},
    {"name": "fn-scan", "subsystem": "store", "class": "common-lisp-compliant",
     "keystones": [], "dispatched_from": []},
    {"name": "fn-missing", "subsystem": "web", "class": "program",
     "keystones": [], "dispatched_from": []},
    {"name": "fn-route", "subsystem": "control", "class": "common-lisp-compliant",
     "keystones": [], "dispatched_from": []},
]}
PROOFS = {"proofs": [
    {"id": "PRF-1", "requirements": ["NNT-002"], "events": ["fn-serve-answers"]},
    {"id": "PRF-2", "requirements": ["STO-001"], "events": ["fn-outer-refuses"]},
]}
REQUIREMENTS = {"requirements": [{"id": "NNT-002"}, {"id": "STO-001"}]}
FAMILIES = {"families": {
    "reply": {"description": "", "requirements": ["NNT-002"]},
    "storage-consistency": {"description": "", "requirements": ["STO-001"]},
}}


def tree() -> Path:
    root = Path(tempfile.mkdtemp())
    (root / "planning").mkdir()
    (root / "build" / "coverage").mkdir(parents=True)
    for name, doc in (("interfaces", INTERFACES), ("proofs", PROOFS),
                      ("requirements", REQUIREMENTS), ("families", FAMILIES)):
        (root / "planning" / (name + ".json")).write_text(json.dumps(doc))
    (root / "build" / "coverage" / "world.json").write_text(json.dumps(WORLD))
    return root


class DelegationTests(unittest.TestCase):
    """`:delegates CALLEE` (host/interfaces.lisp): plumbing whose decision is the
    callee's when the world bears it out, a refused problem otherwise."""

    def build(self):
        world = json.loads(json.dumps(WORLD))
        world["functions"] += [
            fn("fn-wrap-serve", ["fn-serve"], alias=("fn-serve", ["x"])),   # a true alias (cited theorem)
            fn("fn-wrap-scan", ["fn-scan"], alias=("fn-scan", ["x"])),      # a true alias (no theorem)
            fn("fn-wrap-branch", [IF, "fn-serve-refusal"]),  # branches itself, over a helper
            # the 2026-09-29 review's wrappers, each declared :delegates fn-serve:
            fn("fn-wrap-invert", ["not", "fn-serve"]),                        # (not (fn-serve x))
            fn("fn-wrap-hardwire", ["fn-serve"]),                             # (fn-serve x 'admin): calls only fn-serve
            fn("fn-wrap-reorder", ["fn-serve"], formals=("x", "s"),
               alias=("fn-serve", ["s", "x"])),                               # (fn-serve s x)
            fn("fn-wrap-discard", ["car", "fn-serve"]),                       # (car (fn-serve x)): drops the state
            fn("fn-wrap-effect", ["fn-serve", "fn-bump"]),                    # (fn-serve (fn-bump x))
            fn("fn-wrap-shape", ["fn-shape"], alias=("fn-shape", ["x"])),     # alias of a callee with a shape lemma only
            fn("fn-shape", [IF, "fn-serve-refusal"]),
            # undeclared: a one-call wrapper of a decision entry is not a delegation by shape
            fn("fn-wrap-plain", ["fn-serve"], alias=("fn-serve", ["x"])),
            fn("fn-wrap-plain-invert", ["not", "fn-serve"]),
        ]
        world["theorems"] += [thm("fn-shape-true-listp", [], ["fn-shape"])]   # a shape lemma, cited by nothing
        interfaces = json.loads(json.dumps(INTERFACES))
        entry = lambda name, callee: {"name": name, "subsystem": "store", "class": "ideal",
                                      "keystones": [], "dispatched_from": [], "delegates": callee}
        interfaces["entries"] += [
            entry("fn-wrap-serve", "fn-serve"), entry("fn-wrap-scan", "fn-scan"),
            entry("fn-wrap-branch", "fn-serve"), entry("fn-wrap-invert", "fn-serve"),
            entry("fn-wrap-hardwire", "fn-serve"), entry("fn-wrap-reorder", "fn-serve"),
            entry("fn-wrap-discard", "fn-serve"), entry("fn-wrap-effect", "fn-serve"),
            entry("fn-wrap-shape", "fn-shape"), entry("fn-shape", None),
            entry("fn-wrap-plain", None), entry("fn-wrap-plain-invert", None),
        ]
        root = Path(tempfile.mkdtemp())
        (root / "planning").mkdir()
        (root / "build" / "coverage").mkdir(parents=True)
        for name, doc in (("interfaces", interfaces), ("proofs", PROOFS),
                          ("requirements", REQUIREMENTS), ("families", FAMILIES)):
            (root / "planning" / (name + ".json")).write_text(json.dumps(doc))
        (root / "build" / "coverage" / "world.json").write_text(json.dumps(world))
        return root, coverage.build(root / "build" / "coverage" / "world.json", root=root)

    def test_delegation_files_the_wrapper_as_plumbing_and_refuses_the_rest(self):
        root, cov = self.build()
        rows = {r["name"]: r for r in cov["entries"]}
        self.assertEqual(rows["fn-wrap-serve"]["kind"], "delegates")
        self.assertEqual(rows["fn-wrap-serve"]["delegated_direct"], ["fn-serve-answers"])
        self.assertNotIn("delegates_problem", rows["fn-wrap-serve"])
        self.assertNotIn("fn-wrap-serve", coverage.uncovered_decisions(cov))
        self.assertIn("no theorem's conclusion names", rows["fn-wrap-scan"]["delegates_problem"])
        self.assertIn("not one application", rows["fn-wrap-branch"]["delegates_problem"])
        self.assertEqual(rows["fn-wrap-branch"]["kind"], "decision")
        # the review's wrappers: every one refused, none filed as delegating
        for name, text in (("fn-wrap-invert", "not one application"),
                           ("fn-wrap-hardwire", "not one application"),
                           ("fn-wrap-reorder", "not the identity"),
                           ("fn-wrap-discard", "not one application"),
                           ("fn-wrap-effect", "not one application"),
                           ("fn-wrap-shape", "no proof target cites")):
            self.assertIn(text, rows[name]["delegates_problem"], name)
            self.assertNotEqual(rows[name]["kind"], "delegates", name)
        # wrapping a decision entry without a verified delegation is a decision
        for name in ("fn-wrap-invert", "fn-wrap-hardwire", "fn-wrap-reorder", "fn-wrap-discard",
                     "fn-wrap-effect", "fn-wrap-plain", "fn-wrap-plain-invert"):
            self.assertEqual(rows[name]["kind"], "decision", name)
            self.assertEqual(rows[name]["wraps"], ["fn-serve"], name)
            self.assertIn(name, coverage.uncovered_decisions(cov), name)
        self.assertEqual(rows["fn-wrap-serve"]["delegated_cited"], ["fn-serve-answers"])
        self.assertEqual(rows["fn-serve"]["keystone_cited"], ["fn-serve-answers"])
        coverage.write_baseline(cov, root / "planning" / "coverage-baseline.json")
        (root / "planning" / "interfaces-gaps.md").write_text(coverage.render_gaps(cov))
        problems, _notes = coverage.check(cov, root)
        self.assertEqual(sum("fn-wrap-scan" in p for p in problems), 1, problems)
        self.assertEqual(sum("fn-wrap-branch" in p for p in problems), 1, problems)
        self.assertFalse(any("fn-wrap-serve" in p for p in problems), problems)


class WorldTests(unittest.TestCase):
    def setUp(self):
        self.world = coverage.World(WORLD)

    def test_symbols_and_books(self):
        self.assertEqual(coverage.sym("ACL2::FN-SERVE"), "fn-serve")
        self.assertEqual(coverage.sym("COMMON-LISP::IF"), "if")
        self.assertEqual(coverage.sym("STD::FOO"), "std::foo")
        self.assertEqual(coverage.book_of(BOOK), "books/served.lisp")
        self.assertEqual(coverage.book_of(None), "top-level")
        self.assertEqual(coverage.book_of(":ground-zero"), "ground-zero")

    def test_only_the_trees_theorems(self):
        self.assertNotIn("std-lemma", self.world.theorems)
        self.assertIn("fn-serve-answers", self.world.theorems)

    def test_attachment_is_an_edge(self):
        self.assertIn("fn-concrete", self.world.graph["fn-abstract"])
        self.assertIn("fn-field", self.world.descendants("fn-abstract"))

    def test_ancestors_and_path(self):
        toward = self.world.ancestors("fn-serve")
        self.assertEqual(self.world.path(toward, "fn-wrap", "fn-serve"), ["fn-wrap", "fn-serve"])
        self.assertIn("fn-outer", toward)


class CoverTests(unittest.TestCase):
    def setUp(self):
        self.root = tree()
        self.cov = coverage.build(self.root / "build" / "coverage" / "world.json", "box",
                                  root=self.root)
        self.rows = {r["name"]: r for r in self.cov["entries"]}

    def test_direct_and_hyps_only(self):
        serve = self.rows["fn-serve"]
        self.assertEqual(serve["status"], "direct")
        self.assertEqual([t["theorem"] for t in serve["direct"]], ["fn-serve-answers"])
        self.assertEqual(serve["direct"][0]["proofs"], ["PRF-1"])
        self.assertEqual(serve["direct"][0]["families"], ["reply"])
        self.assertEqual([t["theorem"] for t in serve["hyps_only"]], ["fn-serve-assumed"])
        # the caller theorems are via-caller rows, one opened, one by name only
        via = serve["via_caller"]
        self.assertEqual(via["count"], 2)
        self.assertEqual(via["opened"], 1)
        self.assertEqual(via["examples"][0]["theorem"], "fn-outer-refuses")
        self.assertTrue(via["examples"][0]["opened"])
        self.assertEqual(via["examples"][0]["path"], ["fn-outer", "fn-serve"])
        self.assertEqual(via["examples"][0]["families"], ["storage-consistency"])

    def test_decision_rule(self):
        self.assertEqual(self.rows["fn-serve"]["kind"], "decision")
        self.assertIn("refus", self.rows["fn-serve"]["vocabulary"])
        # a :program forwarder whose private closure stops at the entry it calls
        wrap = self.rows["fn-wrap"]
        self.assertEqual(wrap["kind"], "decision")
        self.assertEqual(wrap["mode"], "program")
        self.assertEqual(wrap["book"], "top-level")
        self.assertEqual(self.rows["fn-field"]["kind"], "straight-line")
        self.assertEqual(self.rows["fn-codec-entry"]["kind"], "codec")
        self.assertEqual(self.rows["fn-scan"]["kind"], "branches")
        self.assertEqual(self.rows["fn-missing"]["kind"], "absent")
        self.assertEqual(self.rows["fn-route"]["kind"], "decision")  # wraps fn-serve, no verified :delegates
        self.assertEqual(self.rows["fn-route"]["wraps"], ["fn-serve"])
        self.assertIn("fn-serve", self.rows["fn-route"]["why"])

    def test_callee_only_and_nothing(self):
        # fn-abstract's attachment fn-concrete has a theorem: callee-only
        self.assertEqual(self.rows["fn-abstract"]["status"], "callee-only")
        self.assertEqual(self.rows["fn-abstract"]["callee_only"]["examples"][0]["theorem"],
                         "fn-concrete-fields")
        self.assertEqual(self.rows["fn-scan"]["status"], "nothing")
        # fn-field is a hypothesis-side conclusion: fn-serve-assumed concludes about it
        self.assertEqual(self.rows["fn-field"]["status"], "direct")

    def test_summary_and_families(self):
        counts = coverage.summary(self.cov["entries"])
        self.assertEqual(counts["all"]["declared"], 8)
        self.assertEqual(counts["all"]["decision"], 3)  # fn-serve, and fn-route/fn-wrap wrapping it
        self.assertEqual(counts["all"]["absent"], 1)
        self.assertEqual(counts["nntp/served"]["direct"], 1)
        rows = coverage.query(self.cov, "reply", None, None, True, "direct")
        self.assertNotIn("fn-serve", [r["name"] for r in rows])
        rows = coverage.query(self.cov, "storage-consistency", None, None, True, "direct")
        self.assertIn("fn-serve", [r["name"] for r in rows])
        rows = coverage.query(self.cov, "storage-consistency", None, None, True, "caller")
        self.assertNotIn("fn-serve", [r["name"] for r in rows])

    def test_check_shrink_only_baseline(self):
        cov = json.loads(json.dumps(self.cov))
        cov["rule"]["vocabulary_unmatched"] = []   # the synthetic world names few words
        # make fn-serve uncovered: drop its direct theorem
        cov["entries"][0]["direct"] = []
        (self.root / "planning" / "interfaces-gaps.md").write_text(coverage.render_gaps(cov))
        problems, _notes = coverage.check(cov, root=self.root)
        self.assertTrue(any("fn-serve has no direct theorem" in p for p in problems))
        coverage.write_baseline(cov, self.root / "planning" / "coverage-baseline.json")
        problems, _notes = coverage.check(cov, root=self.root)
        self.assertEqual(problems, [])
        # a stale gaps file is refused; a declared entry beyond the coverage is a note
        (self.root / "planning" / "interfaces-gaps.md").write_text("old")
        problems, _notes = coverage.check(cov, root=self.root)
        self.assertTrue(any("interfaces-gaps.md" in p for p in problems))
        doc = json.loads((self.root / "planning" / "interfaces.json").read_text())
        doc["entries"].append({"name": "fn-new", "subsystem": "web", "class": "program",
                               "keystones": [], "dispatched_from": []})
        (self.root / "planning" / "interfaces.json").write_text(json.dumps(doc))
        (self.root / "planning" / "interfaces-gaps.md").write_text(coverage.render_gaps(cov))
        problems, notes = coverage.check(cov, root=self.root)
        self.assertEqual(problems, [])
        self.assertTrue(any("fn-new" in n for n in notes))

    def test_families_must_file_every_requirement(self):
        doc = json.loads((self.root / "planning" / "families.json").read_text())
        doc["families"]["reply"]["requirements"] = ["NNT-999"]
        (self.root / "planning" / "families.json").write_text(json.dumps(doc))
        problems = coverage.Registry(self.root).problems()
        self.assertTrue(any("NNT-999" in p for p in problems))
        self.assertTrue(any("NNT-002 is filed under no family" in p for p in problems))

    def test_gaps_render_names_the_coordinate(self):
        text = coverage.render_gaps(self.cov)
        self.assertIn("box hbox", text.replace("box box", "box hbox"))
        self.assertIn("| all | 8 | 3 |", text)
        self.assertIn("`fn-missing`", text)


if __name__ == "__main__":
    unittest.main()
