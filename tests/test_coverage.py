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


def fn(name, callees=(), cls="COMMON-LISP-COMPLIANT", book=BOOK, attachment=None):
    return {"name": "ACL2::" + name.upper(), "book": book, "class": "KEYWORD::" + cls,
            "callees": ["ACL2::" + c.upper() if "::" not in c else c for c in callees],
            "attachment": attachment and "ACL2::" + attachment.upper(),
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
            fn("fn-wrap-serve", ["fn-serve"]),         # exactly a call of fn-serve (direct theorem)
            fn("fn-wrap-scan", ["fn-scan"]),           # exactly a call of fn-scan (no theorem)
            fn("fn-wrap-branch", [IF, "fn-serve-refusal"]),  # branches itself, over a helper
        ]
        interfaces = json.loads(json.dumps(INTERFACES))
        interfaces["entries"] += [
            {"name": "fn-wrap-serve", "subsystem": "store", "class": "ideal",
             "keystones": [], "dispatched_from": [], "delegates": "fn-serve"},
            {"name": "fn-wrap-scan", "subsystem": "store", "class": "ideal",
             "keystones": [], "dispatched_from": [], "delegates": "fn-scan"},
            {"name": "fn-wrap-branch", "subsystem": "store", "class": "ideal",
             "keystones": [], "dispatched_from": [], "delegates": "fn-serve"},
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
        self.assertIn("but calls", rows["fn-wrap-branch"]["delegates_problem"])
        self.assertEqual(rows["fn-wrap-branch"]["kind"], "decision")
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
        self.assertEqual(wrap["kind"], "straight-line")
        self.assertEqual(wrap["mode"], "program")
        self.assertEqual(wrap["book"], "top-level")
        self.assertEqual(self.rows["fn-field"]["kind"], "straight-line")
        self.assertEqual(self.rows["fn-codec-entry"]["kind"], "codec")
        self.assertEqual(self.rows["fn-scan"]["kind"], "branches")
        self.assertEqual(self.rows["fn-missing"]["kind"], "absent")
        self.assertEqual(self.rows["fn-route"]["kind"], "delegates")
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
        self.assertEqual(counts["all"]["decision"], 1)
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
        self.assertIn("| all | 8 | 1 |", text)
        self.assertIn("`fn-missing`", text)


class TwinsTests(unittest.TestCase):
    """Q7i (obstructions-3): reference <-> executable twins, and a one-sided diff."""

    TWIN_WORLD = {
        "cbd": "/box/tree/books/",
        "functions": [
            fn("car", book=None), fn("member-eq-exec", book=None),
            dict(fn("fn-x-step", callees=["fn-x-step-ref", "fn-x-step-fast"]),
                 mbe=[["ACL2::FN-X-STEP-REF", "ACL2::FN-X-STEP-FAST"],
                      ["ACL2::FN-X-STEP", "ACL2::MEMBER-EQ-EXEC"]]),
            fn("fn-x-step-ref"), fn("fn-x-step-fast"),
            fn("fn-x-decode", attachment="fn-x-decode-impl"), fn("fn-x-decode-impl"),
            fn("fn-x-tail"), fn("fn-x-tail-exec"),
            fn("create-fn-x$a"), fn("create-fn-x$c"),
            fn("fn-x-entry", callees=["fn-x-step", "fn-x-decode"]),
        ],
        "theorems": [],
    }

    def pairs(self):
        return coverage.twin_pairs(coverage.World(self.TWIN_WORLD))

    def test_pairs_come_from_mbe_defattach_and_names_inside_the_tree(self):
        found = {(p["reference"], p["executable"]): p["via"] for p in self.pairs()}
        self.assertEqual(found, {
            ("fn-x-step-ref", "fn-x-step-fast"): ["mbe in fn-x-step"],
            ("fn-x-step", "fn-x-step-fast"): ["name"],
            ("fn-x-decode", "fn-x-decode-impl"): ["defattach", "name"],
            ("fn-x-tail", "fn-x-tail-exec"): ["name"],
            ("create-fn-x$a", "create-fn-x$c"): ["name"],
        })

    def test_an_entry_shows_its_own_twins_and_those_in_its_closure(self):
        world = coverage.World(self.TWIN_WORLD)
        found = coverage.twins_of(self.pairs(), "fn-x-entry", world)
        self.assertEqual(found["own"], [])
        self.assertEqual(sorted((p["reference"], p["executable"]) for p in found["closure"]),
                         [("fn-x-decode", "fn-x-decode-impl"),
                          ("fn-x-step", "fn-x-step-fast"),
                          ("fn-x-step-ref", "fn-x-step-fast")])
        own = coverage.twins_of(self.pairs(), "fn-x-decode")
        self.assertEqual([p["executable"] for p in own["own"]], ["fn-x-decode-impl"])
        self.assertIn("own     fn-x-decode", coverage.render_twins(own))

    def git(self, root, *args):
        import subprocess
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args],
                       cwd=root, check=True, capture_output=True)

    def test_a_diff_that_changes_one_side_of_a_pair_is_flagged(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "books").mkdir()
            (root / "books/ref.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-x-tail (x)\n  (cdr x))\n')
            (root / "books/exec.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-x-tail-exec (x)\n  (cdr x))\n')
            self.git(root, "init", "-q")
            self.git(root, "add", ".")
            self.git(root, "commit", "-q", "-m", "base")
            (root / "books/ref.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-x-tail (x)\n  (cddr x))\n')
            pairs = self.pairs()
            changed = coverage.changed_definitions("HEAD", root)
            self.assertEqual(changed, {"fn-x-tail": "books/ref.lisp:2"})
            flags = coverage.one_sided(pairs, changed)
            self.assertEqual(len(flags), 1)
            self.assertIn("fn-x-tail changed (books/ref.lisp:2); its twin fn-x-tail-exec",
                          flags[0])
            # Both sides changed: nothing to flag.
            (root / "books/exec.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-x-tail-exec (x)\n  (cddr x))\n')
            self.assertEqual(coverage.one_sided(
                pairs, coverage.changed_definitions("HEAD", root)), [])
            # A deleted definition counts as changed (the old side is read).
            (root / "books/exec.lisp").write_text('(in-package "ACL2")\n')
            (root / "books/ref.lisp").write_text(
                '(in-package "ACL2")\n(defun fn-x-tail (x)\n  (cdr x))\n')
            self.assertEqual(coverage.changed_definitions("HEAD", root),
                             {"fn-x-tail-exec": "books/exec.lisp:2"})


    def test_the_cli_flags_by_default_and_refuses_only_with_strict(self):
        import contextlib, io
        from unittest import mock
        with tempfile.TemporaryDirectory() as directory:
            twins = Path(directory) / "twins.json"
            twins.write_text(json.dumps({"pairs": self.pairs()}))
            with mock.patch.object(coverage, "TWINS", twins), \
                    mock.patch.object(coverage, "changed_definitions",
                                      lambda base: {"fn-x-tail-exec": "books/exec.lisp:2"}):
                for extra, code in (([], 0), (["--strict"], 1)):
                    out = io.StringIO()
                    with contextlib.redirect_stdout(out):
                        self.assertEqual(coverage.main(["twins", "--diff", "HEAD"] + extra), code)
                    self.assertIn("1 one-sided change(s)", out.getvalue())
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    self.assertEqual(coverage.main(["twins", "fn-x-tail"]), 0)
                self.assertIn("fn-x-tail-exec", out.getvalue())


class DumpTests(unittest.TestCase):
    """`coverage.py dump --host BOX`: image-world, then the host files, then the dump."""

    def drive(self, fail_at=None):
        import subprocess
        from types import SimpleNamespace
        calls = []

        def run(argv, **kwargs):
            calls.append((argv, kwargs.get("env", {}).get("FN_LANE")))
            code = 1 if fail_at and any(fail_at in word for word in argv) else 0
            return subprocess.CompletedProcess(argv, code, stdout="", stderr="")

        with tempfile.TemporaryDirectory() as directory:
            args = SimpleNamespace(host="hbox", lane="lanex", name=None, keep=False,
                                   no_host_files=False, out=directory + "/world.json")
            import io
            import contextlib
            with contextlib.redirect_stderr(io.StringIO()) as err:
                code = coverage.dump_command(args, run=run)
        return code, calls, err.getvalue()

    def test_the_host_files_load_one_by_one_between_start_and_dump(self):
        code, calls, err = self.drive()
        self.assertEqual(code, 0, err)
        words = [argv for argv, _ in calls]
        repl = [w for w in words if w[0].endswith("python3") or "proof_repl.py" in " ".join(w)]
        self.assertEqual(repl[0][2:5], ["start", "cov-lanex", "books/image-world"])
        sent = [w[4] for w in repl if w[2] == "send"]
        self.assertTrue(sent[0].startswith("(if (boundp-global 'fn-image-world-books"))
        lds = [form for form in sent if form.startswith('(ld "../host/')]
        self.assertGreater(len(lds), 10)
        self.assertEqual(lds[0], '(ld "../host/store-host.lisp" :ld-error-action :error)')
        self.assertTrue(any("FN_IMAGE_WORLD_CLOSED" in form for form in sent))
        self.assertEqual(sent[-2], '(ld "../tools/coverage_dump.lisp")')
        self.assertEqual(sent[-1], '(cov-dump "/tank/fn/gates/lanex-repl/build/coverage/world.json" state)')
        self.assertEqual(words[-2][:2], ["scp", "-q"])
        self.assertEqual(repl[-1][2:4], ["stop", "cov-lanex"])
        self.assertTrue(all(lane == "lanex" for w, lane in calls if "proof_repl.py" in " ".join(w)))
        self.assertIn("coverage.py build --world", err)

    def test_a_failing_host_file_is_named_and_the_session_stopped(self):
        code, calls, err = self.drive(fail_at="owner-host.lisp")
        self.assertEqual(code, 1)
        self.assertIn("FAILED at ../host/owner-host.lisp", err)
        words = [argv for argv, _ in calls]
        self.assertFalse(any(w[0] == "scp" for w in words))
        self.assertFalse(any("cov-dump" in " ".join(w) for w in words))
        self.assertEqual(words[-1][2:4], ["stop", "cov-lanex"])


if __name__ == "__main__":
    unittest.main()
