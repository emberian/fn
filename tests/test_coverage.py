"""tools/coverage.py: what the world says about an entry, and the decision rule.

A synthetic world dump (the shape tools/coverage_dump.lisp writes) with a
small call graph, and the registries a tree would have around it.
"""
from __future__ import annotations

import json
import os
import subprocess
from unittest import mock
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
    """`coverage.py dump` (obstructions-6 item 46): remote_check ships the tree,
    then one bare ACL2 on the LOAD-ONLY launcher reads the umbrella, the host
    files, the dumper and the dump."""

    def test_the_session_is_umbrella_host_lds_dumper_dump(self):
        session = coverage.dump_session("/abs/world.json").splitlines()
        self.assertEqual(session[0], '(ld "image-world.lisp")')
        self.assertTrue(session[1].startswith("(if (boundp-global 'fn-image-world-books"))
        lds = [line for line in session if line.startswith('(ld "../host/')]
        self.assertGreater(len(lds), 10)
        announce = session.index(lds[0]) - 1
        self.assertIn(coverage.DUMP_LD, session[announce])
        self.assertIn(lds[0].split('"')[1], session[announce])
        self.assertEqual(session[-4:], ['(ld "../tools/coverage_dump.lisp")',
                                        '(cov-dump "/abs/world.json" state)',
                                        f'(value-triple (cw "{coverage.DUMP_DONE}~%"))',
                                        "(good-bye)"])
        bare = coverage.dump_session("/abs/w.json", with_host=False).splitlines()
        self.assertFalse(any("../host/" in line for line in bare))

    def test_findings_name_the_host_file_and_tls_exhaustion(self):
        out = (f"{coverage.DUMP_LD} ../host/a.lisp\n{coverage.DUMP_LD} ../host/b.lisp\n"
               "Thread local storage exhausted.\n")
        findings, world, done = coverage.dump_findings(out)
        self.assertEqual((world, done), (False, False))
        self.assertTrue(findings[0].startswith("in ../host/b.lisp: Thread local storage"))
        findings, world, done = coverage.dump_findings(
            f"{coverage.DUMP_WORLD_OK}\n{coverage.DUMP_DONE}\n")
        self.assertEqual((findings, world, done), ([], True, True))

    def test_here_refuses_without_the_load_launcher_or_the_certificate(self):
        import io, contextlib
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("FN_LOAD_ACL2", None)
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                self.assertEqual(coverage.dump_here(Path("/tmp/x.json"), True, 5), 2)
            self.assertIn("FN_LOAD_ACL2 is unset", err.getvalue())

    def test_here_installs_the_umbrella_set_first_and_moves_a_partial_dump_aside(self):
        import io, contextlib, subprocess
        calls = []
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "world.json"

            def run(argv, **kwargs):
                calls.append(argv)
                if "install-set" in argv:
                    return subprocess.CompletedProcess(argv, 0, b"installed 700 missing 0")
                out.write_text("{}")
                return subprocess.CompletedProcess(
                    argv, 0, f"{coverage.DUMP_WORLD_OK}\nACL2 Error in X\n".encode())
            env = {"FN_LOAD_ACL2": "/l/tls256k", "FN_ACL2": "/l/tls64k"}
            with mock.patch.dict(os.environ, env), \
                    mock.patch.object(Path, "is_file", lambda self: True
                                      if self.name == "image-world.cert"
                                      else os.path.isfile(self)), \
                    contextlib.redirect_stderr(io.StringIO()) as err:
                code = coverage.dump_here(out, True, 5, run=run)
            self.assertEqual(code, 1)
            self.assertEqual(calls[0][-4:], ["--acl2", "/l/tls64k", "install-set",
                                             "books/image-world"])
            self.assertFalse(out.exists())
            self.assertTrue((Path(directory) / "world.partial.json").exists())
            self.assertIn("FAIL in tools/coverage_dump.lisp", err.getvalue())

    def test_host_drives_remote_check_with_the_load_only_launcher(self):
        import io, contextlib, subprocess
        from types import SimpleNamespace
        calls = []

        def run(argv, **kwargs):
            calls.append(argv)
            return subprocess.CompletedProcess(argv, 1)
        args = SimpleNamespace(host="persvati", out=str(coverage.DEFAULT_WORLD),
                               timeout=1800, no_host_files=False)
        with contextlib.redirect_stderr(io.StringIO()) as err:
            code = coverage.dump_command(args, run=run)
        self.assertEqual(code, 1)
        self.assertIn("FAILED on persvati", err.getvalue())
        argv = calls[0]
        self.assertEqual(argv[2:4], ["persvati", "--cmd"])
        self.assertIn("FN_LOAD_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls256k", argv[4])
        self.assertIn("coverage.py dump --here", argv[4])
        self.assertIn("build/coverage/world.json", argv)


class EventLagTests(unittest.TestCase):
    """Item 47: a new PRF's events count before `ledger.py --write` regenerates."""

    def test_proof_events_are_read_directly_and_the_lag_is_named(self):
        root = tree()
        (root / "planning" / "proof-events.json").write_text(json.dumps({"targets": [
            {"id": "PRF-1", "events": [{"kind": "theorem", "name": "fn-serve-answers"}]},
            {"id": "PRF-2", "events": [{"kind": "theorem", "name": "fn-outer-refuses"},
                                       {"kind": "theorem", "name": "fn-new-keystone"}]}]}))
        registry = coverage.Registry(root)
        self.assertEqual(registry.proofs_of_event["fn-new-keystone"], ["PRF-2"])
        self.assertEqual(registry.event_lag, ["PRF-2"])
        _, notes = coverage.check(None, root)
        self.assertTrue(any("lag planning/proof-events.json for 1 target(s) (PRF-2)" in note
                            and "regen the ledger" in note for note in notes), notes)

    def test_without_proof_events_proofs_json_is_read(self):
        registry = coverage.Registry(tree())
        self.assertEqual(registry.proofs_of_event["fn-serve-answers"], ["PRF-1"])
        self.assertEqual(registry.event_lag, [])


class SourceRevisionTests(unittest.TestCase):
    """Item 48: a tree without git names the dump's commit."""

    def test_no_git_requires_the_flag_and_the_flag_is_recorded(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(SystemExit) as refused:
                coverage.source_revision(None, Path(directory))
            self.assertIn("--source-revision SHA", str(refused.exception))
            self.assertEqual(coverage.source_revision("33bb1ada7", Path(directory)),
                             "33bb1ada7")
            with self.assertRaises(SystemExit):
                coverage.source_revision("HEAD~1", Path(directory))

    def test_build_records_the_named_revision(self):
        root = tree()
        cov = coverage.build(root / "build" / "coverage" / "world.json", "persvati",
                             root=root, revision="abc1234")
        self.assertEqual(cov["coordinate"]["source_revision"], "abc1234")
        self.assertEqual(cov["coordinate"]["box"], "persvati")


class LoadOnlyTests(unittest.TestCase):
    """The tls256k launcher loads; it never certifies (item 46)."""

    def test_load_only_launcher_is_not_a_certifying_one(self):
        import farm
        for box, host in farm.HOSTS.items():
            self.assertIn("tls256k", host["load_acl2"], box)
            self.assertNotEqual(host["load_acl2"], host["acl2"], box)
            self.assertNotEqual(host["load_acl2"], host["image_acl2"], box)

    def test_only_load_sessions_name_it(self):
        users = subprocess.run(["git", "grep", "-lF", '"load_acl2"', "--", "tools"],
                               cwd=ROOT, capture_output=True, text=True).stdout.split()
        self.assertEqual(sorted(users), ["tools/coverage.py", "tools/farm.py"])


if __name__ == "__main__":
    unittest.main()
