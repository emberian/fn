"""`tools/keystone_emit.py`'s toothless ledger, its shrink-only ceiling and
manifest regeneration, over small fixtures (no ACL2, no real tree)."""

from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import keystone_emit as ke  # noqa: E402

REV = "4e5a4b8bb3d8"


def entry(name, cls="hand", **more):
    return {"name": name, "class": cls, "registry": True, **more}


def base_of(*names):
    return {"entries": [entry(n) for n in names]}


class Findings(unittest.TestCase):
    def run_findings(self, current, base):
        # no committed manifest (it is regenerated into build/, never committed)
        return ke.manifest_findings({e["name"]: e for e in current}, base, REV, None)

    def test_a_new_untoothed_keystone_is_toothless_not_a_manifest_finding(self):
        current = {e["name"]: e for e in [entry("a"), entry("new")]}
        self.assertEqual(self.run_findings([entry("a"), entry("new")], base_of("a")), [])
        self.assertEqual(ke.untoothed_new(current, base_of("a")), ["new"])

    def test_a_keystone_with_teeth_is_not_toothless(self):
        current = {e["name"]: e for e in [entry("a"), entry("new", "generated", owed_met=None)]}
        self.assertEqual(ke.untoothed_new(current, base_of("a")), [])

    def test_a_base_keystone_is_not_toothless(self):
        self.assertEqual(ke.untoothed_new({"a": entry("a")}, base_of("a")), [])

    def test_teeth_declared_wrongly_still_fail(self):
        found = self.run_findings(
            [entry("a"), entry("new", "generated", owed_met=False, owed_by="lane-x")],
            base_of("a"))
        self.assertTrue(any("do not state what lane-x owes" in f for f in found), found)

    def test_a_new_deferred_mutation_is_still_a_finding(self):
        found = self.run_findings([entry("a"), entry("new", "generated", owed_met=None,
                                                     mutations="deferred")], base_of("a"))
        self.assertTrue(any("defers its mutation" in f for f in found), found)

    def test_a_downgrade_is_still_a_finding(self):
        found = self.run_findings([entry("a")], {"entries": [gen_entry("a")]})
        self.assertTrue(any("a downgrade" in f for f in found), found)


def gen_entry(name):
    return entry(name, "generated", owed_met=None)


class Ceiling(unittest.TestCase):
    def test_a_name_outside_the_set_fails_and_cites_its_ack_token(self):
        found = ke.toothless_findings(["a", "b", "c"], {"toothless": ["a", "b"]})
        self.assertEqual(len(found), 1)
        self.assertIn("new toothless keystone c", found[0])
        self.assertIn("ratchet:keystone_emit:c", found[0])

    def test_the_same_set_passes(self):
        self.assertEqual(ke.toothless_findings(["b", "a"], {"toothless": ["a", "b"]}), [])

    def test_a_swap_fails_both_ways(self):
        found = ke.toothless_findings(["a", "c"], {"toothless": ["a", "b"]})
        self.assertEqual(len(found), 2)
        self.assertTrue(any("new toothless keystone c" in f for f in found))
        self.assertTrue(any("b is in planning/teeth-ceiling.json and is no longer" in f
                            for f in found))

    def test_a_drop_without_a_write_fails(self):
        found = ke.toothless_findings(["a"], {"toothless": ["a", "b"]})
        self.assertEqual(len(found), 1)
        self.assertIn("lower the set: --write-ceiling", found[0])

    def test_a_missing_or_old_format_ceiling_fails(self):
        self.assertEqual(len(ke.toothless_findings([], {})), 1)
        self.assertEqual(len(ke.toothless_findings([], {"toothless": 3})), 1)


class WriteCeiling(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / "ceiling.json"
        self.acks = Path(self.tmp.name) / "ACKS.md"
        self.acks.write_text("")
        for patch in [mock.patch.object(ke, "CEILING", self.path),
                      mock.patch.object(ke.ratchet, "ACKS", self.acks)]:
            patch.start()
            self.addCleanup(patch.stop)

    def write(self, names):
        with contextlib.redirect_stdout(io.StringIO()):
            return ke.write_ceiling(names)

    def stored(self):
        return json.loads(self.path.read_text())["toothless"]

    def test_the_first_capture_is_allowed_and_drops_write(self):
        self.assertEqual(self.write(["b", "a", "c"]), 0)
        self.assertEqual(self.stored(), ["a", "b", "c"])
        self.assertEqual(self.write(["a"]), 0)
        self.assertEqual(self.stored(), ["a"])

    def test_adding_a_name_without_its_ack_is_refused(self):
        self.write(["a"])
        self.assertEqual(self.write(["a", "b"]), 1)
        self.assertEqual(self.stored(), ["a"])

    def test_a_swap_write_is_refused_without_the_ack(self):
        self.write(["a", "b"])
        self.assertEqual(self.write(["a", "c"]), 1)
        self.assertEqual(self.stored(), ["a", "b"])

    def test_adding_a_name_with_its_ack_passes(self):
        self.write(["a"])
        self.acks.write_text("ratchet:keystone_emit:b \u2014 a reason \u2014 lane q\n")
        self.assertEqual(self.write(["a", "b"]), 0)
        self.assertEqual(self.stored(), ["a", "b"])


def gen(name, book="tests/acl2/t.lisp", claim="c1", **more):
    return entry(name, "generated", owner_book=book, claim_digest=claim, owed_met=None, **more)


class Vanished(unittest.TestCase):
    def findings(self, current, base_entries, exists=lambda path: True):
        # no committed manifest (it is regenerated into build/, never committed)
        return ke.manifest_findings({e["name"]: e for e in current}, {"entries": base_entries},
                                    REV, None, exists)

    def test_a_base_generated_entry_that_vanishes_is_a_finding(self):
        found = self.findings([entry("a")], [gen("old"), entry("a")])
        self.assertEqual(len(found), 1)
        self.assertIn("old had generated teeth in the base (tests/acl2/t.lisp)", found[0])

    def test_a_rename_shows_as_old_gone_plus_new_generated(self):
        current = [entry("a"), gen("new")]
        self.assertEqual(self.findings(current, [gen("old"), entry("a")]), [])
        renamed, lost = ke.vanished_generated({e["name"]: e for e in current},
                                              {"entries": [gen("old")]})
        self.assertEqual((renamed, lost), ({"old": ["new"]}, []))

    def test_a_rename_into_a_different_claim_is_not_a_rename(self):
        found = self.findings([gen("new", claim="c2")], [gen("old")])
        self.assertEqual(len(found), 1)

    def test_a_rename_into_hand_is_not_a_rename(self):
        found = self.findings([entry("new")], [gen("old")])
        self.assertTrue(any("old had generated teeth" in f for f in found), found)

    def test_an_entry_whose_book_is_deleted_is_exempt(self):
        self.assertEqual(self.findings([entry("a")], [gen("old"), entry("a")],
                                       exists=lambda path: False), [])

    def test_an_entry_still_present_is_not_vanished(self):
        self.assertEqual(self.findings([gen("old")], [gen("old")]), [])


class Retired(unittest.TestCase):
    """A generated keystone deleted as a twin a different keystone supersedes
    (coordinator ruling 2026-10-11 on fn-orcs-predict-rows-at-is-the-fold)."""

    def row(self, **more):
        return {"name": "old", "owner_book": "tests/acl2/t.lisp", "superseded_by": "succ",
                "ruling": "coordinator 2026-10-11", "item": None, **more}

    def findings(self, current, base_entries, rows):
        return ke.manifest_findings({e["name"]: e for e in current}, {"entries": base_entries},
                                    REV, None, lambda path: True,
                                    retirements={r["name"]: r for r in rows})

    def test_a_row_naming_a_generated_successor_retires_the_entry(self):
        self.assertEqual(self.findings([gen("succ", claim="c9")], [gen("old"), gen("succ", claim="c9")],
                                       [self.row()]), [])

    def test_a_bare_drop_is_still_refused(self):
        found = self.findings([gen("succ", claim="c9")], [gen("old")], [])
        self.assertTrue(any("old had generated teeth" in f for f in found), found)

    def test_a_row_whose_successor_is_toothless_missing_or_itself_is_refused(self):
        for current, row, words in (
                ([entry("succ")], self.row(), "has no generated teeth now"),
                ([gen("other", claim="c9")], self.row(), "not a keystone in the current manifest"),
                ([gen("other", claim="c9")], self.row(superseded_by="old"), "not a keystone"),
                ([gen("succ", claim="c9")], self.row(ruling=" "), "names no ruling"),
                ([gen("succ", claim="c9")], self.row(owner_book="books/x.lisp"), "owner book")):
            found = self.findings(current, [gen("old")], [row])
            self.assertEqual(len(found), 1, (row, found))
            self.assertIn(words, found[0])

    def test_a_row_for_a_keystone_still_present_is_a_finding(self):
        found = self.findings([gen("old"), gen("succ", claim="c9")], [gen("old")], [self.row()])
        self.assertTrue(any("still a keystone" in f for f in found), found)

    def test_retire_writes_the_row_and_refuses_what_it_cannot_retire(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "teeth-retirements.json"
            base = {"entries": [gen("old"), entry("hand")]}
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(ke.retire("old", None, "r", None, base, path), 2)
                self.assertEqual(ke.retire("old", "old", "r", None, base, path), 2)
                self.assertEqual(ke.retire("old", "succ", "", None, base, path), 2)
                self.assertEqual(ke.retire("hand", "succ", "r", None, base, path), 2)
                self.assertEqual(ke.retire("nope", "succ", "r", None, base, path), 2)
                self.assertFalse(path.exists())
                self.assertEqual(ke.retire("old", "succ", "coordinator 2026-10-11", "IT-1", base, path), 0)
            rows = ke.load_retirements(path)
            self.assertEqual(rows["old"], {"name": "old", "owner_book": "tests/acl2/t.lisp",
                                           "superseded_by": "succ",
                                           "ruling": "coordinator 2026-10-11", "item": "IT-1"})


class WriteManifest(unittest.TestCase):
    """gate(write=True) over a fixture registry: no books, three keystones."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.proofs = self.dir / "proofs.json"
        self.manifest = self.dir / "manifest.json"
        self.set_registry(["kept", "new"])
        committed = ke.stored({n: dict(entry(n), complete=False)
                               for n in ["kept", "gone"]})
        self.manifest.write_text(json.dumps({"entries": committed}))
        self.base = base_of("kept", "gone")
        patches = [mock.patch.object(ke, "PROOFS", self.proofs),
                   mock.patch.object(ke, "MANIFEST", self.manifest),
                   mock.patch.object(ke, "COMMITTED", self.dir / "committed.json"),
                   mock.patch.object(ke, "CEILING", self.dir / "ceiling.json"),
                   mock.patch.object(ke.ledger, "load_tree",
                                     lambda lazy=True: SimpleNamespace(books={})),
                   mock.patch.object(ke, "certified_books", lambda books: {}),
                   # the fixture keystones are cited by no interface entry (the
                   # box step's build/box/interfaces.json is not read here)
                   mock.patch.object(ke.keystone_critical, "interface_index", lambda *a: {}),
                   mock.patch.object(ke, "base_manifest", lambda: (self.base, REV))]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def set_registry(self, names):
        self.proofs.write_text(json.dumps({"proofs": [{"id": "P", "events": names}]}))

    def run_gate(self, write):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            problems = ke.gate(write)
        return problems, out.getvalue()

    def written(self):
        return {e["name"] for e in json.loads(self.manifest.read_text())["entries"]}

    def set_ceiling(self, names):
        (self.dir / "ceiling.json").write_text(json.dumps({"toothless": names}))

    def test_a_new_toothless_keystone_above_the_ceiling_blocks_regeneration(self):
        self.set_ceiling([])
        problems, _ = self.run_gate(True)
        self.assertTrue(any("new toothless keystone new" in p for p in problems))
        self.assertEqual(self.written(), {"kept", "gone"})

    def test_within_the_ceiling_it_regenerates_and_prints_the_ledger(self):
        self.set_ceiling(["new"])
        problems, out = self.run_gate(True)
        self.assertEqual(problems, [])
        self.assertEqual(self.written(), {"kept", "new"})
        self.assertIn("dropped from the manifest: gone", out)
        self.assertIn("keystones without teeth: 1 (ceiling 1)", out)
        self.assertIn("toothless: new", out)

    def test_the_gate_check_alone_has_no_manifest_finding(self):
        # the manifest is regenerated into build/, never committed: an older
        # one there is not a finding (the old "stale" finding is gone)
        self.set_ceiling(["new"])
        problems, out = self.run_gate(False)
        self.assertEqual(problems, [])
        self.assertIn("toothless: new", out)
        self.assertEqual(self.written(), {"kept", "gone"})

    def test_a_committed_manifest_is_refused_and_blocks_regeneration(self):
        self.set_ceiling(["new"])
        (self.dir / "committed.json").write_text(json.dumps({"entries": []}))
        for write in (False, True):
            problems, _ = self.run_gate(write)
            self.assertEqual(len(problems), 1)
            self.assertIn("planning/teeth-obligations.json is committed again", problems[0])
        self.assertEqual(self.written(), {"kept", "gone"})


class NewWitnessClasses(unittest.TestCase):
    def test_check_cannot_scope_away_findings_even_with_write(self):
        for flags in (["--check"], ["--check", "--write"]):
            with self.subTest(flags=flags), contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as refused:
                ke.main(flags + ["--id", "PRF-10017"])
            self.assertEqual(refused.exception.code, 2)

    def test_scoped_registry_write_preserves_other_ids(self):
        form = ke.ledger.read_forms('''
          (defkeystone scoped (<= 0 (nfix x)) :id "PRF-10017"
            :subject nfix :witness ((x 1))
            :mutations ((off (:conclusion (< 1 (nfix x))) ((x 1)) :fault "off")))
        ''')[0]
        other = {"id": "PRF-001", "keystone_subjects": {"old": "f"}}
        with tempfile.TemporaryDirectory() as directory:
            proofs, events = [Path(directory) / name for name in ("proofs.json", "events.json")]
            proofs.write_text(json.dumps({"proofs": [other, {"id": "PRF-10017"}]}))
            events.write_text(json.dumps({"targets": [{"id": "PRF-001", "events": []}]}))
            with mock.patch.object(ke, "PROOFS", proofs), mock.patch.object(ke, "PROOF_EVENTS", events):
                self.assertEqual(ke.registry_findings([ke.Keystone("tests/acl2/k.lisp", 1, form)],
                                                     True, {"PRF-10017"}), [])
            self.assertEqual(json.loads(proofs.read_text())["proofs"][0], other)
            self.assertEqual(json.loads(events.read_text())["targets"][1]["events"][0]["name"], "scoped")

    def test_record_cache_failure_does_not_block_valid_registry_write(self):
        import green_check
        form = ke.ledger.read_forms('''
          (defkeystone scoped (<= 0 (nfix x)) :id "PRF-10017"
            :subject nfix :witness ((x 1))
            :mutations ((off (:conclusion (< 1 (nfix x))) ((x 1)) :fault "off")))
        ''')[0]
        out = io.StringIO()
        with mock.patch.object(ke, "forms_in", return_value=[("tests/acl2/k.lisp", 1, form)]), \
                mock.patch.object(ke, "subject_findings", return_value=([], {})), \
                mock.patch.object(ke, "registry_findings", return_value=[]) as registry, \
                mock.patch.object(ke, "gate", side_effect=green_check.CacheUnavailable("unavailable")), \
                mock.patch.object(ke, "CRITICAL", []), contextlib.redirect_stdout(out):
            self.assertEqual(ke.main(["--write"]), 1)
        self.assertTrue(any(call.args[1] for call in registry.call_args_list))
        self.assertIn("record certificate cache unavailable", out.getvalue())

    def test_register_claimed_never_allocates(self):
        form = ke.ledger.read_forms('''
          (defkeystone scoped (<= 0 (nfix x)) :id "PRF-10017"
            :subject nfix :witness ((x 1))
            :mutations ((off (:conclusion (< 1 (nfix x))) ((x 1)) :fault "off")))
        ''')[0]
        stone = ke.Keystone("tests/acl2/k.lisp", 1, form)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "proofs.json"
            path.write_text('{"proofs": []}')
            before = path.read_bytes()
            with mock.patch.object(ke, "PROOFS", path), \
                    mock.patch("next_id.read_ledger", return_value=[{
                        "id": "PRF-10017", "lane": "memory-run-launch"}]), \
                    mock.patch("next_id.claim", side_effect=AssertionError("must not allocate")), \
                    mock.patch.object(ke.ledger, "stamped_evidence", side_effect=lambda row, _: row):
                row, errors = ke.register_claimed(stone, "memory-run-launch", "M24", "Held admissions")
            self.assertEqual(errors, [])
            self.assertEqual(row["id"], "PRF-10017")
            self.assertEqual(path.read_bytes(), before)

    def test_refused_register_write_leaves_registry_bytes_unchanged(self):
        form = ke.ledger.read_forms("""
          (defkeystone scoped (<= 0 (nfix x)) :id "PRF-10017"
            :subject nfix :witness ((x 1))
            :mutations ((off (:conclusion (< 1 (nfix x))) ((x 1)) :fault "off")))
        """)[0]
        orphan = ke.ledger.read_forms(ke.ledger.source_text(form).replace(
            '"PRF-10017"', '"PRF-99999"').replace('scoped', 'orphan'))[0]
        for refusal in ("subject", "registry"):
            with self.subTest(refusal=refusal), tempfile.TemporaryDirectory() as directory:
                proofs, events = [Path(directory) / name for name in ("proofs.json", "events.json")]
                proofs.write_text('{ "proofs": [] }\n')
                events.write_text('{ "targets": [] }\n')
                before = proofs.read_bytes(), events.read_bytes()
                forms = [("tests/acl2/k.lisp", 1, form)]
                if refusal == "registry":
                    forms.append(("tests/acl2/k.lisp", 2, orphan))
                out = io.StringIO()
                with mock.patch.object(ke, "PROOFS", proofs), \
                        mock.patch.object(ke, "PROOF_EVENTS", events), \
                        mock.patch.object(ke, "forms_in", return_value=forms), \
                        mock.patch.object(ke, "subject_findings", return_value=(
                            ["subject is not host-reached"] if refusal == "subject" else [], {})), \
                        mock.patch.object(ke, "gate", return_value=[]), \
                        mock.patch.object(ke, "CRITICAL", []), \
                        mock.patch("next_id.read_ledger", return_value=[{
                            "id": "PRF-10017", "lane": "memory-run-launch"}]), \
                        mock.patch("next_id.claim", side_effect=AssertionError("must not allocate")), \
                        mock.patch.object(ke.ledger, "stamped_evidence", side_effect=lambda row, _: row), \
                        contextlib.redirect_stdout(out):
                    self.assertEqual(ke.main([
                        "--write", "--register-id", "PRF-10017", "--register-name", "scoped",
                        "--lane", "memory-run-launch", "--milestone", "M24", "--title", "Held admissions"]), 1)
                self.assertIn("--write refused", out.getvalue())
                self.assertEqual((proofs.read_bytes(), events.read_bytes()), before)
                self.assertNotIn("registered existing claim", out.getvalue())

    def test_register_write_commits_validated_row_and_citations_without_cache(self):
        import green_check
        form = ke.ledger.read_forms("""
          (defkeystone scoped (<= 0 (nfix x)) :id "PRF-10017"
            :subject nfix :witness ((x 1))
            :mutations ((off (:conclusion (< 1 (nfix x))) ((x 1)) :fault "off")))
        """)[0]
        with tempfile.TemporaryDirectory() as directory:
            proofs, events = [Path(directory) / name for name in ("proofs.json", "events.json")]
            other = {"id": "PRF-001", "keystone_subjects": {"kept": "f"}}
            proofs.write_text(json.dumps({"proofs": [other]}))
            events.write_text('{"targets": []}')
            out = io.StringIO()
            with mock.patch.object(ke, "PROOFS", proofs), \
                    mock.patch.object(ke, "PROOF_EVENTS", events), \
                    mock.patch.object(ke, "forms_in", return_value=[("tests/acl2/k.lisp", 1, form)]), \
                    mock.patch.object(ke, "subject_findings", return_value=([], {})), \
                    mock.patch.object(ke, "gate", side_effect=green_check.CacheUnavailable("unavailable")), \
                    mock.patch.object(ke, "CRITICAL", []), \
                    mock.patch("next_id.read_ledger", return_value=[{
                        "id": "PRF-10017", "lane": "memory-run-launch"}]), \
                    mock.patch("next_id.claim", side_effect=AssertionError("must not allocate")), \
                    mock.patch.object(ke.ledger, "stamped_evidence", side_effect=lambda row, _: row), \
                    contextlib.redirect_stdout(out):
                self.assertEqual(ke.main([
                    "--write", "--id", "PRF-10017", "--register-id", "PRF-10017",
                    "--register-name", "scoped", "--lane", "memory-run-launch",
                    "--milestone", "M24", "--title", "Held admissions"]), 1)
            rows = json.loads(proofs.read_text())["proofs"]
            self.assertEqual(rows[0], other)
            self.assertEqual(rows[1]["id"], "PRF-10017")
            self.assertEqual(rows[1]["keystone_subjects"], {"scoped": "nfix"})
            self.assertEqual(json.loads(events.read_text())["targets"], [{
                "id": "PRF-10017", "events": [{"kind": "theorem", "name": "scoped"}]}])
            self.assertIn("registered existing claim PRF-10017", out.getvalue())
            self.assertIn("record certificate cache unavailable", out.getvalue())

    def test_a_host_logic_subject_must_be_called_and_host_reached(self):
        graph = SimpleNamespace(books=[], hosts=["host/owner-host.lisp"],
                                book_defs={"nfix"}, known={"nfix", "host-builder"},
                                stobj_names=set(), reachable=set(), host_reachable={"host-builder"})
        for claim, called in (("(equal (host-builder x) x)", True),
                              ("(let ((unused (host-builder x))) (equal (nfix x) x))", False)):
            with self.subTest(claim=claim):
                form = ke.ledger.read_forms(
                    "(defkeystone host-claim " + claim + " :subject host-builder "
                    ":witness ((x 1)) :breaks nil :mutations "
                    "((off (:conclusion (< 1 (nfix x))) () :fault \"off\")))")[0]
                stone = ke.Keystone("tests/acl2/k.lisp", 1, form)
                with mock.patch("reach_check.Graph", return_value=graph), \
                        mock.patch("reach_check.theorem_forms", return_value={}) as read, \
                        mock.patch.object(ke, "host_line", return_value="host/owner-host.lisp:1"):
                    problems, reached = ke.subject_findings([stone])
                read.assert_called_once_with(["host/owner-host.lisp"])
                self.assertEqual(not problems, called)
                self.assertEqual(bool(reached), called)
        graph.host_reachable = set()
        with mock.patch("reach_check.Graph", return_value=graph), \
                mock.patch("reach_check.theorem_forms", return_value={}):
            problems, reached = ke.subject_findings([ke.Keystone("tests/acl2/k.lisp", 1,
                ke.ledger.read_forms("(defkeystone host-claim (equal (host-builder x) x) "
                    ":subject host-builder :witness ((x 1)) :breaks nil :mutations "
                    "((off (:conclusion (< 1 (nfix x))) () :fault \"off\")))")[0])])
        self.assertTrue(any("reached by no host line" in p for p in problems))
        self.assertEqual(reached, {})

    def test_subject_check_reads_the_claim_bindings(self):
        form = ke.ledger.read_forms('''
          (defkeystone scoped (let ((a (nfix x)))
            (implies (< 0 a) (< 1 (+ 1 a))))
            :subject nfix :witness ((x 1)) :breaks ((h1 ((x 0))))
            :mutations ((off (:conclusion (< 2 (+ 1 a))) ((x 1)) :fault "off")))
        ''')[0]
        graph = SimpleNamespace(books={}, book_defs={"nfix"}, stobj_names=set(),
                                export_of={}, reachable={"nfix"})
        with mock.patch("reach_check.Graph", return_value=graph), \
                mock.patch("reach_check.theorem_forms", return_value={}), \
                mock.patch.object(ke, "host_line", return_value="host/a.lisp:1"):
            problems, reached = ke.subject_findings([ke.Keystone("tests/acl2/k.lisp", 1, form)])
        self.assertEqual(problems, [])
        self.assertEqual(reached, {"scoped": "host/a.lisp:1"})

    def test_subject_rejects_a_variable_named_like_a_reachable_function(self):
        form = ke.ledger.read_forms('''
          (defkeystone scoped
            (let ((fn-adm-peer-open (nfix x)))
              (implies (< 0 fn-adm-peer-open) (< 1 (+ 1 fn-adm-peer-open))))
            :subject fn-adm-peer-open :witness ((x 1)) :breaks ((h1 ((x 0))))
            :mutations ((off (:conclusion (< 2 (+ 1 fn-adm-peer-open)))
                             ((x 1)) :fault "off")))
        ''')[0]
        graph = SimpleNamespace(books={}, book_defs={"nfix", "fn-adm-peer-open"},
                                stobj_names=set(), reachable={"nfix", "fn-adm-peer-open"})
        with mock.patch("reach_check.Graph", return_value=graph), \
                mock.patch("reach_check.theorem_forms", return_value={}):
            problems, reached = ke.subject_findings([ke.Keystone("tests/acl2/k.lisp", 1, form)])
        self.assertEqual(reached, {})
        self.assertEqual(len(problems), 1)
        self.assertIn("is not a function", problems[0])

    def test_subject_rejects_an_unused_bound_call(self):
        form = ke.ledger.read_forms('''
          (defkeystone scoped
            (let ((unused (fn-adm-peer-open x nil nil nil 1 1)))
              (implies (< 0 (nfix x)) (< 1 (+ 1 (nfix x)))))
            :subject fn-adm-peer-open :witness ((x 1)) :breaks ((h1 ((x 0))))
            :mutations ((off (:conclusion (< 2 (+ 1 (nfix x))))
                             ((x 1)) :fault "off")))
        ''')[0]
        graph = SimpleNamespace(books={}, book_defs={"nfix", "fn-adm-peer-open"},
                                stobj_names=set(), reachable={"nfix", "fn-adm-peer-open"})
        with mock.patch("reach_check.Graph", return_value=graph), \
                mock.patch("reach_check.theorem_forms", return_value={}):
            problems, reached = ke.subject_findings([ke.Keystone("tests/acl2/k.lisp", 1, form)])
        self.assertEqual(reached, {})
        self.assertEqual(len(problems), 1)

    def test_subject_findings_follow_declared_binders_and_literal_positions(self):
        peer = "(fn-adm-peer-open v nil nil nil 1 1)"
        store = ("(fn-prstartup-run-store-need profile core nursery output peer "
                 "workers cache-limit root resident bp-terms)")
        cases = [
            ("declared-mv-variable-is-not-a-call",
             "(<= 0 (mv-let (fn-adm-peer-open y) (mv 0 (nfix x)) "
             "(declare (ignore fn-adm-peer-open)) y))", "fn-adm-peer-open", False),
            ("declared-let-producer-is-reached",
             "(natp (let ((a " + store + ")) (declare (ignorable a)) a))",
             "fn-prstartup-run-store-need", True),
            ("lambda-unused-call-after-string-is-not-a-subject",
             '(equal ((lambda (x y) (declare (ignore y)) x) "fixed" '
             + peer + ') "fixed")', "fn-adm-peer-open", False),
            ("declared-mv-producer-is-reached",
             "(natp (mv-let (unused value) (mv 0 " + store + ") "
             "(declare (ignore unused)) value))", "fn-prstartup-run-store-need", True),
            ("plain-mv-producer-is-reached",
             "(equal (mv-let (unused value) (mv 0 " + peer + ") value) nil)",
             "fn-adm-peer-open", True),
            ("declared-let-star-producer-is-reached",
             "(natp (let* ((a " + store + ") (b a)) "
             "(declare (ignorable a)) b))", "fn-prstartup-run-store-need", True),
            ("lambda-used-call-after-string-is-reached",
             '(equal ((lambda (x y) (declare (ignore x)) y) "fixed" '
             + peer + ') nil)', "fn-adm-peer-open", True),
            ("literal-matching-a-binding-name-is-inert",
             '(let ((a ' + peer + ')) (equal ((lambda (x) x) "a") "a"))',
             "fn-adm-peer-open", False),
        ]
        defined = {"nfix", "fn-adm-peer-open", "fn-prstartup-run-store-need"}
        graph = SimpleNamespace(books={}, book_defs=defined, stobj_names=set(),
                                reachable=defined)
        for label, claim, subject, expected in cases:
            for from_theorem in (False, True):
                with self.subTest(case=label, from_theorem=from_theorem):
                    form = ke.ledger.read_forms(
                        '(defkeystone scoped ' + claim + ' :subject ' + subject
                        + ' :witness ((x 1)) :breaks nil :mutations '
                        + '((off (:conclusion (< 1 (nfix x))) ((x 1)) :fault "off")))')[0]
                    stone = ke.Keystone("tests/acl2/k.lisp", 1, form)
                    self.assertIsNotNone(stone.parts)
                    original = ke.render(form)
                    theorems = ({"scoped": ("books/k.lisp", ke.render([
                        ke.Sym("defthm"), ke.Sym("scoped"), form[2]]))}
                        if from_theorem else {})
                    with mock.patch("reach_check.Graph", return_value=graph), \
                            mock.patch("reach_check.theorem_forms", return_value=theorems), \
                            mock.patch.object(ke, "host_line", return_value="host/a.lisp:1"):
                        problems, reached = ke.subject_findings([stone])
                    self.assertEqual(ke.render(form), original)
                    if expected:
                        self.assertEqual(problems, [])
                        self.assertEqual(reached, {"scoped": "host/a.lisp:1"})
                    else:
                        self.assertEqual(reached, {})
                        self.assertEqual(len(problems), 1)
                        self.assertIn("is not a function", problems[0])

    def test_call_heads_follow_parallel_sequential_and_shadowed_bindings(self):
        parallel = ke.ledger.read_forms("(let ((a (f x)) (b (g a))) (h b))")[0]
        sequential = ke.ledger.read_forms("(let* ((a (f x)) (b (g a))) (h b))")[0]
        shadowed = ke.ledger.read_forms("(let ((a (f x))) (let ((a 0)) (h a)))")[0]
        self.assertEqual(ke.claim_call_heads(parallel), {"g", "h"})
        self.assertEqual(ke.claim_call_heads(sequential), {"f", "g", "h"})
        self.assertEqual(ke.claim_call_heads(shadowed), {"h"})

    def test_scoped_claim_preserves_labels_and_scopes_mutation(self):
        form = ke.ledger.read_forms('''
          (defteeth scoped
            :claim (let* ((y (+ 1 x)))
                     (let ((x y) (y (+ 1 y)))
                       (((positive (< 1 x))) (< 2 y))))
            :witness ((x 1)) :breaks ((positive ((x 0))))
            :mutations ((strict (:conclusion (< 3 y)) () :fault "too high")))
        ''')[0]
        parts = ke.ledger.defteeth_parts(form)
        self.assertIsNotNone(parts)
        self.assertEqual(parts["labels"], [ke.ledger.Sym("positive")])
        self.assertEqual(ke.ledger.head(parts["hyps"][0]), "let*")
        events = ke.ledger.teeth_events(parts, "defteeth")
        self.assertEqual(len(events), 4)  # witness, removal, mutation, row
        mutation_terms = events[2][1][1:]
        self.assertEqual(len(mutation_terms), 3)  # antecedent, conclusion, not mutant
        self.assertEqual(ke.ledger.head(mutation_terms[-1][-1][1]), "let*")
        form[-1][0][1][1] = ke.ledger.read_forms("(< 2 y)")[0]
        self.assertIsNone(ke.ledger.defteeth_parts(form))  # unchanged conclusion

    def test_stobj_builders_are_read_without_evaluation(self):
        parts = self.parts(extra=":stobjs ((cell (fill x cell)))")
        self.assertIsNotNone(parts)
        self.assertEqual(ke.ledger.head(parts["options"][":stobjs"][0][1]), "fill")
        self.assertIsNone(self.parts(extra=":stobjs ((cell))"))
        self.assertIsNone(self.parts(extra=":stobjs ((cell cell) (cell cell))"))
        self.assertIsNone(self.parts(extra=":stobjs ((cell cell)) :instances (run loop)"))
        self.assertIsNone(self.parts(extra=":stobjs ((cell cell)) :witness-lemma fact"))

    def test_stobj_refinements_require_stobjs_and_only_proof_hints(self):
        self.assertIsNotNone(self.parts(extra=":stobjs ((cell (fill x cell))) "
            ":stobj-checks (((p cell) (check cell) :hints ((\"Goal\" :in-theory nil))))"))
        self.assertIsNone(self.parts(extra=":stobj-checks (((p cell) (check cell)))"))
        self.assertIsNone(self.parts(extra=":stobjs ((cell (fill x cell))) "
            ":stobj-checks (((p cell) (check cell) :rule-classes nil))"))

    def parts(self, removal="(:assumption assumed)", extra=""):
        return ke.ledger.defteeth_parts(ke.ledger.read_forms(f"""
          (defteeth example :claim (((trust (assumed x))) (equal x 1))
            :witness ((x 1)) {extra}
            :breaks ((trust {removal}))
            :mutations ((two (:conclusion (equal x 2)) () :fault "wrong value")))
        """)[0])

    def test_assumption_has_its_own_removal_class_and_no_assertion(self):
        parts = self.parts()
        self.assertIsNotNone(parts)
        self.assertEqual(str(ke.ledger._dk_removal_kind(parts["breaks"]["trust"])),
                         ":assumption")
        events = ke.ledger.teeth_events(parts, "defteeth")
        assertions = [e for e in events if ke.ledger.head(e) == "assert-event"]
        self.assertEqual(len(assertions), 2)  # whole witness + mutation
        self.assertNotIn("without TRUST", ke.ledger.source_text(events))

    def test_assumptions_do_not_invent_must_fail_events(self):
        parts = self.parts(extra=":must-fail t")
        self.assertEqual(ke.ledger.defteeth_names(parts)["without"], [])
        events = ke.ledger.teeth_events(parts, "defteeth")
        local = [e for e in events if ke.ledger.head(e) == "local"]
        self.assertEqual(len(local), 1)  # the mutation only

    def test_bad_assumption_syntax_is_not_a_declaration(self):
        for removal in ("(:assumption)", "(:assumption nil)",
                        "(:assumption (f x))", "(:assumption f extra)"):
            with self.subTest(removal=removal):
                self.assertIsNone(self.parts(removal))

    def test_instance_is_recorded_separately_from_executable(self):
        parts = self.parts(extra=":instances (run run-loop)")
        row = ke.ledger.teeth_row(parts, "defteeth")[3][1]
        self.assertEqual(str(ke.ledger.keyword_plist(row)[":witness"]), ":instance")
        self.assertIsNone(self.parts(extra=":instances (run)"))
        self.assertIsNone(self.parts(extra=":instances (run loop) :witness-lemma fact"))

    def test_unguarded_witness_needs_stobjs_and_is_its_own_mode(self):
        stobjs = ":stobjs ((cell (fill x cell))) "
        self.assertIsNone(self.parts(extra=':witness-unguarded "a defun-sk guard"'))
        self.assertIsNone(self.parts(extra=stobjs + ":witness-unguarded t"))
        parts = self.parts(extra=stobjs + ':witness-unguarded "a defun-sk guard"')
        self.assertIsNotNone(parts)
        row = ke.ledger.teeth_row(parts, "defteeth")[3][1]
        self.assertEqual(str(ke.ledger.keyword_plist(row)[":witness"]), ":unguarded")
        events = ke.ledger.teeth_events(parts, "defteeth")
        self.assertEqual(ke.ledger.head(events[0][1]), "fn-dk-unguarded")
        self.assertIn("witness (unguarded: a defun-sk guard)", ke.ledger.source_text(events[0]))
        # the removal and the mutation keep their own modes
        self.assertNotIn("fn-dk-unguarded", ke.ledger.source_text(events[1:]))
        book = SimpleNamespace(teeth_declared={"example": parts}, teeth_owed={})
        tree = SimpleNamespace(books={"tests/acl2/t.lisp": book})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests/acl2").mkdir(parents=True)
            (root / "tests/acl2/t.lisp").write_text("fixture")
            proofs = root / "proofs.json"
            proofs.write_text('{"proofs": [{"events": ["example"]}]}')
            with mock.patch.object(ke, "ROOT", root), mock.patch.object(ke, "PROOFS", proofs), \
                    mock.patch.object(ke.keystone_critical, "interface_index", lambda *a: {}):
                result = ke.obligations(tree, {"tests/acl2/t.lisp": True})["example"]
        self.assertEqual(result["witness"], "unguarded")
        self.assertFalse(result["complete"])

    def test_manifest_does_not_count_assumptions_as_reachable_or_complete(self):
        parts = self.parts()
        book = SimpleNamespace(teeth_declared={"example": parts}, teeth_owed={})
        tree = SimpleNamespace(books={"tests/acl2/t.lisp": book})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests/acl2").mkdir(parents=True)
            (root / "tests/acl2/t.lisp").write_text("fixture")
            proofs = root / "proofs.json"
            proofs.write_text('{"proofs": [{"events": ["example"]}]}')
            with mock.patch.object(ke, "ROOT", root), mock.patch.object(ke, "PROOFS", proofs), \
                    mock.patch.object(ke.keystone_critical, "interface_index", lambda *a: {}):
                result = ke.obligations(tree, {"tests/acl2/t.lisp": True})["example"]
        self.assertEqual(result["removals"],
                         {"reachable": 0, "logical": 0, "lemma": 0, "assumption": 1})
        self.assertFalse(result["complete"])


class ClaimEvidenceStampTests(unittest.TestCase):
    def test_a_claimed_row_carries_the_ledger_evidence_stamp(self):
        with tempfile.TemporaryDirectory() as directory:
            proofs = Path(directory) / "proofs.json"
            proofs.write_text(json.dumps({"proofs": []}) + "\n")
            keystone = SimpleNamespace(name="k", registry_name="k", subject="s",
                                       book="books/k.lisp")
            answer = SimpleNamespace(stdout="claimed PRF-9999\n")
            with mock.patch.object(ke, "PROOFS", proofs), \
                    mock.patch.object(ke.subprocess, "run", return_value=answer):
                self.assertEqual(ke.claim(keystone, "lane", "M5", "t"), "PRF-9999")
            registry = json.loads(proofs.read_text())
            self.assertEqual(registry["proofs"][0]["evidence"], ["books/k.lisp"])
            self.assertEqual(ke.ledger.evidence_problems(registry), [])


if __name__ == "__main__":
    unittest.main()
