"""`tools/keystone_emit.py`'s owed-keystone model and manifest regeneration,
and `tools/teeth_owed_file.py`, over small fixtures (no ACL2, no real tree)."""

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
import teeth_owed_file as tof  # noqa: E402

REV = "4e5a4b8bb3d8"


def entry(name, cls="hand", **more):
    return {"name": name, "class": cls, "registry": True, **more}


def base_of(*names):
    return {"entries": [entry(n) for n in names]}


def item(name, state="open", **more):
    return {"id": tof.item_id(name), "category": "teeth-owed", "keystone": name,
            "state": state, **more}


class Findings(unittest.TestCase):
    def run_findings(self, current, base, owed):
        stored = ke.stored({e["name"]: dict(e, complete=False) for e in current})
        return ke.manifest_findings({e["name"]: e for e in current}, base, REV,
                                    {"entries": stored}, owed)

    def test_a_new_untoothed_keystone_with_no_item_is_a_finding(self):
        found = self.run_findings([entry("a"), entry("new")], base_of("a"), {})
        self.assertEqual(len(found), 1)
        self.assertIn("new is new", found[0])

    def test_an_open_item_makes_it_owed_not_a_finding(self):
        found = self.run_findings([entry("a"), entry("new")], base_of("a"),
                                  {"new": item("new")})
        self.assertEqual(found, [])

    def test_an_item_covers_only_its_own_keystone(self):
        found = self.run_findings([entry("a"), entry("new"), entry("other")], base_of("a"),
                                  {"new": item("new")})
        self.assertEqual(len(found), 1)
        self.assertIn("other is new", found[0])

    def test_a_keystone_with_teeth_leaves_the_owed_list(self):
        found = self.run_findings([entry("a"), entry("new", "generated", owed_met=None)],
                                  base_of("a"), {"new": item("new")})
        self.assertEqual(len(found), 1)
        self.assertIn("now has generated teeth", found[0])

    def test_teeth_declared_wrongly_still_fail_while_owed(self):
        found = self.run_findings(
            [entry("a"), entry("new", "generated", owed_met=False, owed_by="lane-x")],
            base_of("a"), {"new": item("new", state="open")})
        self.assertTrue(any("do not state what lane-x owes" in f for f in found), found)

    def test_an_item_for_a_name_in_no_registry_is_a_finding(self):
        found = self.run_findings([entry("a")], base_of("a"), {"ghost": item("ghost")})
        self.assertEqual(len(found), 1)
        self.assertIn("names ghost", found[0])

    def test_an_item_for_a_keystone_already_in_the_base_is_a_finding(self):
        found = self.run_findings([entry("a")], base_of("a"), {"a": item("a")})
        self.assertEqual(len(found), 1)
        self.assertIn("covers only a new keystone", found[0])


class ItemReading(unittest.TestCase):
    def test_only_open_teeth_owed_items_are_read(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for name, value in {"o": item("o"), "p": item("p", state="in-progress"),
                                "l": item("l", state="landed"), "r": item("r", state="refuted"),
                                "x": {"id": "X", "category": "other", "keystone": "x",
                                      "state": "open"}}.items():
                (directory / f"{name}.json").write_text(json.dumps(value))
            (directory / "bad.json").write_text("{")
            self.assertEqual(sorted(ke.owed_items(directory)), ["o", "p"])


class WriteManifest(unittest.TestCase):
    """gate(write=True) over a fixture registry: no books, three keystones."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        (self.dir / "items").mkdir()
        self.proofs = self.dir / "proofs.json"
        self.manifest = self.dir / "manifest.json"
        self.set_registry(["kept", "new"])
        committed = ke.stored({n: dict(entry(n), complete=False)
                               for n in ["kept", "gone"]})
        self.manifest.write_text(json.dumps({"entries": committed}))
        self.base = base_of("kept", "gone")
        patches = [mock.patch.object(ke, "PROOFS", self.proofs),
                   mock.patch.object(ke, "MANIFEST", self.manifest),
                   mock.patch.object(ke, "OWED_ITEMS", self.dir / "items"),
                   mock.patch.object(ke.ledger, "load_tree",
                                     lambda lazy=True: SimpleNamespace(books={})),
                   mock.patch.object(ke, "certified_books", lambda books: {}),
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

    def test_an_unowed_new_keystone_blocks_regeneration(self):
        problems, _ = self.run_gate(True)
        self.assertTrue(any("new is new" in p for p in problems))
        self.assertEqual(self.written(), {"kept", "gone"})

    def test_a_deleted_keystone_drops_out_and_is_printed(self):
        (self.dir / "items" / "n.json").write_text(json.dumps(item("new")))
        problems, out = self.run_gate(True)
        self.assertEqual(problems, [])
        self.assertEqual(self.written(), {"kept", "new"})
        self.assertIn("dropped from the manifest: gone", out)
        self.assertIn("1 new keystone(s) owed", out)
        self.assertIn("owed: new (TEETH-OWED-NEW", out)

    def test_the_gate_check_alone_counts_owed_and_reports_staleness(self):
        (self.dir / "items" / "n.json").write_text(json.dumps(item("new")))
        problems, out = self.run_gate(False)
        self.assertEqual(len(problems), 1)
        self.assertIn("stale", problems[0])
        self.assertIn("owed: new", out)


class Filing(unittest.TestCase):
    def sites(self, *names):
        return {n: SimpleNamespace(name=n, book=f"books/{n}.lisp", line=7,
                                   statement=[ke.Sym("equal"), ke.Sym("x"), ke.Sym("x")], local=False)
                for n in names}

    def plan(self, current, sites, open_items=None, base=None, closed=None, root=ROOT):
        return tof.plan({e["name"]: e for e in current},
                        base if base is not None else base_of("a"), sites,
                        open_items or {}, root, closed)

    def test_it_files_exactly_the_new_untoothed_class(self):
        current = [entry("a"), entry("new"), entry("done", "generated", owed_met=None)]
        files, refused, present = self.plan(current, self.sites("new"))
        self.assertEqual([i["keystone"] for i in files], ["new"])
        self.assertEqual((refused, present), ([], []))
        filed = files[0]
        self.assertEqual((filed["id"], filed["state"], filed["category"], filed["owner"]),
                         ("TEETH-OWED-NEW", "open", "teeth-owed", "unassigned"))
        self.assertEqual((filed["file"], filed["line"]), ("books/new.lisp", 7))
        self.assertIn("(equal x x)", filed["detail"])

    def test_it_is_idempotent_over_open_items(self):
        files, refused, present = self.plan([entry("a"), entry("new")], self.sites("new"),
                                            {"new": item("new")})
        self.assertEqual((files, refused, present), ([], [], ["new"]))

    def test_it_refuses_with_a_named_reason(self):
        current = [entry("a"), entry("nosite"), entry("held", owed_by="lane-q", owed_in="b.lisp"),
                   entry("shadow", registry=False), entry("closed")]
        files, refused, _ = self.plan(current, self.sites("held", "shadow", "closed"),
                                      closed={"TEETH-OWED-CLOSED": "landed"})
        self.assertEqual(files, [])
        reasons = dict(refused)
        self.assertIn("no non-local defthm", reasons["nosite"])
        self.assertIn("a different class", reasons["held"])
        self.assertIn("not a registry keystone", reasons["shadow"])
        self.assertIn("never overwrites", reasons["closed"])

    def test_it_refuses_everything_without_a_base(self):
        files, refused, _ = tof.plan({"new": entry("new")}, None, {}, {}, ROOT)
        self.assertEqual(files, [])
        self.assertIn("no protected base", refused[0][1])

    def test_the_owner_is_the_lane_the_book_header_names(self):
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "b.lisp").write_text("; header\n; (lane reclaim, 2026-10-03: x)\n")
            (Path(tmp) / "c.lisp").write_text("; nobody\n")
            self.assertEqual(tof.book_owner(Path(tmp), "b.lisp"), "reclaim")
            self.assertEqual(tof.book_owner(Path(tmp), "c.lisp"), "unassigned")
            self.assertEqual(tof.book_owner(Path(tmp), "missing.lisp"), "unassigned")

    def test_a_filed_item_is_read_back_by_the_gate_and_not_refiled(self):
        files, _, _ = self.plan([entry("a"), entry("new")], self.sites("new"))
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            tof.file_items(files, directory)
            self.assertEqual(list(ke.owed_items(directory)), ["new"])
            again, refused, present = self.plan([entry("a"), entry("new")], self.sites("new"),
                                                ke.owed_items(directory),
                                                closed=tof.existing_states(directory))
            self.assertEqual((again, refused, present), ([], [], ["new"]))
            found = ke.manifest_findings({"a": entry("a"), "new": entry("new")}, base_of("a"),
                                         REV, None, ke.owed_items(directory))
            self.assertFalse([f for f in found if "is new" in f])


if __name__ == "__main__":
    unittest.main()
