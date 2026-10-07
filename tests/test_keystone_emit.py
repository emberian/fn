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
        stored = ke.stored({e["name"]: dict(e, complete=False) for e in current})
        return ke.manifest_findings({e["name"]: e for e in current}, base, REV,
                                    {"entries": stored})

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
    def test_n_above_the_ceiling_fails_and_cites_the_ratchet_token(self):
        found = ke.toothless_findings(["a", "b", "c"], {"toothless": 2})
        self.assertEqual(len(found), 1)
        self.assertIn("ratchet:keystone_emit:toothless", found[0])

    def test_n_at_or_below_the_ceiling_passes(self):
        self.assertEqual(ke.toothless_findings(["a", "b"], {"toothless": 2}), [])
        self.assertEqual(ke.toothless_findings(["a"], {"toothless": 2}), [])

    def test_a_missing_ceiling_fails(self):
        self.assertEqual(len(ke.toothless_findings([], {})), 1)


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

    def write(self, n):
        with contextlib.redirect_stdout(io.StringIO()):
            return ke.write_ceiling(n)

    def stored(self):
        return json.loads(self.path.read_text())["toothless"]

    def test_the_first_capture_is_allowed_and_a_lowering_writes(self):
        self.assertEqual(self.write(5), 0)
        self.assertEqual(self.stored(), 5)
        self.assertEqual(self.write(3), 0)
        self.assertEqual(self.stored(), 3)

    def test_a_raise_without_an_ack_is_refused(self):
        self.write(3)
        self.assertEqual(self.write(4), 1)
        self.assertEqual(self.stored(), 3)

    def test_a_raise_with_the_ack_passes(self):
        self.write(3)
        self.acks.write_text("ratchet:keystone_emit:toothless \u2014 a reason \u2014 lane q\n")
        self.assertEqual(self.write(4), 0)
        self.assertEqual(self.stored(), 4)


def gen(name, book="tests/acl2/t.lisp", claim="c1", **more):
    return entry(name, "generated", owner_book=book, claim_digest=claim, owed_met=None, **more)


class Vanished(unittest.TestCase):
    def findings(self, current, base_entries, exists=lambda path: True):
        stored = ke.stored({e["name"]: dict(e, complete=False) for e in current})
        return ke.manifest_findings({e["name"]: e for e in current}, {"entries": base_entries},
                                    REV, {"entries": stored}, exists)

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
                   mock.patch.object(ke, "CEILING", self.dir / "ceiling.json"),
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

    def set_ceiling(self, n):
        (self.dir / "ceiling.json").write_text(json.dumps({"toothless": n}))

    def test_a_new_toothless_keystone_above_the_ceiling_blocks_regeneration(self):
        self.set_ceiling(0)
        problems, _ = self.run_gate(True)
        self.assertTrue(any("exceed the ceiling 0" in p for p in problems))
        self.assertEqual(self.written(), {"kept", "gone"})

    def test_within_the_ceiling_it_regenerates_and_prints_the_ledger(self):
        self.set_ceiling(1)
        problems, out = self.run_gate(True)
        self.assertEqual(problems, [])
        self.assertEqual(self.written(), {"kept", "new"})
        self.assertIn("dropped from the manifest: gone", out)
        self.assertIn("keystones without teeth: 1 (ceiling 1)", out)
        self.assertIn("toothless: new", out)

    def test_the_gate_check_alone_reports_staleness(self):
        self.set_ceiling(1)
        problems, out = self.run_gate(False)
        self.assertEqual(len(problems), 1)
        self.assertIn("stale", problems[0])
        self.assertIn("toothless: new", out)


if __name__ == "__main__":
    unittest.main()
