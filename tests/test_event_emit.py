"""tools/event_emit.py: the defevent registry and its stable-code check."""
from __future__ import annotations

import copy
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import event_emit  # noqa: E402

BASE = {"fam": {"book": "books/x.lisp", "version": 1,
                "codes": {"a": 1, "b": 2},
                "reserved": {"0": {"name": "start", "why": "a start entry"}},
                "recorded": {}, "otherwise": 0, "encode": "enc",
                "decode": "dec", "recognizer": None}}


def changed(**edit) -> dict:
    new = copy.deepcopy(BASE)
    new["fam"].update(edit)
    return new


class StabilityTests(unittest.TestCase):
    def test_unchanged_is_stable(self):
        self.assertEqual(event_emit.stability(BASE, BASE), [])

    def test_added_kind_is_stable(self):
        self.assertEqual(event_emit.stability(BASE, changed(codes={"a": 1, "b": 2, "c": 3})), [])

    def test_renumbering_needs_a_version(self):
        found = event_emit.stability(BASE, changed(codes={"a": 1, "b": 3},
                                                    reserved={"0": BASE["fam"]["reserved"]["0"],
                                                              "2": {"name": "b", "why": "old"}}))
        self.assertTrue(any("b was code 2 and is now 3" in p for p in found), found)
        bumped = event_emit.stability(BASE, changed(version=2, codes={"a": 1, "b": 3},
                                                    reserved={"0": BASE["fam"]["reserved"]["0"],
                                                              "2": {"name": "b", "why": "old"}}))
        self.assertEqual(bumped, [])

    def test_reused_code(self):
        found = event_emit.stability(BASE, changed(codes={"a": 1, "c": 2}))
        self.assertTrue(any("code 2 named b and now names c" in p for p in found), found)

    def test_retired_code_must_be_reserved(self):
        found = event_emit.stability(BASE, changed(version=2, codes={"a": 1}))
        self.assertTrue(any("code 2 (b) left :codes without a :reserved entry" in p
                            for p in found), found)

    def test_reserved_code_taken(self):
        found = event_emit.stability(BASE, changed(codes={"a": 1, "b": 2, "c": 0}, reserved={}))
        self.assertTrue(any("reserved code 0 (start) is now c" in p for p in found), found)

    def test_version_never_decreases_and_family_never_removed(self):
        self.assertTrue(event_emit.stability(changed(version=3), BASE))
        self.assertTrue(event_emit.stability(BASE, {}))


class RegistryTests(unittest.TestCase):
    def test_the_journal_families_are_read(self):
        fams = event_emit.families()
        self.assertEqual(fams["fn-otm-op"]["decode"], "fn-otm-kind-of-op")
        self.assertEqual(fams["fn-otm-op"]["reserved"]["5"]["name"], "note")
        self.assertIn("reading", fams["fn-otm-op"]["recorded"])

    def test_registry_is_current(self):
        self.assertEqual(event_emit.REGISTRY.read_text(),
                         event_emit.render(event_emit.families()))


if __name__ == "__main__":
    unittest.main()
