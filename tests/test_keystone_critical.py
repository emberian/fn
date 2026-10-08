"""`tools/keystone_critical.py` (Ruling 22) and its gate in `tools/keystone_emit.py`
over fixture rows: the map applies by book + interface class, a critical
keystone without the evidence package is a hard fail when new or changed and
owed when existing, a noncritical toothless one stays under the ceiling."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import keystone_critical as kc  # noqa: E402
import keystone_emit as ke  # noqa: E402

MAP = kc.load_map()

# Deputy P's classification (C8 message, 2026-10-08): keystone, class, book.
P_FIXTURE = [
    ("fn-bpnp-rotate-step-refuses-checkpoint-dropping-owed-work", "durability", "books/bp-node-rotation.lisp"),
    ("fn-bpnp-rotation-recovery-seeds-owed-jobs", "durability", "books/bp-node-rotation.lisp"),
    ("fn-bpnr-recover-from-checkpoint-equals-full-recover", "durability", "books/bp-node-rotation.lisp"),
    ("fn-bpnp-rotation-restart-keeps-owed-work", "durability", "books/bp-node-rotation.lisp"),
    ("fn-bpn-step-preserves-lifecycle-invariant", "authorization", "books/bp-node-machine-authorization.lisp"),
    ("fn-xc-span-at-is-the-returned-bytes", "identity-binding", "books/extent-cache.lisp"),
    ("fn-xc-held-token-has-one-slot", "resource-reservation", "books/extent-cache.lisp"),
    ("fn-xc-install-duplicate-is-already-held", "resource-reservation", "books/extent-cache.lisp"),
    ("fn-prl-row-sum-covers-bound-reserve", "resource-reservation", "books/page-read-ledger-rowsum.lisp"),
]


def iface(**more):
    return dict({"class": "common-lisp-compliant", "subsystem": "store", "extraction": None}, **more)


class Mapping(unittest.TestCase):
    def test_every_row_has_a_reason_and_a_known_class(self):
        for row in MAP["rows"]:
            self.assertTrue(row["why"])
            self.assertIn(row["class"], MAP["classes"])

    def test_deputy_p_fixture_classes_come_out_of_the_map(self):
        for name, cls, book in P_FIXTURE:
            self.assertEqual(kc.classify(name, book, [], MAP["rows"]), cls, name)

    def test_noncritical_controls_are_unmatched(self):
        for book in ("books/decoded-window-step-trajectory.lisp", "books/string-line-cursor.lisp",
                     "books/list-row-cursor.lisp", "books/nonexistent.lisp"):
            self.assertIsNone(kc.classify("fn-x", book, [], MAP["rows"]), book)

    def test_unknown_book_is_noncritical(self):
        self.assertIsNone(kc.classify("fn-x", None, [], MAP["rows"]))

    def test_book_and_theorem_rows_split_a_mixed_book(self):
        rows = [{"class": "resource-reservation", "book": ["books/m.lisp"], "theorem": ["a-*"], "why": "w"},
                {"class": "identity-binding", "book": ["books/m.lisp"], "why": "w"}]
        self.assertEqual(kc.classify("a-1", "books/m.lisp", [], rows), "resource-reservation")
        self.assertEqual(kc.classify("b-1", "books/m.lisp", [], rows), "identity-binding")

    def test_interface_class_and_extraction_select_by_the_citing_entry(self):
        rows = [{"class": "extraction", "extraction": True, "why": "w"},
                {"class": "parser-boundary", "book": ["books/p.lisp"], "interface_class": "program", "why": "w"},
                {"class": "durability", "book": ["books/p.lisp"], "why": "w"}]
        self.assertEqual(kc.classify("k", "books/p.lisp", [iface(extraction="extract")], rows), "extraction")
        self.assertEqual(kc.classify("k", "books/p.lisp", [iface(**{"class": "program"})], rows), "parser-boundary")
        self.assertEqual(kc.classify("k", "books/p.lisp", [iface()], rows), "durability")
        self.assertEqual(kc.classify("k", "books/p.lisp", [], rows), "durability")

    def test_a_malformed_row_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "m.json"
            path.write_text('{"classes": ["durability"], "rows": [{"class": "durability"}]}')
            with self.assertRaises(ValueError):
                kc.load_map(path)


class Marking(unittest.TestCase):
    def test_mark_critical_records_class_book_and_statement_digest(self):
        theorem = type("T", (), {"book": "books/bp-node-rotation.lisp", "statement": ["defthm", "x"]})
        tree = type("Tree", (), {"theorems": {"k": theorem, "q": type("T", (), {
            "book": "books/string-line-cursor.lisp", "statement": ["defthm", "q"]})}})
        entries = {"k": {"registry": True}, "q": {"registry": True}, "z": {"registry": False}}
        ke.mark_critical(tree, entries, MAP, {})
        self.assertEqual(entries["k"]["critical"], "durability")
        self.assertEqual(entries["k"]["book"], "books/bp-node-rotation.lisp")
        self.assertIn("statement_digest", entries["k"])
        self.assertNotIn("critical", entries["q"])
        self.assertNotIn("critical", entries["z"])


def teeth(name, **more):
    return dict({"name": name, "class": "generated", "registry": True, "critical": "durability",
                 "witness": "executable", "certified": True, "statement_digest": "d1",
                 "removals": {"reachable": 1, "logical": 0, "lemma": 0, "assumption": 0},
                 "mutations": "edits:1", "subject": "fn-s"}, **more)


class Gate(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "tests").mkdir()
        (self.root / "tests/host.lisp").write_text("(deftest host-rotation (fn-s x))")
        (self.root / "tests/trace.lisp").write_text("(deftest trace-rotation)")
        (self.root / "tests/mut.lisp").write_text("(deftest mut-rotation)")
        self.full = {"host_test": "tests/host.lisp::host-rotation",
                     "trace_witness": "tests/trace.lisp::trace-rotation",
                     "mutation": "tests/mut.lisp::mut-rotation"}

    def run_gate(self, current, base_names, declared=None, owed=None, reachable=lambda s: True,
                 base_extra=None):
        base = {"entries": [dict({"name": n, "class": "hand"}, **(base_extra or {}).get(n, {}))
                            for n in base_names]}
        return kc.findings({e["name"]: e for e in current}, base, declared or {}, owed or {},
                           reachable, self.root)

    def test_new_critical_without_the_package_is_a_hard_fail(self):
        found, summary = self.run_gate([teeth("k")], [])
        self.assertEqual(summary["new_or_changed"], 1)
        self.assertTrue(any("HARD FAIL" in f and "host_test" in f and "trace_witness" in f
                            and "mutation" in f for f in found), found)

    def test_new_critical_with_the_whole_package_passes(self):
        found, summary = self.run_gate([teeth("k")], [], {"k": self.full})
        self.assertEqual(found, [])
        self.assertEqual(summary["complete"], 1)

    def test_a_new_critical_cannot_hide_in_the_owed_list(self):
        found, _ = self.run_gate([teeth("k")], [], owed={"k": {"item": "PRF-1"}})
        self.assertTrue(any("HARD FAIL" in f for f in found))
        self.assertTrue(any("cannot be owed" in f for f in found), found)

    def test_each_missing_part_is_named(self):
        for part, why in (("host_test", "host_test"), ("trace_witness", "trace_witness"),
                          ("mutation", "mutation")):
            declared = {k: v for k, v in self.full.items() if k != part}
            found, _ = self.run_gate([teeth("k")], [], {"k": declared})
            self.assertTrue(any(why + " (" in f for f in found), (part, found))

    def test_a_declared_test_that_does_not_exist_or_misses_the_subject_fails(self):
        for edit in ({"host_test": "tests/gone.lisp::host-rotation"},
                     {"host_test": "tests/host.lisp::absent-marker"},
                     {"trace_witness": "elsewhere/trace.lisp::trace-rotation"}):
            found, _ = self.run_gate([teeth("k")], [], {"k": dict(self.full, **edit)})
            self.assertTrue(any("HARD FAIL" in f for f in found), edit)
        (self.root / "tests/host.lisp").write_text("(deftest host-rotation)")
        found, _ = self.run_gate([teeth("k")], [], {"k": self.full})
        self.assertTrue(any("never mentions the subject" in f for f in found), found)

    def test_a_subject_no_host_line_reaches_fails(self):
        found, _ = self.run_gate([teeth("k")], [], {"k": self.full}, reachable=lambda s: False)
        self.assertTrue(any("reached by no host line" in f for f in found), found)

    def test_no_positive_witness_or_wrong_answer_witness_fails(self):
        for bad in (teeth("k", witness="lemma"), teeth("k", certified=False),
                    teeth("k", removals={"reachable": 0}, mutations="deferred"),
                    {"name": "k", "class": "hand", "registry": True, "critical": "durability"}):
            found, _ = self.run_gate([bad], [], {"k": self.full})
            self.assertTrue(any("HARD FAIL" in f for f in found), bad)

    def test_existing_critical_without_the_package_needs_an_owed_item(self):
        found, _ = self.run_gate([teeth("k")], ["k"])
        self.assertTrue(any("no owed item" in f for f in found), found)
        found, summary = self.run_gate([teeth("k")], ["k"], owed={"k": {"item": "PRF-1344"}})
        self.assertEqual((found, summary["owed"]), ([], 1))

    def test_an_owed_item_must_be_a_claimed_id(self):
        found, _ = self.run_gate([teeth("k")], ["k"], owed={"k": {"item": "later"}})
        self.assertTrue(any("no owed item" in f for f in found))

    def test_a_changed_existing_critical_loses_its_owed_cover(self):
        found, _ = self.run_gate([teeth("k", statement_digest="d2")], ["k"],
                                 owed={"k": {"item": "PRF-1344"}},
                                 base_extra={"k": {"statement_digest": "d1"}})
        self.assertTrue(any("changed" in f and "HARD FAIL" in f for f in found), found)

    def test_an_owed_name_that_gained_the_package_or_left_the_class_must_be_removed(self):
        found, _ = self.run_gate([teeth("k")], ["k"], {"k": self.full}, owed={"k": {"item": "PRF-1"}})
        self.assertTrue(any("remove it" in f for f in found), found)
        found, _ = self.run_gate([], ["k"], owed={"k": {"item": "PRF-1"}})
        self.assertTrue(any("no longer a critical" in f for f in found), found)

    def test_declaring_evidence_for_a_noncritical_name_is_a_finding(self):
        found, _ = self.run_gate([], [], {"q": self.full})
        self.assertTrue(any("not a critical registry keystone" in f for f in found))

    def test_a_noncritical_toothless_keystone_stays_under_the_ceiling(self):
        entry = {"name": "n", "class": "hand", "registry": True}
        found, summary = self.run_gate([entry], [])
        self.assertEqual((found, summary["critical"]), ([], 0))
        self.assertEqual(ke.untoothed_new({"n": entry}, {"entries": []}), ["n"])
        self.assertTrue(any("new toothless keystone n" in f
                            for f in ke.toothless_findings(["n"], {"toothless": []})))
        self.assertEqual(ke.toothless_findings(["n"], {"toothless": ["n"]}), [])

    def test_the_critical_class_is_stored_and_the_package_recomputed(self):
        self.assertNotIn("critical", ke.LIVE)
        stored = ke.stored({"k": dict(teeth("k"), complete=True)})
        self.assertEqual(stored[0]["critical"], "durability")
        self.assertNotIn("certified", stored[0])


if __name__ == "__main__":
    unittest.main()
