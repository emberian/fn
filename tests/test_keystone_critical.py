"""`tools/keystone_critical.py` (Ruling 22) and its gate in `tools/keystone_emit.py`
over fixture rows: the map applies by book + interface class, a critical
keystone without the evidence package is a hard fail when new or changed and
owed when existing, a noncritical toothless one stays under the ceiling."""

from __future__ import annotations

from pathlib import Path
import sys
import os
import subprocess
import tempfile
import unittest
from unittest import mock

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


# Run this world fixture with an existing proof_repl session containing
# books/defkeystone. It uses ACL2's actual translation and all-vars check;
# Python does not approximate closedness or theorem-formula equality.
OPEN_LEMMA_FIXTURE = """
(progn
 (defthm p7-critical-open-lemma (equal (car (cons x nil)) x) :rule-classes nil)
 (defthm p7-critical-closed-lemma (equal (car (cons 'a nil)) 'a) :rule-classes nil)
 (assert-event
  (equal (car (fn-dt-lemma-problem 'fixture 'p7-critical-open-lemma
                 '((x free-variable)) '(equal (car (cons x nil)) x) (w state)))
         :lemma-open))
 (assert-event
  (equal (car (fn-dt-lemma-problem 'fixture 'p7-critical-open-lemma
                 nil '(equal (car (cons x nil)) x) (w state)))
         :lemma-open))
 (assert-event
  (equal (car (fn-dt-lemma-problem 'fixture 'p7-critical-open-lemma
                 '((x 'a)) '(equal (car (cons x nil)) x) (w state)))
         :lemma-differs))
 (assert-event
  (not (fn-dt-lemma-problem 'fixture 'p7-critical-closed-lemma
                 '((x 'a)) '(equal (car (cons x nil)) x) (w state)))))
"""


class GroundLemmaWorld(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("FN_CRITICAL_PROOF_REPL"),
                         "FN_CRITICAL_PROOF_REPL names a live defkeystone proof session")
    def test_free_variable_lemma_is_refused_by_the_world(self):
        result = subprocess.run(
            [sys.executable, str(ROOT / "tools/proof_repl.py"), "send",
             os.environ["FN_CRITICAL_PROOF_REPL"], OPEN_LEMMA_FIXTURE,
             "--host", os.environ.get("FN_CRITICAL_PROOF_HOST", "persvati"), "--limit", "5"],
            capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


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


class ModelProgramReach(unittest.TestCase):
    def test_campaign_program_requires_the_existing_cut_check(self):
        import reach_check
        from tests.campaign import native_cuts
        graph = type("Graph", (), {"reachable": set(), "tied": {"fn-lgrc-program"}})()
        with mock.patch.object(reach_check, "Graph", return_value=graph):
            with mock.patch.object(native_cuts, "verify_log_cut_map") as check:
                reachable = kc.lazy_reachable()
                self.assertTrue(reachable("fn-lgrc-program"))
                self.assertTrue(reachable("fn-lgrc-program"))
                check.assert_called_once()
            with mock.patch.object(native_cuts, "verify_log_cut_map", side_effect=AssertionError("missing fence")):
                self.assertFalse(kc.lazy_reachable()("fn-lgrc-program"))
            graph.tied = {"unmapped-model"}
            self.assertFalse(kc.lazy_reachable()("unmapped-model"))
            graph.tied = set()
            self.assertFalse(kc.lazy_reachable()("fn-lgrc-program"))

    def test_open_program_requires_order_and_route_checks(self):
        import reach_check
        from tests.campaign import native_cuts
        graph = type("Graph", (), {"reachable": set(), "tied": {"fn-lg-open-program"}})()
        with mock.patch.object(reach_check, "Graph", return_value=graph), \
                mock.patch.object(native_cuts, "verify_recovery_order") as order, \
                mock.patch.object(native_cuts, "verify_log_route_arms", return_value=[]):
            self.assertTrue(kc.lazy_reachable()("fn-lg-open-program"))
            order.assert_called_once()
            with mock.patch.object(native_cuts, "verify_log_route_arms", return_value=["skipped cut"]):
                self.assertFalse(kc.lazy_reachable()("fn-lg-open-program"))
            order.side_effect = AssertionError("barrier reordered")
            self.assertFalse(kc.lazy_reachable()("fn-lg-open-program"))


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
        """BASE_NAMES: the critical base (planning/critical-base.json), each
        recorded with statement digest d1 unless BASE_EXTRA says otherwise."""
        cbase = {n: dict({"class": "durability", "statement_digest": "d1"},
                         **(base_extra or {}).get(n, {})) for n in base_names}
        return kc.findings({e["name"]: e for e in current}, cbase, declared or {}, owed or {},
                           reachable, self.root)

    def test_a_missing_critical_base_fails(self):
        found, _ = kc.findings({"k": teeth("k")}, None, {}, {}, lambda s: True, self.root)
        self.assertTrue(any("critical-base.json is missing" in f for f in found))

    def test_a_keystone_added_after_the_cutover_hard_fails_even_when_the_teeth_base_knows_it(self):
        found, _ = self.run_gate([teeth("old"), teeth("added-later")], ["old"],
                                 owed={"old": {"item": "PRF-1345"}})
        self.assertTrue(any("new durability keystone added-later" in f and "HARD FAIL" in f
                            for f in found), found)
        self.assertFalse(any("keystone old" in f for f in found), found)

    def test_a_changed_statement_of_a_based_keystone_hard_fails_and_cannot_stay_owed(self):
        found, _ = self.run_gate([teeth("k", statement_digest="d2")], ["k"],
                                 owed={"k": {"item": "PRF-1345"}})
        self.assertTrue(any("changed durability keystone k" in f and "HARD FAIL" in f
                            for f in found), found)
        self.assertTrue(any("cannot be owed" in f for f in found), found)

    def test_an_unchanged_based_keystone_with_an_owed_item_passes(self):
        found, summary = self.run_gate([teeth("k")], ["k"], owed={"k": {"item": "PRF-1345"}})
        self.assertEqual((found, summary["owed"]), ([], 1))

    def test_write_critical_base_is_written_once(self):
        old = kc.CBASE
        try:
            kc.CBASE = self.root / "critical-base.json"
            self.assertEqual(kc.write_critical_base({"k": teeth("k")}), 0)
            self.assertEqual(kc.load_critical_base()["k"]["statement_digest"], "d1")
            self.assertEqual(kc.write_critical_base({"k": teeth("k")}), 1)
        finally:
            kc.CBASE = old

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
        for bad in (teeth("k", witness="prose"), teeth("k", certified=False),
                    teeth("k", witness="lemma", certified=False),
                    teeth("k", removals={"reachable": 0}, mutations="deferred"),
                    {"name": "k", "class": "hand", "registry": True, "critical": "durability"}):
            found, _ = self.run_gate([bad], [], {"k": self.full})
            self.assertTrue(any("HARD FAIL" in f for f in found), bad)

    def test_campaign_reach_alone_does_not_supply_a_native_host_test(self):
        def reachable(subject):
            return True
        reachable.campaign_tied = lambda subject: True
        found, _ = self.run_gate([teeth("k")], [], {"k": self.full}, reachable=reachable)
        self.assertTrue(any("requires a native campaign" in f for f in found), found)
        native = self.root / "tests/test_native_cuts.py"
        # A native-looking filename and a static verifier are not execution.
        native.write_text("# fn-s\ndef host_rotation():\n    verify_log_cut_map()\n")
        full = dict(self.full, host_test="tests/test_native_cuts.py::host_rotation")
        found, _ = self.run_gate([teeth("k")], [], {"k": full}, reachable=reachable)
        self.assertTrue(any("does not drive fault cuts" in f for f in found), found)
        native.write_text("# fn-s\nimport subprocess\ndef host_rotation():\n"
                          "    'FN_NATIVE_LOG_FAULT'\n    subprocess.run(['fn-host'])\n")
        found, _ = self.run_gate([teeth("k")], [], {"k": full}, reachable=reachable)
        self.assertTrue(any("does not drive fault cuts" in f for f in found), found)
        native.write_text("# fn-s\nimport subprocess\ndef launch(fault):\n"
                          "    return subprocess.run(['fn-host'], env={'FN_NATIVE_LOG_FAULT': fault})\n"
                          "def host_rotation():\n    return launch(fault='log-copy-fenced')\n")
        found, summary = self.run_gate([teeth("k")], [], {"k": full}, reachable=reachable)
        self.assertEqual((found, summary["complete"]), ([], 1))
        # Static verification elsewhere in a native module is still not the test.
        native.write_text(native.read_text() + "def table_only():\n    verify_log_cut_map()\n")
        found, _ = self.run_gate([teeth("k")], [], {"k": dict(full,
                                 host_test="tests/test_native_cuts.py::table_only")}, reachable=reachable)
        self.assertTrue(any("does not drive fault cuts" in f for f in found), found)

    def test_positive_witness_kind_and_current_certification_are_distinct(self):
        for mode in ("executable", "instance", "lemma"):
            with self.subTest(mode=mode):
                entry = teeth("k", witness=mode, certified=False)
                pkg = kc.package(entry, self.full, lambda s: True, self.root)
                self.assertEqual(pkg["premises"],
                                 "positive witness book is not certified at its current closure key")
                found, _ = self.run_gate([entry], [], {"k": self.full})
                self.assertTrue(any("HARD FAIL" in f for f in found), found)
                found, summary = self.run_gate([dict(entry, certified=True)], [], {"k": self.full})
                self.assertEqual((found, summary["complete"]), ([], 1))
        pkg = kc.package(teeth("k", witness="prose"), self.full, lambda s: True, self.root)
        self.assertEqual(pkg["premises"], "no executable/instance/ground-lemma positive witness")

    def test_certified_ground_lemma_needs_the_same_full_package(self):
        # ACL2's defteeth checks exact closed formula equality for this mode;
        # a quantified crash-image predicate cannot be executed by assert-event.
        entry = teeth("k", witness="lemma", removals={"lemma": 1})
        found, summary = self.run_gate([entry], [], {"k": self.full})
        self.assertEqual((found, summary["complete"]), ([], 1))
        for absent in ("trace_witness", "host_test", "mutation"):
            declared = {k: v for k, v in self.full.items() if k != absent}
            found, _ = self.run_gate([entry], [], {"k": declared})
            self.assertTrue(any(absent + " (" in f for f in found), found)
        # A logical removal alone still does not establish a wrong answer on
        # a reachable path: this case must supply an edit mutation.
        found, _ = self.run_gate([dict(entry, mutations="deferred")], [], {"k": self.full})
        self.assertTrue(any("wrong_answer (" in f for f in found), found)

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
                                 owed={"k": {"item": "PRF-1344"}})
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


class LowerStale(unittest.TestCase):
    def test_a_stale_row_is_dropped_a_live_one_kept_nothing_added(self):
        current = {"live": teeth("live"), "demoted": {"name": "demoted", "registry": True}}
        cbase = {n: {"class": "durability", "statement_digest": "d1"} for n in ("live", "demoted", "gone")}
        owed = {n: {"class": "durability", "item": "PRF-1345"} for n in ("live", "demoted", "gone")}
        new_base, new_owed, dropped = kc.lower_stale(current, cbase, owed)
        self.assertEqual((sorted(new_base), sorted(new_owed)), (["live"], ["live"]))
        self.assertEqual(sorted(dropped["owed:durability"]), ["demoted", "gone"])
        self.assertEqual(sorted(dropped["base:durability"]), ["demoted", "gone"])
        self.assertEqual(new_owed["live"], owed["live"])

    def test_retire_line_names_the_witness_files(self):
        line = kc.retire_line("fn-k", {"owner_book": "tests/acl2/k-tests.lisp"},
                              {"host_test": "tests/test_native_k.py::t", "trace_witness": "tests/acl2/k-tests.lisp::w",
                               "mutation": "tests/acl2/k-tests.lisp::m"})
        self.assertEqual(line, "completed fn-k: premises/wrong_answer tests/acl2/k-tests.lisp; "
                               "host_test tests/test_native_k.py::t; trace_witness tests/acl2/k-tests.lisp::w; "
                               "mutation tests/acl2/k-tests.lisp::m")

    def test_lower_complete_drops_only_current_full_packages(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "tests").mkdir()
            (root / "tests/evidence.py").write_text("# fn-s host trace mutation")
            full = {key: "tests/evidence.py::" + marker for key, marker in
                    (("host_test", "host"), ("trace_witness", "trace"), ("mutation", "mutation"))}
            owed = {n: {"class": "durability", "item": "PRF-1345"} for n in
                    ("complete", "uncertified", "missing-host", "gone")}
            current = {n: teeth(n) for n in owed if n != "gone"}
            current["uncertified"]["certified"] = False
            declared = {n: dict(full) for n in current}
            del declared["missing-host"]["host_test"]
            kept, dropped = kc.lower_complete(current, owed, declared, lambda s: True, root)
            self.assertEqual(dropped, ["complete"])
            self.assertEqual(kept, {n: row for n, row in owed.items() if n != "complete"})
            self.assertEqual(kc.lower_complete(current, kept, declared, lambda s: True, root),
                             (kept, []))

    def test_a_new_critical_is_never_added(self):
        current = {"fresh": teeth("fresh")}
        new_base, new_owed, dropped = kc.lower_stale(current, {}, {})
        self.assertEqual((new_base, new_owed, dropped), ({}, {}, {}))


if __name__ == "__main__":
    unittest.main()
