"""tools/coverage_gap.py: each disposition, ACKs, never-run, fail-closed inputs."""
import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

from tools import coverage_gap as cg


def main(argv):
    with contextlib.redirect_stdout(io.StringIO()):
        return cg.main(argv)

SHA = "a" * 64


class Tree:
    """A throwaway repo root plus a coordinator dir with one live lane."""

    def __init__(self, test):
        d = tempfile.TemporaryDirectory()
        test.addCleanup(d.cleanup)
        self.root = Path(d.name) / "repo"
        self.coord = Path(d.name) / "coordinator"
        self.items = []
        (self.root / "planning/repair/items").mkdir(parents=True)
        (self.root / "tests/scenarios").mkdir(parents=True)
        self.coord.mkdir()
        (Path(d.name) / "lanes/livelane").mkdir(parents=True)
        self.claims = self.coord / "claims.jsonl"
        self.claims.write_text("")
        self.lanes = Path(d.name) / "lanes"
        self.acks = self.root / "planning/repair/ACKS.md"
        self.acks.write_text("# header\n")
        self.catalog([])
        self.tiers([])

    def item(self, id, state="open", **kw):
        self.items.append(id)
        d = {"id": id, "state": state, "owner": "nobody", "notes": [], **kw}
        (self.root / f"planning/repair/items/{id}.json").write_text(json.dumps(d))

    def catalog(self, scenarios):
        (self.root / "tests/scenarios/catalog.json").write_text(json.dumps({"scenarios": scenarios}))

    def tiers(self, modules):
        rows = "".join(f"smoke\tmodule\t{m}\tPEER\twhy\n" for m in modules)
        (self.root / "tests/scenarios/tiers.tsv").write_text("# c\n" + rows)

    def claim(self, id, worker="w", op="claim"):
        with open(self.claims, "a") as f:
            f.write(json.dumps({"op": op, "id": id, "worker": worker}) + "\n")

    def run(self):
        return cg.report(self.root, str(self.claims), str(self.lanes), str(self.acks))


class Dispositions(unittest.TestCase):
    def setUp(self):
        self.t = Tree(self)

    def disp(self, id):
        r = self.t.run()
        for d, rows in r["dispositions"].items():
            if id in [i for i, _ in rows]:
                return d

    def test_landed_inflight_parked_unowned_each(self):
        t = self.t
        t.item("L", "landed", sha="abc")
        t.item("C", "open")
        t.claim("C")
        t.item("W", "in-progress", owner="livelane")
        t.item("P", "deferred", notes=["parked until the merge"])
        t.item("U", "open")
        self.assertEqual(
            [self.disp(i) for i in "L C W P U".split()],
            ["LANDED", "IN-FLIGHT", "IN-FLIGHT", "PARKED", "UNOWNED"])
        self.assertEqual(t.run()["unowned_unacked"], ["U"])

    def test_released_or_done_claim_is_not_a_hold(self):
        self.t.item("C", "open")
        self.t.claim("C")
        self.t.claim("C", op="release")
        self.assertEqual(self.disp("C"), "UNOWNED")

    def test_in_progress_owned_by_a_dead_lane_is_unowned(self):
        self.t.item("D", "in-progress", owner="reapedlane")
        self.assertEqual(self.disp("D"), "UNOWNED")

    def test_deferred_without_a_written_note_is_unowned(self):
        self.t.item("D", "deferred")
        self.assertEqual(self.disp("D"), "UNOWNED")

    def test_ack_clears_an_unowned_item(self):
        self.t.item("U", "open")
        self.t.acks.write_text("U — ember decided S152 stays — ember\n")
        r = self.t.run()
        self.assertEqual(r["unowned_unacked"], [])
        self.assertEqual(self.disp("U"), "PARKED")
        self.assertEqual(r["findings"], [])
        self.assertEqual(main(["--check", "--root", str(self.t.root), "--claims", str(self.t.claims),
                                  "--lanes", str(self.t.lanes)]), 0)

    def test_unacked_unowned_fails_check_but_plain_run_passes(self):
        self.t.item("U", "open")
        argv = ["--root", str(self.t.root), "--claims", str(self.t.claims), "--lanes", str(self.t.lanes)]
        self.assertEqual(main(["--check"] + argv), 1)
        self.assertEqual(main(argv), 0)

    def test_ack_naming_nothing_is_a_finding(self):
        self.t.acks.write_text("GHOST — r — w\n")
        r = self.t.run()
        self.assertTrue(any("GHOST" in f for f in r["findings"]))

    def test_a_ratchet_ack_names_a_baseline_row_not_an_item(self):
        self.t.acks.write_text("ratchet:loop_call_check:f.lisp \u2014 r \u2014 w\n")
        self.assertEqual(self.t.run()["findings"], [])


class FailClosed(unittest.TestCase):
    def setUp(self):
        self.t = Tree(self)

    def test_malformed_ack_line_names_file_and_line(self):
        self.t.acks.write_text("# ok\nX — only a reason\n")
        f = self.t.run()["findings"]
        self.assertTrue(any(str(self.t.acks) + ":2" in x and "malformed" in x for x in f), f)
        self.assertEqual(main(["--root", str(self.t.root), "--claims", str(self.t.claims),
                                  "--lanes", str(self.t.lanes)]), 1)

    def test_unreadable_acks_fails(self):
        self.t.acks.unlink()
        self.assertTrue(any("unreadable" in x for x in self.t.run()["findings"]))

    def test_malformed_item_json_fails(self):
        (self.t.root / "planning/repair/items/bad.json").write_text("{nope")
        self.assertTrue(any("bad.json" in x and "malformed" in x for x in self.t.run()["findings"]))

    def test_item_without_state_fails(self):
        (self.t.root / "planning/repair/items/x.json").write_text('{"id": "x"}')
        self.assertTrue(any("x.json" in x for x in self.t.run()["findings"]))

    def test_malformed_claims_row_fails_with_line(self):
        self.t.claims.write_text('{"op": "claim", "id": "A"}\nnot json\n')
        self.assertTrue(any(":2" in x for x in self.t.run()["findings"]))

    def test_missing_claims_registry_fails(self):
        r = cg.report(self.t.root, str(self.t.claims.with_name("gone.jsonl")), str(self.t.lanes),
                      str(self.t.acks))
        self.assertTrue(any("gone.jsonl" in x for x in r["findings"]))

    def test_missing_catalog_fails(self):
        (self.t.root / "tests/scenarios/catalog.json").unlink()
        self.assertTrue(any("catalog.json" in x for x in self.t.run()["findings"]))


class NeverRun(unittest.TestCase):
    def setUp(self):
        self.t = Tree(self)

    @staticmethod
    def scn(id, **impl):
        return {"id": id, "implementation": {"native": True, "test": "tests.test_native_x", **impl}}

    def test_scenario_without_a_recorded_log_is_never_run(self):
        self.t.catalog([self.scn("SCN-1"), self.scn("SCN-2", log="planning/evidence/a.log")])
        r = self.t.run()
        self.assertEqual(r["never_run_unacked"], ["SCN-1"])

    def test_non_native_scenario_is_not_in_the_matrix(self):
        self.t.catalog([{"id": "SCN-3", "implementation": {"native": False}}, {"id": "SCN-4"}])
        self.assertEqual(self.t.run()["never_run"], [])

    def test_log_present_in_the_tree_counts(self):
        (self.t.root / "l.log").write_text("ok")
        self.t.catalog([self.scn("SCN-5", log="l.log")])
        self.assertEqual(self.t.run()["never_run"], [])

    def test_module_named_by_a_cited_log_is_run_and_a_prefix_is_not(self):
        self.t.tiers(["tests.test_native_peer", "tests.test_native_peer_pull", "tests.test_native_other"])
        self.t.catalog([self.scn("SCN-9", log="planning/evidence/x/test-tests.test_native_peer_pull.log")])
        self.assertEqual(sorted(i for i, _, _ in self.t.run()["never_run"]),
                         ["tests.test_native_other", "tests.test_native_peer"])

    def test_ack_clears_never_run_and_check_exits_zero(self):
        self.t.catalog([self.scn("SCN-1")])
        self.t.acks.write_text("SCN-1 — needs the cloud image — integrator publishes images\n")
        r = self.t.run()
        self.assertEqual(r["never_run_unacked"], [])
        self.assertEqual(r["findings"], [])
        argv = ["--check", "--root", str(self.t.root), "--claims", str(self.t.claims),
                "--lanes", str(self.t.lanes)]
        self.assertEqual(main(argv), 0)
        self.t.acks.write_text("# none\n")
        self.assertEqual(main(argv), 1)


if __name__ == "__main__":
    unittest.main()
