"""tools/fundamentals.py: the judge reproduces the fundamentals scoreboard's
verdicts from its own committed outputs (planning/evidence/
fundamentals-2026-09-27/out, measured on 33bbfae9c), each bar is the
parameter that decides its row, and --write changes only the rows it
measured."""
from __future__ import annotations

import contextlib
import io
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import fundamentals  # noqa: E402

SCOREBOARD = ROOT / "planning" / "evidence" / "fundamentals-2026-09-27" / "out"


def bars(**over):
    a = fundamentals.main.__globals__["argparse"].Namespace(
        f1_slope_max=1.5, f1_anon_peak_mib=64, f2_r_evidence=None, f3_fsync_max=1.0, f3_design_per_post=0.125,
        f4_q_max_ms=None, f4_h_ms=None, f4_client_deadline_ms=10000, f6_bar_s=10,
        f7_reading="as-written", f8_reserved_mb=256, f8_accountable_mib=256, f8_working_set_mib=128,
        f8_reopen_mb=256, checklist=None, row_cores="20-23", f4_cores="16-19", tree=None)
    for k, v in over.items():
        setattr(a, k, v)
    return a


def rows(**over):
    a = bars(**over)
    return {j.__name__.upper(): j(SCOREBOARD, a) for j in fundamentals.JUDGES}


class ScoreboardTests(unittest.TestCase):
    def test_the_scoreboard_verdicts(self):
        r = rows()
        self.assertEqual({k: v.met for k, v in r.items()},
                         {"F1": False, "F2": False, "F3": False, "F4": False,
                          "F5": True, "F6": False, "F7": False, "F8": True})
        # F1: the scoreboard predates J2's anonymous-peak sample: not measurable, never met.
        self.assertIsNone(r["F1"].clauses[-1][1])
        # F8's split: 77.6 MiB accountable, 114.1 MiB working set, the 138 MB
        # reopen floor; the old reserved verdict stays visible and unmet.
        self.assertTrue(any("UNMET" in line for line in r["F8"].raw))
        self.assertTrue(all(v.measured for v in r.values()))

    def test_each_bar_is_its_parameter(self):
        # F6: 40k opened in 22.3 s; a 25 s bar meets it, the 10 s reading not.
        self.assertTrue(rows(f6_bar_s=25)["F6"].met)
        # F7: the alternative reading (SCN-077 on dtn) meets it on this evidence.
        self.assertTrue(rows(f7_reading="scn077-on-dtn")["F7"].met)
        # F1: a slope bar under the measured 1.27 B/octet is not met.
        self.assertFalse(rows(f1_slope_max=1.2)["F1"].met)
        # F8: 138 MB reopen floor against a 128 MB bar; 114.1 MiB working set against 100.
        self.assertFalse(rows(f8_reopen_mb=128)["F8"].met)
        self.assertFalse(rows(f8_working_set_mib=100)["F8"].met)
        self.assertFalse(rows(f8_accountable_mib=64)["F8"].met)

    def _with_floor(self, **reopen):
        import json
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        out = Path(d.name) / "out"
        shutil.copytree(SCOREBOARD, out)
        f = out / "f8-floor-prod.json"
        doc = json.loads(f.read_text())
        doc["after_reopen"].update(reopen)
        f.write_text(json.dumps(doc))
        return out

    def test_f1_judges_the_reopen_anonymous_peak(self):
        at = self._with_floor(anon_peak_kib=60 * 1024, vmsize_kib=900 * 1024)
        f1 = fundamentals.f1(at, bars())
        self.assertTrue(f1.met, f1.clauses)
        self.assertIn("virtual 900.0 MiB", f1.clauses[-1][2])
        self.assertFalse(fundamentals.f1(self._with_floor(anon_peak_kib=65 * 1024), bars()).met)
        self.assertFalse(fundamentals.f1(at, bars(f1_anon_peak_mib=59)).met)

    def test_f3_bar_is_strict_and_the_batching_gap_is_a_finding(self):
        f3 = fundamentals.f3(SCOREBOARD, bars())
        clause = f3.clauses[0]
        self.assertIn("at the named rate", clause[0])
        self.assertIn("POST/s", clause[2])
        finding = [line for line in f3.raw if "FINDING F3-G" in line]
        self.assertEqual(len(finding), 1)
        self.assertIn("OPEN", finding[0])
        # exactly the bar is not under it
        worst = float(clause[2].split("measured: ")[1].split()[0])
        self.assertFalse(fundamentals.f3(SCOREBOARD, bars(f3_fsync_max=worst)).clauses[0][1])

    def test_f6_from_the_scale_curve_judges_the_next_point_up(self):
        import json
        sys.path.insert(0, str(ROOT / "tools"))
        import scale_curve
        ns = [1000, 2000, 5000, 10000, 25000, 50000, 100000]
        # replay grows linearly (0.4 + 0.11 s per 1k), the checkpoint open more slowly.
        points = {str(n): {"n": n, "values": {
            "open_replay.s": 0.4 + 0.00011 * n, "open_checkpoint.s": 0.3 + 0.00005 * n,
            "open_checkpoint.rss_kib": 150000 + 5.0 * n, "open_checkpoint.hwm_kib": 200000 + 10.0 * n,
            "open_checkpoint.anon_peak_kib": 90000 + 4.0 * n}} for n in ns}
        curve = {"meta": {"ns": ns, "load_start": ["1"], "load_end": ["1"], "wall_s": 60}, "points": points}
        curve["fits"] = scale_curve.fit_all(curve)
        self.assertEqual(curve["fits"]["open_replay.s"]["best"], "N")
        self.assertAlmostEqual(curve["fits"]["open_replay.s"]["at_1M"], 110.4, places=3)
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "out"
            shutil.copytree(SCOREBOARD, out)
            (out / "f6-curve").mkdir()
            (out / "f6-curve" / "curve.json").write_text(json.dumps(curve))
            f6 = fundamentals.f6(out, bars())
            # 25k: 3.15 s replay; 50k: 5.9 s replay -- both under 10 s.
            self.assertTrue(f6.met, f6.clauses)
            self.assertIn("5.90 s measured at 50k", f6.clauses[1][2])
            self.assertFalse(fundamentals.f6(out, bars(f6_bar_s=5)).met)
            f8 = fundamentals.f8(out, bars())
            self.assertTrue(any("open_checkpoint.rss_kib fits N" in line for line in f8.raw), f8.raw)

    def test_f4_stays_open_until_q_max_and_h_are_named(self):
        f4 = rows()["F4"]
        unknown = [name for name, met, _ in f4.clauses if met is None]
        self.assertTrue(any(n.startswith("F4-R") for n in unknown))
        self.assertTrue(any(n.startswith("F4-W") for n in unknown))
        # Named, and generous: the hour meets F4-W (no POST lost, max 11.3 s)
        # but F4-R needs the stall case, which this run did not make.
        f4 = rows(f4_q_max_ms=4000, f4_h_ms=10000)["F4"]
        by = {n.split(":")[0]: m for n, m, _ in f4.clauses}
        self.assertTrue(by["F4-W"])
        self.assertFalse(by["F4-R"])

    def test_write_touches_only_measured_rows(self):
        with tempfile.TemporaryDirectory(dir=ROOT / "build") as tmp:
            ev = Path(tmp) / "fundamentals-test"
            shutil.copytree(SCOREBOARD, ev / "out")
            for f in ("f6-chain-20000-asis.json", "f6-chain-20000-reckpt.json",
                      "f6-t40k-2k-cp5-asis.json", "f6-t40k-2k-cp5-reckpt.json"):
                (ev / "out" / f).unlink()
            checklist = Path(tmp) / "release.md"
            shutil.copy(ROOT / "planning" / "release-v{}.md".format((ROOT / "VERSION").read_text().strip()), checklist)
            before = fundamentals.table_rows(checklist.read_text())
            a = bars(checklist=str(checklist), out=str(ev / "out"), revision="HEAD", write=True)
            with contextlib.redirect_stdout(io.StringIO()):
                fundamentals.judge(a)
            after = fundamentals.table_rows(checklist.read_text())
            self.assertEqual(after["F6"], before["F6"])
            self.assertIn("fundamentals-test/F1.md", after["F1"][4])
            self.assertEqual(after["F1"][3], "OPEN")  # no anonymous peak in that evidence
            self.assertEqual(after["F8"][3], "MET")
            self.assertEqual(after["F2"][3], "OPEN")
            self.assertFalse((ev / "F6.md").exists())
            self.assertIn("Verdict: MET", (ev / "F5.md").read_text())


if __name__ == "__main__":
    unittest.main()
