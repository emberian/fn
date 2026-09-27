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
        f1_slope_max=1.5, f1_reopen_mb=128, f1_reopen="hwm", f2_r_evidence=None, f3_fsync_max=1.0,
        f4_q_max_ms=None, f4_h_ms=None, f4_client_deadline_ms=10000, f6_bar_s=10,
        f7_reading="as-written", f8_reserved_mb=256, f8_in_use_mb=128, f8_in_use="rss",
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
                         {"F1": True, "F2": False, "F3": False, "F4": False,
                          "F5": True, "F6": False, "F7": False, "F8": False})
        self.assertTrue(all(v.measured for v in r.values()))

    def test_each_bar_is_its_parameter(self):
        # F6: 40k opened in 22.3 s; a 25 s bar meets it, the 10 s reading not.
        self.assertTrue(rows(f6_bar_s=25)["F6"].met)
        # F7: the alternative reading (SCN-077 on dtn) meets it on this evidence.
        self.assertTrue(rows(f7_reading="scn077-on-dtn")["F7"].met)
        # F1: a slope bar under the measured 1.27 B/octet is not met.
        self.assertFalse(rows(f1_slope_max=1.2)["F1"].met)
        # F8: 138 MB reopen floor against a 128 MB bar.
        self.assertFalse(rows(f8_reserved_mb=2000, f8_reopen_mb=128)["F8"].met)
        self.assertTrue(rows(f8_reserved_mb=2000)["F8"].met)

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
            shutil.copy(ROOT / "planning" / "release-v6.7.0.md", checklist)
            before = fundamentals.table_rows(checklist.read_text())
            a = bars(checklist=str(checklist), out=str(ev / "out"), revision="HEAD", write=True)
            with contextlib.redirect_stdout(io.StringIO()):
                fundamentals.judge(a)
            after = fundamentals.table_rows(checklist.read_text())
            self.assertEqual(after["F6"], before["F6"])
            self.assertIn("fundamentals-test/F1.md", after["F1"][4])
            self.assertEqual(after["F1"][3], "MET")
            self.assertEqual(after["F2"][3], "OPEN")
            self.assertFalse((ev / "F6.md").exists())
            self.assertIn("Verdict: MET", (ev / "F5.md").read_text())


if __name__ == "__main__":
    unittest.main()
