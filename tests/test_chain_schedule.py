"""tools/chain_schedule.py: the load-normalised walls, the chain, the job plan."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import chain_schedule as chain  # noqa: E402


# A chain a -> b -> c of 10 s books and eight free 5 s books.
BOOKS = ["books/a", "books/b", "books/c"] + [f"books/f{i}" for i in range(8)]
GRAPH = {book: set() for book in BOOKS}
GRAPH["books/b"] = {"books/a"}
GRAPH["books/c"] = {"books/b"}
WALLS = {book: 10.0 if book in ("books/a", "books/b", "books/c") else 5.0
         for book in BOOKS}


class ChainTests(unittest.TestCase):

    def test_the_critical_chain_is_the_heaviest_path_dependencies_first(self):
        self.assertEqual(chain.critical_chain(BOOKS, GRAPH, WALLS),
                         ["books/a", "books/b", "books/c"])
        self.assertEqual(chain.critical_chain(BOOKS, GRAPH, WALLS, "books/f3"),
                         ["books/f3"])

    def test_simulation_is_bounded_below_by_the_chain_and_the_work(self):
        # 70 s of work: one job is the sum; enough jobs is the 30 s chain.
        self.assertEqual(chain.simulate(BOOKS, GRAPH, WALLS, 1), 70.0)
        self.assertEqual(chain.simulate(BOOKS, GRAPH, WALLS, 8), 30.0)
        for jobs in range(1, 12):
            wall = chain.simulate(BOOKS, GRAPH, WALLS, jobs)
            self.assertGreaterEqual(wall, max(30.0, 70.0 / jobs))

    def test_the_plan_takes_the_fewest_jobs_that_finish_the_chain(self):
        # With no slowdown three jobs already reach the chain's 30 s; more
        # only load the box.
        flat = chain.slowdown
        try:
            chain.slowdown = lambda load, host=None: 1.0
            plan = chain.choose_jobs(BOOKS, GRAPH, WALLS, 16, cpus=24)
        finally:
            chain.slowdown = flat
        self.assertEqual(plan.predicted_by_jobs[3], 30.0)
        self.assertEqual(plan.jobs, 3)

    def test_a_steep_curve_and_a_loaded_box_choose_fewer_jobs(self):
        idle = chain.choose_jobs(BOOKS, GRAPH, WALLS, 16, cpus=4, background=0.0,
                                 host="persvati")
        loaded = chain.choose_jobs(BOOKS, GRAPH, WALLS, 16, cpus=4, background=4.0,
                                   host="persvati")
        self.assertLessEqual(loaded.jobs, idle.jobs)
        best = min(idle.predicted_by_jobs.values())
        self.assertLessEqual(idle.predicted_seconds, best * (1 + chain.TOLERANCE))
        self.assertTrue(all(seconds > best * (1 + chain.TOLERANCE)
                            for jobs, seconds in idle.predicted_by_jobs.items()
                            if jobs < idle.jobs))

    def test_slowdown_is_one_below_the_knee_and_grows_after(self):
        knee, slope = chain.curve("persvati")
        self.assertEqual(chain.slowdown(knee / 2, "persvati"), 1.0)
        self.assertAlmostEqual(chain.slowdown(knee + 0.5, "persvati"), 1 + slope * 0.5)
        self.assertEqual(chain.curve("somewhere-new"), chain.DEFAULT_CURVE)

    def test_parse_jobs(self):
        self.assertEqual(chain.parse_jobs("7"), 7)
        self.assertEqual(chain.parse_jobs("auto"), ("auto", chain.DEFAULT_CEILING))
        self.assertEqual(chain.parse_jobs("auto:9"), ("auto", 9))
        for bad in ("auto:0", "auto:x", "lots"):
            with self.assertRaises(ValueError):
                chain.parse_jobs(bad)


class QuietWallTests(unittest.TestCase):

    def write(self, history: Path, stamp: str, host: str, walls: dict, loads: dict) -> None:
        (history / f"certify-{stamp}-1.json").write_text(json.dumps({
            "hostname": host, "cpu_count": 24,
            "book_wall_seconds": walls, "book_load_average": loads}))

    def test_a_wall_is_divided_by_the_slowdown_it_ran_under(self):
        with tempfile.TemporaryDirectory() as directory:
            history = Path(directory)
            load = 24 * 1.14  # load per core 1.14: persvati's s = 1 + 2.2 * 1.0
            self.write(history, "20260101T000000Z", "persvati",
                       {"books/x": 32.0}, {"books/x": [load, load]})
            walls = chain.quiet_walls(["books/x", "books/y"], history, "persvati")
            self.assertAlmostEqual(walls.seconds["books/x"],
                                   32.0 / chain.slowdown(1.14, "persvati"))
            self.assertEqual(walls.measured, 1)
            # An unmeasured book counts the median of the measured ones.
            self.assertEqual(walls.seconds["books/y"], walls.seconds["books/x"])

    def test_this_box_is_preferred_and_the_recent_runs_count(self):
        with tempfile.TemporaryDirectory() as directory:
            history = Path(directory)
            quiet = [1.0, 1.0]
            self.write(history, "20260101T000000Z", "hbox", {"books/x": 50.0},
                       {"books/x": quiet})
            for day in range(2, 2 + chain.RECENT + 2):
                self.write(history, f"202601{day:02d}T000000Z", "persvati",
                           {"books/x": 100.0 if day < 4 else 4.0}, {"books/x": quiet})
            self.assertEqual(chain.quiet_walls(["books/x"], history, "persvati")
                             .seconds["books/x"], 4.0)
            self.assertEqual(chain.quiet_walls(["books/x"], history, "hbox")
                             .seconds["books/x"], 50.0)
            # A box with no runs of its own takes every box's.
            self.assertEqual(chain.quiet_walls(["books/x"], history, "laptop")
                             .seconds["books/x"], 4.0)

    def test_a_pcert_or_unreadable_manifest_is_skipped(self):
        with tempfile.TemporaryDirectory() as directory:
            history = Path(directory)
            (history / "certify-20260101T000000Z-1.json").write_text("{not json")
            (history / "certify-20260102T000000Z-1.json").write_text(json.dumps(
                {"pcert": True, "book_wall_seconds": {"books/x": 9.0}}))
            walls = chain.quiet_walls(["books/x"], history, "persvati")
            self.assertEqual(walls.measured, 0)
            self.assertEqual(walls.seconds["books/x"], chain.UNKNOWN_SECONDS)

    def test_the_summary_cache_answers_the_same_and_follows_an_edit(self):
        # tooling-obstructions: every call re-read ~400 MB of manifests.
        with tempfile.TemporaryDirectory() as directory:
            history = Path(directory) / "h"
            history.mkdir()
            summary = Path(directory) / "summary.json"
            self.write(history, "20260101T000000Z", "persvati", {"books/x": 8.0},
                       {"books/x": [30.0, 30.0]})
            (history / "certify-20260102T000000Z-1.json").write_text("{not json")
            plain = chain.quiet_walls(["books/x"], history, "persvati")
            cached = chain.quiet_walls(["books/x"], history, "persvati", summary)
            self.assertEqual(cached, plain)
            self.assertTrue(summary.is_file())
            # A second call reads the summary, not the manifests.
            with mock.patch.object(Path, "read_text", autospec=True,
                                   side_effect=lambda path, **_: (
                                       summary.open(encoding="utf-8").read()
                                       if path == summary else self.fail(f"read {path}"))):
                self.assertEqual(chain.quiet_walls(["books/x"], history, "persvati", summary),
                                 plain)
            # An edited manifest is read again.
            self.write(history, "20260101T000000Z", "persvati", {"books/x": 2.0},
                       {"books/x": [1.0, 1.0]})
            os.utime(history / "certify-20260101T000000Z-1.json", ns=(1, 1))
            self.assertEqual(chain.quiet_walls(["books/x"], history, "persvati", summary)
                             .seconds["books/x"], 2.0)


if __name__ == "__main__":
    unittest.main()
