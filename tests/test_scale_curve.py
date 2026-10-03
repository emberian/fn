"""tools/scale_curve.py's fit, flags, table and probe registry, on synthetic
curves (no box, no image): the model it picks for a known shape, the
extrapolation, and each flag on the shape that should raise it and not on
one that should not."""
from __future__ import annotations

import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import scale_curve as sc  # noqa: E402

NS = list(sc.NS)


def curve(fn, noise=0.0, series="s.s"):
    points = {}
    for i, n in enumerate(NS):
        wobble = 1 + (noise if i % 2 else -noise)
        points[str(n)] = {"n": n, "values": {series: fn(n) * wobble}, "errors": {}}
    c = {"meta": {"ns": NS, "probes": ["s"], "jobs": 1, "cores_per_job": 2, "mem": "24G",
                  "load_start": ["1"], "load_end": ["1"], "wall_s": 1, "fixtures": "x"},
         "points": points}
    c["fits"] = sc.fit_all(c)
    return c, c["fits"][series]


class FitTests(unittest.TestCase):
    def test_each_shape_is_named_and_extrapolated(self):
        for shape, fn in (("constant", lambda n: 2.0), ("log N", lambda n: 1 + 0.5 * math.log(n)),
                          ("N", lambda n: 0.3 + 1e-4 * n), ("N log N", lambda n: 0.3 + 1e-5 * n * math.log(n)),
                          ("N^2", lambda n: 0.5 + 1e-9 * n * n)):
            _, f = curve(fn, noise=0.01)
            self.assertEqual(f["best"], shape, f)
            self.assertAlmostEqual(f["at_1M"] / fn(1e6), 1.0, delta=0.08)
            self.assertFalse([x for x in f["flags"] if not x.startswith("ambiguous")], f["flags"])
        _, f = curve(lambda n: 0.3 + 1e-4 * n)
        self.assertAlmostEqual(f["at_10M"], 0.3 + 1e-4 * 1e7, places=6)
        self.assertLess(f["residual"], 1e-9)

    def test_noise_is_not_growth(self):
        # A flat series with 10% alternating noise: the constant, not N^2.
        _, f = curve(lambda n: 4.0, noise=0.10)
        self.assertEqual(f["best"], "constant")

    def test_a_threshold_past_25k_is_a_bend(self):
        # Linear until 50k, then four times the slope: the small-N fit misses 100k.
        _, f = curve(lambda n: 0.5 + 1e-4 * n if n <= 50000 else 5.5 + 4e-4 * (n - 50000))
        self.assertTrue(any(x.startswith("bend") for x in f["flags"]), f["flags"])
        self.assertTrue(any(x.startswith("steepens") for x in f["flags"]), f["flags"])
        # A curve that FLATTENS is not a threshold suspicion (the extrapolation is pessimistic).
        _, g = curve(lambda n: 0.5 + 1e-4 * min(n, 30000))
        self.assertFalse([x for x in g["flags"] if x.startswith(("bend", "steepens"))], g["flags"])

    def test_a_known_threshold_inside_the_range_is_named_and_flagged_when_it_bends(self):
        # The automatic checkpoint at ~32,768: auto_checkpoint.* can move there.
        _, f = curve(lambda n: 1.0 if n < 32768 else 60.0, series="auto_checkpoint.ms")
        self.assertIn("automatic checkpoint due (2 x suffix >= K) at ~32,768", f["crosses"])
        self.assertTrue(any(x.startswith("threshold: automatic checkpoint") for x in f["flags"]), f)
        _, g = curve(lambda n: 0.3 + 1e-4 * n, series="auto_checkpoint.ms")
        self.assertFalse([x for x in g["flags"] if x.startswith("threshold")], g["flags"])
        # A series the threshold cannot move lists no crossing.
        _, h = curve(lambda n: 0.3 + 1e-4 * n, series="reads.article_p50_ms")
        self.assertNotIn("crosses", h)

    def test_ambiguity_and_missing_points(self):
        c, f = curve(lambda n: 0.3 + 1e-4 * n)
        del c["points"]["100000"]["values"]["s.s"]
        f = sc.fit_all(c)["s.s"]
        self.assertIn("failed: no point at N = [100000]", f["flags"])
        # Two points only: no fit.
        pts = {"1000": {"values": {"s.s": 1.0}}, "2000": {"values": {"s.s": 2.0}}}
        g = sc.fit_all({"meta": {"ns": NS}, "points": pts})["s.s"]
        self.assertNotIn("best", g)
        self.assertTrue(g["flags"][0].startswith("failed"))
        # Log N and N both fit a gently rising 3-point series within the noise:
        # ambiguous, as the flag says.
        pts = {str(n): {"values": {"s.s": v}} for n, v in ((1000, 1.0), (2000, 1.08), (5000, 1.2))}
        h = sc.fit_all({"meta": {"ns": [1000, 2000, 5000]}, "points": pts})["s.s"]
        self.assertTrue(any(x.startswith("ambiguous") for x in h["flags"]), h)


class OutputTests(unittest.TestCase):
    def test_the_table_and_the_known_comparison(self):
        c, _ = curve(lambda n: 0.3 + 1e-4 * n, series="open_checkpoint.s")
        md = sc.markdown(c)
        self.assertIn("| open_checkpoint.s | 0.4 | 0.5 | 0.8 | 1.30 |", md)
        self.assertIn("| N | 0.000 |", md)
        self.assertIn("Known thresholds inside the measured range", md)
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "curve.json"
            path.write_text(json.dumps(c))
            out = subprocess.run([sys.executable, str(ROOT / "tools" / "scale_curve.py"), "fit", str(path),
                                  "--known", "open_checkpoint.s=100.3@1000000",
                                  "open_checkpoint.s=10.3@100000"],
                                 capture_output=True, text=True, check=True).stdout
        self.assertIn("| open_checkpoint.s | 1,000,000 | 100 | N | 100 | 1.00 |", out)
        self.assertIn("| open_checkpoint.s 1,000,000/100,000 | 9.74 | 9.74 | 1.00 |", out)


class RegistryTests(unittest.TestCase):
    def test_probes_stages_and_variants(self):
        self.assertTrue(all(stage in sc.STAGES for stage, _ in sc.PROBES.values()))
        std = sc.standard_probes()
        for name in ("open_replay", "checkpoint", "open_checkpoint", "reads", "status", "health",
                     "posts", "digest", "export"):
            self.assertIn(name, std)
        for name in ("auto_checkpoint", "pinned_reader", "reclaim"):
            self.assertIn(name, sc.VARIANTS)
            self.assertNotIn(name, std)
        self.assertTrue(all(sc.PROBES[p][1].__doc__ for p in sc.PROBES))

    def test_the_curve_fixture_is_registered_at_the_curve_ns(self):
        import fixtures
        fx = fixtures.BY_NAME["curve"]
        self.assertEqual(tuple(fixtures.CURVE_NS), sc.NS)
        self.assertEqual(fx.stores, tuple("n{}/store".format(n) for n in sc.NS))
        self.assertEqual(sc.FIXTURES, str(fixtures.ROOT / "curve"))


class HeapProbeTests(unittest.TestCase):
    """The `heap` probe (the fold of f8_curve.py) against a stand-in hook."""

    def test_heap_probe_reads_the_hook_and_names_its_series(self):
        import os
        import threading
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as d:
            heap = Path(d)

            def hook():
                while not (heap / "go").exists():
                    pass
                tag = (heap / "go").read_text().strip()
                (heap / "go").unlink()
                (heap / ("heap-" + tag + ".txt")).write_text(
                    "dynamic-usage 900\ndynamic-usage-after-gc 700\n")
                (heap / ("done-" + tag)).write_text("")
            threading.Thread(target=hook, daemon=True).start()
            pt = SimpleNamespace(n=1000, env={"FN_HEAP_DIR": d},
                                 owner=SimpleNamespace(pid=os.getpid()))
            values = sc.PROBES["heap"][1](pt)
        self.assertEqual((values["live_bytes"], values["garbage_bytes"]), (700, 200))
        self.assertIn("heap", sc.VARIANTS)


if __name__ == "__main__":
    unittest.main()
