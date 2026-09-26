"""The throughput gate's check: tolerance and floor, the run it picks for HEAD,
and the named-cause override (tools/throughput_gate.py)."""

import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

from tools import throughput_gate as tg


def git(root, *args):
    return subprocess.run(["git", "-C", str(root)] + list(args), check=True, stdout=subprocess.PIPE,
                          text=True, env={"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@x",
                                          "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@x",
                                          "PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin"}).stdout.strip()


class ThroughputGateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        git(self.root, "init", "-q")
        (self.root / "host").mkdir()
        (self.root / "host" / "a.lisp").write_text("a\n")
        git(self.root, "add", "host/a.lisp")
        git(self.root, "commit", "-q", "--no-gpg-sign", "-m", "one")
        self.first = git(self.root, "rev-parse", "HEAD")
        self.runs = self.root / "planning" / "evidence" / "throughput"
        self.runs.mkdir(parents=True)
        self.patches = [mock.patch.object(tg, "ROOT", self.root),
                        mock.patch.object(tg, "RUNS", self.runs),
                        mock.patch.object(tg, "BASELINE", self.root / "planning" / "throughput-baseline.json"),
                        mock.patch.object(tg, "CAUSES", self.root / "planning" / "throughput-causes.json")]
        for p in self.patches:
            p.start()
        tg.BASELINE.write_text(json.dumps({"metrics": {
            "probe_cpu_s": {"value": 4.0, "floor": 0.5},
            "post_median_ms": {"value": 1.6, "floor": 1.0}}}))

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.tmp.cleanup()

    def record(self, name, revision, finished, **metrics):
        doc = {"revision": revision, "finished_utc": finished,
               "quiet_before": {"threshold_cores": tg.QUIET_CPU}, "box_load": {}}
        doc.update(metrics)
        (self.runs / name).write_text(json.dumps(doc))

    def check(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = tg.check(None)
        return code, out.getvalue()

    def test_limit_is_the_larger_of_tolerance_and_floor(self):
        self.assertEqual(tg.limit(4.0, 0.5), 5.0)
        self.assertEqual(tg.limit(1.6, 1.0), 2.6)

    def test_within_tolerance_passes_and_a_twenty_fold_step_fails(self):
        self.record("a.json", self.first, "2026-09-26T01:00:00Z", probe_cpu_s=4.9, post_median_ms=2.5)
        self.assertEqual(self.check()[0], 0)
        self.record("b.json", self.first, "2026-09-26T02:00:00Z", probe_cpu_s=80.0, post_median_ms=1.7)
        code, text = self.check()
        self.assertEqual(code, 1)
        self.assertIn("REGRESSION probe_cpu_s", text)
        self.assertNotIn("REGRESSION post_median_ms", text)

    def test_a_figure_well_under_the_baseline_is_reported_improved(self):
        self.record("a.json", self.first, "2026-09-26T01:00:00Z", probe_cpu_s=2.0, post_median_ms=1.5)
        code, text = self.check()
        self.assertEqual(code, 0)
        self.assertIn("IMPROVED probe_cpu_s", text)
        self.assertNotIn("IMPROVED post_median_ms", text)

    def test_a_missing_metric_fails(self):
        self.record("a.json", self.first, "2026-09-26T01:00:00Z", probe_cpu_s=4.0)
        code, text = self.check()
        self.assertEqual(code, 1)
        self.assertIn("MISSING post_median_ms", text)

    def test_named_cause_passes_the_regression_and_only_for_its_revision(self):
        self.record("b.json", self.first, "2026-09-26T02:00:00Z", probe_cpu_s=80.0, post_median_ms=1.7)
        tg.CAUSES.write_text(json.dumps({"causes": [{"revision": "0000000", "reason": "other"}]}))
        self.assertEqual(self.check()[0], 1)
        tg.CAUSES.write_text(json.dumps({"causes": [{"revision": self.first[:12], "reason": "known"}]}))
        code, text = self.check()
        self.assertEqual(code, 0)
        self.assertIn("named cause", text)

    def test_the_nearest_measured_ancestor_is_compared_and_a_later_code_change_is_stale(self):
        self.record("old.json", self.first, "2026-09-26T09:00:00Z", probe_cpu_s=80.0, post_median_ms=1.7)
        (self.root / "host" / "a.lisp").write_text("b\n")
        git(self.root, "commit", "-q", "--no-gpg-sign", "-am", "two")
        second = git(self.root, "rev-parse", "HEAD")
        # The older revision alone: it is compared, and named stale.
        code, text = self.check()
        self.assertEqual(code, 1)
        self.assertIn("STALE", text)
        # A run of HEAD itself is nearer, whatever its timestamp.
        self.record("new.json", second, "2026-09-26T01:00:00Z", probe_cpu_s=4.0, post_median_ms=1.7)
        code, text = self.check()
        self.assertEqual(code, 0)
        self.assertNotIn("STALE", text)

    def test_an_under_load_run_is_compared_on_cpu_and_allocation_only(self):
        self.record("load.json", self.first, "2026-09-26T01:00:00Z", quiet=False,
                    probe_cpu_s=4.1, post_median_ms=50.0)
        code, text = self.check()
        self.assertEqual(code, 0)
        self.assertIn("1 of 2 metrics compared", text)
        self.record("load2.json", self.first, "2026-09-26T02:00:00Z", quiet=False,
                    probe_cpu_s=80.0, post_median_ms=1.0)
        self.assertEqual(self.check()[0], 1)
        # A quiet run of the same revision is preferred over a newer loaded one.
        self.record("quiet.json", self.first, "2026-09-26T00:00:00Z", quiet=True,
                    probe_cpu_s=4.0, post_median_ms=1.6)
        code, text = self.check()
        self.assertEqual(code, 0)
        self.assertIn("quiet.json", text)

    def test_refused_and_smoke_runs_are_not_evidence(self):
        self.record("refused.json", self.first, "2026-09-26T01:00:00Z", refused="box not quiet: x")
        doc = {"revision": self.first, "finished_utc": "2026-09-26T02:00:00Z",
               "quiet_before": {"threshold_cores": 100.0}, "probe_cpu_s": 99.0, "post_median_ms": 99.0}
        (self.runs / "smoke.json").write_text(json.dumps(doc))
        code, text = self.check()
        self.assertEqual(code, 0)
        self.assertIn("NOT MEASURED", text)

    def test_the_signed_row_catches_a_return_of_the_replay_under_load(self):
        tg.BASELINE.write_text(json.dumps({"metrics": {
            "post_signed_owner_cpu_ms": {"value": 90.0, "floor": 25.0},
            "post_signed_p95_ms": {"value": 120.0, "floor": 50.0}}}))
        # Under load only the owner's CPU is compared: the wall figure is not.
        self.record("a.json", self.first, "2026-09-26T01:00:00Z", quiet=False,
                    post_signed_owner_cpu_ms=100.0, post_signed_p95_ms=900.0)
        code, text = self.check()
        self.assertEqual(code, 0)
        self.assertIn("1 of 2 metrics compared", text)
        # signed-history-index's before row: 0.355 s against 0.101 s at N = 1,000.
        self.record("b.json", self.first, "2026-09-26T02:00:00Z", quiet=False,
                    post_signed_owner_cpu_ms=340.0, post_signed_p95_ms=400.0)
        code, text = self.check()
        self.assertEqual(code, 1)
        self.assertIn("REGRESSION post_signed_owner_cpu_ms", text)

    def test_baseline_takes_a_new_metric_from_dev_alone_and_refuses_it_missing_from_dev(self):
        full = {m: 1.0 for m in tg.METRICS}
        release = {k: v for k, v in full.items() if k not in tg.NEW_METRICS}
        release.update(revision="r" * 40, core_sha256="c")
        dev = dict(full, revision="d" * 40, core_sha256="e", post_signed_p95_ms=110.0)
        rp, dp = self.root / "release.json", self.root / "dev.json"
        rp.write_text(json.dumps(release))
        dp.write_text(json.dumps(dev))
        tg.BASELINE.unlink()
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            tg.write_baseline(mock.Mock(release=str(rp), dev=str(dp), allow_regression=False))
        row = json.loads(tg.BASELINE.read_text())["metrics"]["post_signed_p95_ms"]
        self.assertEqual((row["value"], row["release"], row["dev"]), (110.0, None, 110.0))
        self.assertIn("release run predates it", out.getvalue())
        self.assertEqual(json.loads(tg.BASELINE.read_text())["metrics"]["post_median_ms"]["value"], 1.0)
        # A metric outside NEW_METRICS, or one the dev run lacks, is still refused.
        del dev["post_signed_p95_ms"]
        dp.write_text(json.dumps(dev))
        with self.assertRaises(SystemExit), contextlib.redirect_stdout(io.StringIO()):
            tg.write_baseline(mock.Mock(release=str(rp), dev=str(dp), allow_regression=False))
        del release["post_median_ms"]
        rp.write_text(json.dumps(release))
        with self.assertRaises(SystemExit), contextlib.redirect_stdout(io.StringIO()):
            tg.write_baseline(mock.Mock(release=str(rp), dev=str(dp), allow_regression=False))

    def test_the_signed_preload_spreads_its_carriers_over_the_extension(self):
        class Author:
            def sign(self, stem, octets):
                return stem.encode()
        at, probes = tg.signed_carriers_for(Author(), 0, 1000, 32, 5, 2048)
        self.assertEqual(len(at), 32)
        self.assertEqual(min(at), 0)
        self.assertLess(max(at), 1000)
        gaps = sorted(at)
        self.assertTrue(all(31 <= b - a <= 32 for a, b in zip(gaps, gaps[1:])))
        self.assertEqual(len(probes), 5)
        self.assertEqual(len(set(probes) | set(at.values())), 37)

    def test_a_carrier_source_is_dot_safe_and_about_its_size(self):
        from tools import signed_carriers as sc
        src = sc.source("<x@example.invalid>", 2048)
        self.assertTrue(1900 <= len(src) <= 2048)
        self.assertIn(b"Message-ID: <x@example.invalid>\r\n\r\n", src)
        self.assertEqual(sc.dot_stuff(b"a\r\n.b\r\n"), b"a\r\n..b\r\n")


if __name__ == "__main__":
    unittest.main()
