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


if __name__ == "__main__":
    unittest.main()
