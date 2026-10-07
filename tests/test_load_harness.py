"""Laptop unit tests of tools/load: the judge, the workload parser, the report and item filing.

Fixed JSON in, no image, no box, seconds.  Run only this module:
    python3 -m unittest tests.test_load_harness
"""
import json
import tempfile
import unittest
from pathlib import Path

from tools.load import cells, result, workloads


def cell_result(**over):
    cr = {"cell": "W13", "workload": "rss-small-filled", "target": "image", "arm": "B", "rep": 1, "status": "complete",
          "preset": "small", "git": "0123456789abcdef", "launch": "x", "seconds": 100.0,
          "image": {"path": "/img/fn-host-developer", "core_sha256": "ab" * 32, "tree_sha": "0b4d3b18385a53209146a78296e282d06c17e573"},
          "box": {"name": "hbox", "cores": 16, "loadavg_start": [4.0, 4.0, 4.0], "loadavg_end": [4.5, 4.1, 4.0],
                  "fs": "tmpfs", "arc_bytes_start": 1, "arc_bytes_end": 2},
          "phases": [{"name": "idle", "kind": "idle", "seconds": 20.0, "measure": True, "status": "ok",
                      "mem": {"vmrss": 160000, "hwm": 210000, "anon": 25000, "file": 132000}, "gc": {"count": 3, "ms": 120.0},
                      "counts": {"admitted": 1000, "refused": 0}}],
          "metrics": {"rss_kib.vmrss": 160000, "rss_kib.hwm": 210000, "rss_kib.anon": 25000, "rss_kib.file": 132000, "gc.ms": 120.0},
          "not_measured": {}, "refusals": {}, "admitted": {"admitted": 1000, "refused": 0}}
    cr.update(over)
    return cr


class JudgeTests(unittest.TestCase):
    def setUp(self):
        self.bars = result.load_bars()

    def rows(self, cr):
        return {r["bar"]: r for r in result.judge_cell(cr, self.bars)}

    def test_hwm_over_the_bar_fails_and_rss_is_only_reported(self):
        rows = self.rows(cell_result())          # hwm 210000 > 131072
        self.assertEqual(rows["L-HWM"]["verdict"], "FAIL")
        self.assertEqual(rows["L-RSS"]["verdict"], "REPORTED")
        cr = cell_result()
        cr["metrics"]["rss_kib.hwm"] = 131072
        cr["metrics"]["rss_kib.vmrss"] = 999999   # at-rest RSS is never judged
        rows = self.rows(cr)
        self.assertEqual(rows["L-HWM"]["verdict"], "PASS")
        self.assertEqual(rows["L-RSS"]["verdict"], "REPORTED")
        cr["metrics"]["rss_kib.hwm"] = 131073
        self.assertEqual(self.rows(cr)["L-HWM"]["verdict"], "FAIL")

    def test_absent_metric_is_not_measured_with_its_reason(self):
        cr = cell_result(metrics={}, not_measured={"rss_kib.hwm": "idle phase did not complete"})
        row = self.rows(cr)["L-HWM"]
        self.assertEqual(row["verdict"], "NOT-MEASURED")
        self.assertIn("idle phase", row["reason"])

    def test_latency_bar_is_not_measured_when_the_box_is_loaded(self):
        cr = cell_result(cell="W2@10k", workload="readers", metrics={"article.p99_ms.R16": 80.0},
                         box={"name": "hbox", "loadavg_start": [9.5, 8, 7]})
        row = self.rows(cr)["L-READ"]
        self.assertEqual(row["verdict"], "NOT-MEASURED")
        self.assertIn("box loaded", row["reason"])
        cr["box"]["loadavg_start"] = [3.0, 3, 3]
        self.assertEqual(self.rows(cr)["L-READ"]["verdict"], "FAIL")
        cr["metrics"]["article.p99_ms.R16"] = 12.0
        self.assertEqual(self.rows(cr)["L-READ"]["verdict"], "PASS")

    def test_memory_bar_is_judged_on_a_loaded_box(self):
        cr = cell_result(box={"name": "hbox", "loadavg_start": [14.0, 13, 12]})
        self.assertEqual(self.rows(cr)["L-HWM"]["verdict"], "FAIL")

    def test_every_check_must_hold_and_a_fail_beats_a_missing_metric(self):
        cr = cell_result(cell="W1", workload="post-rate", metrics={"post.rate_c1": 5.0}, not_measured={})
        row = self.rows(cr)["L-POST"]
        self.assertEqual(row["verdict"], "FAIL")
        cr["metrics"] = {"post.rate_c1": 50.0}
        self.assertEqual(self.rows(cr)["L-POST"]["verdict"], "NOT-MEASURED")
        cr["metrics"] = {"post.rate_c1": 50.0, "post.rate_c8": 80.0}
        self.assertEqual(self.rows(cr)["L-POST"]["verdict"], "PASS")

    def test_incomplete_run_names_its_status(self):
        cr = cell_result(metrics={}, status="error")
        self.assertIn("error", self.rows(cr)["L-HWM"]["reason"])

    def test_every_bar_row_has_a_known_workload_and_cell(self):
        data = workloads.load()
        for b in self.bars:
            self.assertIn(b["workload"], data["workloads"], b["id"])
            self.assertEqual(data["cells"][b["cell"]], b["workload"], b["id"])
            self.assertTrue(b["checks"], b["id"])

    def test_bar_thresholds_are_the_program_numbers(self):
        by = {b["id"]: b for b in self.bars}
        self.assertEqual(by["L-HWM"]["checks"][0]["threshold"], 128 * 1024)
        self.assertEqual(by["L-HWM"]["checks"][0]["metric"], "rss_kib.hwm")
        self.assertEqual(by["L-HWM"]["severity"], "high")
        self.assertEqual(by["L-RSS"]["checks"][0]["cmp"], "report")
        self.assertEqual(by["L-LIN"]["checks"][0]["threshold"], 15.0)
        self.assertEqual(by["L-READ"]["checks"][0]["threshold"], 50)
        self.assertEqual({c["threshold"] for c in by["L-CATCHUP"]["checks"]}, {35})
        self.assertEqual({c["threshold"] for c in by["L-POST"]["checks"]}, {10})


class StatsTests(unittest.TestCase):
    def test_p99_is_null_under_200_samples(self):
        st = result.lat_stats([0.001] * 199)
        self.assertIsNone(st["p99_ms"])
        self.assertEqual(st["p50_ms"], 1.0)
        self.assertIsNotNone(result.lat_stats([0.001] * 200)["p99_ms"])

    def test_percentiles_on_a_ramp(self):
        st = result.lat_stats([i / 1000.0 for i in range(1, 401)])
        self.assertEqual(st["n"], 400)
        self.assertEqual(st["max_ms"], 400.0)
        self.assertAlmostEqual(st["p99_ms"], 396.0, delta=1.5)

    def test_exponent_of_linear_and_quadratic(self):
        self.assertAlmostEqual(result.fit_exponent([(1, 1), (2, 2), (4, 4), (8, 8)]), 1.0, places=3)
        self.assertAlmostEqual(result.fit_exponent([(1, 1), (2, 4), (4, 16)]), 2.0, places=3)


class WorkloadTests(unittest.TestCase):
    def test_file_validates_and_declares_the_required_workloads(self):
        data = workloads.load()
        for name in ("smoke", "rss-small-filled", "article-sizes", "post-rate", "readers", "growth", "m1-durable",
                     "fresh-start", "catchup"):
            self.assertIn(name, data["workloads"])

    def test_nmem3_clean_is_the_reference_workload(self):
        c = workloads.nmem3_clean()
        self.assertEqual((c["posts"], c["octets"], c["idle_connections"], c["idle_seconds"]), (1000, 2048, (8, 24), 20))
        self.assertIn("--max-open-suffix", c["init_flags"])
        self.assertEqual(c["groups"], ("fn.letters", "fn.test"))
        self.assertEqual(c["sbcl_user_args"], "--dynamic-space-size 1068MB --tls-limit 16384")

    def test_smoke_is_50_posts_50_articles_one_reader(self):
        s = workloads.resolve("smoke").spec["phases"]
        self.assertEqual((s[0]["count"], s[1]["count"], s[1]["readers"]), (50, 50, 1))

    def test_cell_ids_resolve_store_variant_and_arm(self):
        c = workloads.resolve("W2@10k/R16")
        self.assertEqual((c.workload, c.store_n, [p["name"] for p in c.spec["phases"]]), ("readers", 10000, ["R16"]))
        self.assertEqual(c.spec["store"]["preload"], 10000)
        self.assertEqual(workloads.resolve("W13/A").arm, "A")
        self.assertEqual(workloads.resolve("W1/default").spec["preset"], "default")

    def test_bad_ids_and_bad_data_are_refused(self):
        for bad in ("nope", "W2@7k", "W2/zzz", "W2@@"):
            with self.assertRaises(workloads.WorkloadError, msg=bad):
                workloads.resolve(bad)
        data = workloads.load()
        data["workloads"]["smoke"]["phases"][0]["kind"] = "frobnicate"
        with self.assertRaises(workloads.WorkloadError):
            workloads.validate(data)
        data = workloads.load()
        data["workloads"]["smoke"]["phases"][0].update(duration_s=5)
        with self.assertRaises(workloads.WorkloadError):
            workloads.validate(data)


class DeriveTests(unittest.TestCase):
    def test_rss_metrics_come_from_the_measure_phase(self):
        m, nm = cells.derive("rss-small-filled", cell_result()["phases"])
        self.assertEqual(m["rss_kib.vmrss"], 160000)
        self.assertEqual(m["gc.ms"], 120.0)

    def test_article_ratio_and_exponent(self):
        ph = [{"name": "sizes", "sizes_ms": {"16": 2.0, "64": 8.0, "512": 80.0}}]
        m, nm = cells.derive("article-sizes", ph)
        self.assertEqual(m["article.ratio_8n_over_n"], 10.0)
        self.assertIn("article.exponent", m)
        m, nm = cells.derive("article-sizes", [{"name": "sizes", "sizes_ms": {"16": 2.0}}])
        self.assertIn("article.ratio_8n_over_n", nm)

    def test_unimplemented_phase_names_every_metric_it_owns(self):
        ph = [{"name": "pull", "status": "not-implemented", "reason": "L6", "measure": True}]
        m, nm = cells.derive("catchup", ph)
        self.assertEqual(nm["catchup.rate_1000"], "L6")
        self.assertEqual(nm["catchup.rate_10000"], "L6")

    def test_reader_phases_carry_p99_only_with_200_samples(self):
        ph = [{"name": "R16", "cmd": {"ARTICLE": result.lat_stats([0.002] * 300)}, "rate": {"article_per_s": 100.0}}]
        m, nm = cells.derive("readers", ph)
        self.assertEqual(m["article.p99_ms.R16"], 2.0)
        ph = [{"name": "R16", "cmd": {"ARTICLE": result.lat_stats([0.002] * 50)}}]
        m, nm = cells.derive("readers", ph)
        self.assertIn("article.p99_ms.R16", nm)


class ReportAndItemTests(unittest.TestCase):
    def res(self, **over):
        return {"schema": 1, "label": "ctl", "rev": "0b4d3b1", "cells": [cell_result(**over)]}

    def test_report_leads_with_the_verdict_table_and_carries_conditions(self):
        text = result.report(self.res(), result.load_bars())
        first_table = text.index("| bar |")
        self.assertLess(first_table, text.index("| phase |"))
        self.assertIn("L-HWM", text)
        self.assertIn("FAIL", text)
        self.assertIn("load [4.0, 4.0, 4.0]", text)
        self.assertIn("loopback", text)

    def test_result_line_keys_and_prefix(self):
        cr = cell_result()
        cr["bars"] = result.judge_cell(cr, result.load_bars())
        line = result.print_line(cr, cr["bars"])
        self.assertTrue(line.startswith("FN_LOAD_RESULT {"))
        obj = json.loads(line[len("FN_LOAD_RESULT "):])
        for key in ("cell", "image", "box", "git", "load_start", "load_end", "seconds", "cmd", "rate", "rss_kib",
                    "refusals", "bar", "verdict"):
            self.assertIn(key, obj)
        self.assertEqual(obj["rss_kib"]["file"], 132000)
        self.assertEqual(obj["bar"]["L-HWM"], "FAIL")
        self.assertEqual(obj["verdict"], "fail")
        self.assertEqual(obj["gc_s"], 0.12)

    def test_items_are_filed_for_fails_only_and_updated_not_duplicated(self):
        with tempfile.TemporaryDirectory() as d:
            res = self.res()
            written = result.file_items(res, result.load_bars(), items_dir=d, now="2026-10-07T00:00:00Z")
            self.assertEqual([Path(p).name for p in written], ["LOAD-L-HWM-0b4d3b18385a.json"])
            item = json.loads(Path(written[0]).read_text())
            self.assertEqual(sorted(item), ["category", "detail", "file", "id", "line", "notes", "owner", "severity",
                                            "source", "state", "title", "updated"])
            self.assertEqual(item["state"], "open")
            self.assertIn("210000", item["detail"])
            # same run again: no duplicate, same file, no new note
            result.file_items(res, result.load_bars(), items_dir=d, now="2026-10-07T01:00:00Z")
            self.assertEqual(len(list(Path(d).glob("*.json"))), 1)
            self.assertEqual(json.loads(Path(written[0]).read_text())["notes"], [])
            # a re-run with a new figure updates the item and notes it
            res2 = self.res()
            res2["cells"][0]["metrics"]["rss_kib.hwm"] = 150000
            result.file_items(res2, result.load_bars(), items_dir=d, now="2026-10-07T02:00:00Z")
            item = json.loads(Path(written[0]).read_text())
            self.assertEqual(len(item["notes"]), 1)
            self.assertIn("150000", item["detail"])
            self.assertEqual(len(list(Path(d).glob("*.json"))), 1)

    def test_passes_and_not_measured_file_nothing(self):
        with tempfile.TemporaryDirectory() as d:
            res = self.res(metrics={"rss_kib.vmrss": 100000, "rss_kib.hwm": 120000})
            self.assertEqual(result.file_items(res, result.load_bars(), items_dir=d), [])
            res = self.res(metrics={})
            self.assertEqual(result.file_items(res, result.load_bars(), items_dir=d), [])


if __name__ == "__main__":
    unittest.main()
