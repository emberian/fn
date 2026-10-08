"""Laptop unit tests of tools/load: the judge, the workload parser, the report and item filing.

Fixed JSON in, no image, no box, seconds.  Run only this module:
    python3 -m unittest tests.test_load_harness
"""
import json
import tempfile
import unittest
from pathlib import Path

from tools.load import cells, peers, result, workloads


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


class TimeBarTests(unittest.TestCase):
    def setUp(self):
        self.bars = result.load_bars()

    def cr(self, **box):
        b = {"name": "persvati", "cores": 12, "loadavg_start": [20.0, 2, 2], "loadavg_end": [20.5, 2, 2], "fs": "zfs", "pinned": list(range(12, 24)),
             "busy_cores_start": 1.0, "busy_cores_end": 1.5}
        b.update(box)
        return cell_result(cell="W1", workload="post-rate", box=b,
                           metrics={"post.p50_ms.c1": 18.0, "post.p99_ms.c1": 200.0, "post.cpu_ms_per_op.c1": 10.0,
                                    "post.rate_c1r3": 12.0, "post.rate_c8r3": 30.0}, not_measured={})

    def rows(self, cr):
        return {r["bar"]: r for r in result.judge_cell(cr, self.bars)}

    def test_quiet_pinned_zfs_cell_is_judged(self):
        rows = self.rows(self.cr())
        self.assertEqual(rows["T-POST"]["verdict"], "PASS")
        self.assertEqual(rows["T-RATE"]["verdict"], "PASS")     # the tmpfs checks do not apply on zfs

    def test_time_bar_is_not_measured_when_load_exceeds_4_at_either_end(self):
        for box in ({"busy_cores_start": 4.5}, {"busy_cores_end": 6.0}):
            row = self.rows(self.cr(**box))["T-POST"]
            self.assertEqual(row["verdict"], "NOT-MEASURED")
            self.assertIn("box loaded", row["reason"])
            self.assertEqual(row["checks"][0]["value"], 18.0)   # the figures stay in the row

    def test_whole_box_loadavg_does_not_matter_only_the_cells_cores(self):
        row = self.rows(self.cr())["T-POST"]       # loadavg 20 but 1.0 busy cores on 12-23
        self.assertEqual(row["verdict"], "PASS")

    def test_missing_per_core_record_is_not_measured(self):
        row = self.rows(self.cr(busy_cores_start=None))["T-POST"]
        self.assertEqual(row["verdict"], "NOT-MEASURED")

    def test_publication_octets_exponent_is_judged_on_a_loaded_box(self):
        cr = cell_result(cell="W15", workload="mem-vs-size", box={"name": "hbox", "busy_cores_start": 20, "busy_cores_end": 20, "loadavg_start": [20, 20, 20]},
                         metrics={"publish.write_octets.exponent": 0.957}, not_measured={"publish.stall_max_s": "needs W8"})
        row = {r["bar"]: r for r in result.judge_cell(cr, self.bars)}["T-PUB"]
        self.assertEqual(row["verdict"], "FAIL")

    def test_time_bar_needs_pinned_cores(self):
        row = self.rows(self.cr(pinned=None))["T-POST"]
        self.assertEqual(row["verdict"], "NOT-MEASURED")
        self.assertIn("pinned", row["reason"])

    def test_zfs_checks_do_not_apply_on_tmpfs_and_tmpfs_floor_is_50(self):
        cr = self.cr(fs="tmpfs")
        rows = self.rows(cr)
        self.assertEqual(rows["T-RATE"]["verdict"], "FAIL")      # 12/s < 50/s on tmpfs
        self.assertEqual(rows["T-POST"]["checks"][-1]["metric"], "post.cpu_ms_per_op.c1")
        self.assertEqual(len(rows["T-POST"]["checks"]), 1)       # only the CPU check applies

    def test_cpu_over_16_ms_per_post_fails(self):
        cr = self.cr()
        cr["metrics"]["post.cpu_ms_per_op.c1"] = 17.0
        self.assertEqual(self.rows(cr)["T-POST"]["verdict"], "FAIL")


class SweepTests(unittest.TestCase):
    def sub(self, key, n, open_s):
        return (key, n, {"cell": "W15@" + key, "status": "complete", "target": "image", "box": {"name": "hbox", "loadavg_start": [1, 1, 1]},
                         "metrics": {"open_s.checkpoint": open_s, "rss.at_rest.vmrss": 100000 + n}, "not_measured": {}, "refusals": {}})

    def test_merge_suffixes_and_fits_exponents(self):
        subs = [self.sub("1k", 1000, 1.0), self.sub("10k", 10000, 10.0), self.sub("100k", 100000, 100.0)]
        m = cells.merge_sweep("W15", "mem-vs-size", subs)
        self.assertEqual(m["metrics"]["open_s.checkpoint@10k"], 10.0)
        self.assertAlmostEqual(m["metrics"]["open_s.checkpoint.exponent"], 1.0, places=2)
        self.assertLess(m["metrics"]["rss.at_rest.vmrss.exponent"], 0.2)
        self.assertEqual(m["status"], "complete")

    def test_incomplete_member_marks_the_merged_cell(self):
        subs = [self.sub("1k", 1000, 1.0), self.sub("10k", 10000, 10.0)]
        subs[1][2]["status"] = "error"
        self.assertIn("10k error", cells.merge_sweep("W15", "mem-vs-size", subs)["status"])

    def test_sub_cells_are_not_judged_twice(self):
        cr = cell_result(cell="W15@1k", sub=True)
        self.assertEqual(result.judge_cell(cr, result.load_bars()), [])

    def test_census_sums_owner_slots_per_stobj(self):
        text = ("=== RAW dynamic-usage 1000\n--- room\nCONS:\n    5,000 bytes, 10 objects, 100% dynamic.\n\n"
                "--- instance-usage\n\nTop 80 dynamic instance types:\n  FN-X   4,000 bytes,   12 objects (3 per object).\n"
                "--- owner\nOWNER cat slot 0 type T bytes 4000\nOWNER cat slot 1 type (UNSIGNED-BYTE_32) bytes 300\n"
                "OWNER arena slot 0 type T bytes 10\n--- large\nLARGE (UNSIGNED-BYTE_8) count 2 bytes 600000 maxlen 400000\n")
        c = cells.parse_census(text)["raw"]
        self.assertEqual(c["dynamic_usage"], 1000)
        self.assertEqual(c["groups"]["cat"], 4300)
        self.assertEqual(c["groups"]["arena"], 10)
        self.assertEqual(c["large"]["(UNSIGNED-BYTE_8)"]["bytes"], 600000)
        self.assertEqual(c["by_type"]["room:CONS"], 5000)
        self.assertEqual(c["by_type"]["inst:FN-X"], 4000)


class ProfTests(unittest.TestCase):
    def test_parse_prof_window(self):
        text = ("window_ms 5000.0 gc_ms 120.0 consed_mb 440.0\n"
                "acl2-entry\tfn-post\t100\t900.5\nacl2-entry\tfn-x\t50\t10.0\nbarrier\tfdatasync\t100\t40.0\n"
                "gate-hold\tfoo\t7\t3.0\n")
        r = cells.parse_prof(text, 100)
        self.assertEqual(r["calls_per_cmd"], 1.5)
        self.assertEqual(r["sync_calls_per_cmd"], 1.0)
        self.assertEqual(r["sync_ms_per_cmd"], 0.4)
        self.assertEqual(r["consed_bytes_per_cmd"], round(440 * 1048576 / 100))

    def test_alloc_exponent_flat_in_article_size(self):
        ph = [{"name": "prof", "prof": {"ARTICLE_%dk" % k: {"calls_per_cmd": 3, "sync_calls_per_cmd": 0, "sync_ms_per_cmd": 0,
                                                          "consed_bytes_per_cmd": 10_000_000 + k * 100} for k in (2, 8, 32, 128)}}]
        m, nm = cells.derive("prof-ops", ph)
        self.assertLess(m["alloc.article.exponent"], 0.1)


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

DONE = ("catch-up peer=A round=done position=1000 end=1000 imported=1000 duplicate=0 refused=0 "
        "digest=" + "ab" * 32 + " transport=clear")
FAILED = ("catch-up peer=A round=failed position=9954 end=10000 imported=9954 duplicate=0 refused=0 "
          "digest=" + "cd" * 32 + " reason=round-deadline transport=clear")


class PeersTests(unittest.TestCase):
    def test_round_lines_parse_done_and_failed_with_reason(self):
        d = peers.parse_round_line("2026-10-07T18:00:00Z info " + DONE)
        self.assertEqual((d["round"], d["position"], d["imported"], d["reason"], d["transport"]), ("done", 1000, 1000, None, "clear"))
        f = peers.parse_round_line(FAILED)
        self.assertEqual((f["round"], f["reason"], f["imported"], f["end"]), ("failed", "round-deadline", 9954, 10000))
        pre = peers.parse_round_line(FAILED.replace("transport=clear", "at=preamble"))
        self.assertEqual(pre["at"], "preamble")
        self.assertIsNone(peers.parse_round_line("catch-up peer=A starting"))

    def test_splits_are_the_seconds_per_thousand(self):
        series = [(1.0, 0), (2.0, 400), (3.0, 1000), (4.0, 1500), (5.0, 2600), (6.0, 2999)]
        self.assertEqual(peers.splits(series, 0.0), [3.0, 2.0])      # 1000 at t=3, 2000 at t=5; 2999 is partial
        self.assertEqual(peers.splits([], 0.0), [])
        self.assertEqual(peers.splits([(9.0, 5000)], 4.0), [5.0, 0.0, 0.0, 0.0, 0.0])

    def test_cpu_splits_difference_the_cpu_at_each_thousand(self):
        rows = [(500, 2.0, 5.0), (1000, 3.0, 9.0), (1900, 4.0, 15.0), (2100, 5.5, 18.0)]
        self.assertEqual(peers.cpu_splits(rows, (1.0, 1.0)), [{"a_cpu_s": 2.0, "b_cpu_s": 8.0}, {"a_cpu_s": 2.5, "b_cpu_s": 9.0}])

    def test_gc_and_thread_splits_per_thousand(self):
        gc = ["GC 100 5000 52428800", "GC 200 9000 104857600", "GC 400 30000 157286400", "junk"]
        out = peers.gc_splits(gc, 0, [250, 450])
        self.assertEqual(out[0], {"gc_ms": 9.0, "gcs": 2, "dynamic_mib_after_gc": 100.0})
        self.assertEqual(out[1], {"gc_ms": 21.0, "gcs": 1, "dynamic_mib_after_gc": 150.0})
        td = peers.thread_deltas({"1 sbcl": 1.0}, [{"1 sbcl": 3.0, "2 w": 1.0}, {"1 sbcl": 4.0, "2 w": 9.0}], top=1)
        self.assertEqual(td, [{"1 sbcl": 2.0}, {"2 w": 8.0}])
        self.assertEqual([r[0] for r in peers.crossings([(500,), (1000,), (1001,), (2500,)])], [1000, 2500])

    def test_pace_and_thin(self):
        self.assertEqual(peers.pace(1000, 34.2), 29.24)
        self.assertIsNone(peers.pace(10, 0))
        pts = [(i, i) for i in range(1000)]
        t = peers.thin(pts, 100)
        self.assertLessEqual(len(t), 101)
        self.assertEqual(t[-1], pts[-1])
        self.assertEqual(peers.thin(pts[:5], 100), pts[:5])

    def test_compare_counts_missing_extra_and_differing_ignoring_path_and_xref(self):
        def art(mid, body, path="Path: a!not-for-mail", xref="Xref: a fn.test:1"):
            return ("%s\r\n%s\r\nMessage-ID: %s\r\n\r\n%s\r\n" % (path, xref, mid, body)).encode()
        a = {"<1>": art("<1>", "x"), "<2>": art("<2>", "y"), "<3>": art("<3>", "z")}
        b = {"<1>": art("<1>", "x", "Path: b!a!not-for-mail", "Xref: b fn.test:9"), "<2>": art("<2>", "CHANGED"), "<4>": art("<4>", "w")}
        c = peers.compare(a, ["<1>", "<2>", "<3>"], b, ["<1>", "<2>", "<4>"])
        self.assertEqual((c["missing"], c["extra"], c["differing"], c["divergence"]), (1, 1, 1, 3))
        self.assertFalse(c["order_equal"])
        same = peers.compare(a, ["<1>"], dict(a), ["<1>"])
        self.assertEqual(same["divergence"], 0)
        self.assertTrue(same["order_equal"])

    def test_chain_digest_is_the_tests_recurrence_over_articles_without_xref(self):
        calls = []
        fake = lambda data: (calls.append(data), bytes([len(data) % 256]) * 32)[1]
        arts = {"<1>": b"Xref: n fn.test:1\r\nA: b\r\n\r\nbody\r\n"}
        h = peers.chain_digest(["<1>"], arts, fake)
        self.assertEqual(len(h), 64)
        self.assertEqual(calls[0], b"A: b\r\n\r\nbody\r\n")        # Xref dropped before hashing
        self.assertEqual(calls[1], bytes(32) + fake(b"A: b\r\n\r\nbody\r\n") + b"<1>")
        self.assertEqual(peers.chain_digest([], {}, fake), "00" * 32)

    def test_digest_lines_keep_the_last_hex_word_of_each_line(self):
        text = ("digest history " + "11" * 32 + "\ndigest canonical " + "22" * 32 + "\nnoise\ndigest state " + "33" * 32
                + "\ncheckpoint-digest sequence=1000 " + "44" * 32 + "\nopen=checkpoint:1000 suffix=0\n")
        self.assertEqual(peers.digest_lines(text), {"history": "11" * 32, "canonical": "22" * 32, "state": "33" * 32,
                                                    "checkpoint-digest": "44" * 32})

    def test_p99_ratio_needs_200_samples_on_both_sides(self):
        idle, during = result.lat_stats([0.01] * 300), result.lat_stats([0.025] * 300)
        self.assertEqual(peers.p99_ratio(during, idle), 2.5)
        self.assertIsNone(peers.p99_ratio(result.lat_stats([0.01] * 50), idle))
        self.assertEqual(peers.lag_summary([(0, 10, 10), (1, 50, 20), (2, 60, 60)]), {"max": 30, "final": 0})

    def phase(self, **over):
        r = {"nominal": 1000, "mode": "catchup", "terminal": "round-done", "pace_excl_start": 31.5, "pace_incl_start": 29.2,
             "b_count_final": 1000, "rounds_failed": 0, "first_import_s": 3.1, "chain_equal": True, "a_count_final": 1000,
             "compare": {"divergence": 0}, "b_mem": {"vmrss": 150000, "hwm": 160000, "peak_vmrss": 155000}}
        r.update(over)
        return [{"name": "pull", "kind": "peers", "measure": True, "peers": r, "mem": {"vmrss": 1, "hwm": 2, "anon": 3, "file": 4}}]

    def test_catchup_metrics_name_the_nominal_n_and_both_paces(self):
        m, nm = cells.derive("catchup", self.phase())
        self.assertEqual((m["catchup.rate_1000"], m["catchup.rate_incl_start_1000"]), (31.5, 29.2))
        self.assertEqual((m["peers.divergence"], m["peers.digest_chain_equal"], m["b.rss_kib.hwm"]), (0, 1, 160000))
        self.assertNotIn("catchup.rate_10000", m)

    def test_a_failed_round_is_not_measured_with_its_terminal_and_divergence_fails(self):
        m, nm = cells.derive("catchup", self.phase(nominal=10000, pace_excl_start=None, pace_incl_start=None, terminal="deadline-2400s",
                                                    compare={"divergence": 46}, chain_equal=False))
        self.assertIn("deadline-2400s", nm["catchup.rate_10000"])
        cr = cell_result(cell="W6a@10k", workload="catchup", metrics=m, not_measured=nm)
        rows = {r["bar"]: r for r in result.judge_cell(cr, result.load_bars())}
        self.assertEqual(rows["L-CATCHUP"]["verdict"], "NOT-MEASURED")
        self.assertEqual(rows["L-DIVERGE-CATCHUP"]["verdict"], "FAIL")

    def test_post_p99_under_load_is_judged_by_ratio_and_labelled_proposal(self):
        ph = self.phase(mode="catchup-load", post_idle=result.lat_stats([0.01] * 300), post_during=result.lat_stats([0.04] * 300))
        m, nm = cells.derive("peers-catchup-load", ph)
        self.assertEqual(m["post.p99_ratio"], 4.0)
        cr = cell_result(cell="W6c@1k", workload="peers-catchup-load", metrics=m, not_measured=nm)
        rows = {r["bar"]: r for r in result.judge_cell(cr, result.load_bars())}
        self.assertEqual(rows["L-CATCHUP-POST-P99"]["verdict"], "FAIL")
        self.assertIn("PROPOSAL", rows["L-CATCHUP-POST-P99"]["quantity"])

    def test_w6_cells_resolve_with_their_peers_mode_and_the_test_profile(self):
        data = workloads.load()
        a = workloads.resolve("W6a@10k", data)
        self.assertEqual((a.spec["peers"]["mode"], a.spec["store"]["preload"], a.spec["phases"][0]["kind"]), ("catchup", 10000, "peers"))
        self.assertEqual(workloads.resolve("W6b", data).spec["phases"][0]["posts"], 1300)
        c = workloads.resolve("W6c@1k", data).spec["phases"][0]
        self.assertEqual((c["rate_per_s"], c["mode"]), (20, "catchup-load"))
        flags = workloads.init_flags(data, "peers")
        self.assertIn("32768", flags)                                  # tests/test_native_peer_catchup PROFILE
        self.assertEqual(flags[flags.index("--max-history-octets") + 1], str(64 << 20))



if __name__ == "__main__":
    unittest.main()
