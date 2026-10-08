"""Laptop unit tests of tools/load: the judge, the workload parser, the report and item filing.

Fixed JSON in, no image, no box, seconds.  Run only this module:
    python3 -m unittest tests.test_load_harness
"""
import io
import os
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from tools.load import cells, driver, peers, result, workloads, sweep


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


class LockWaitTests(unittest.TestCase):
    LOG = ("100000000 fn%20owner%2Fstore=10:10000 %3Cunnamed%3E=1:1000\n"
           "101000000 fn%20owner%2Fstore=13:16000 %3Cunnamed%3E=1:1000\n"
           "102000000 fn%20owner%2Fstore=18:26000 %3Cunnamed%3E=2:2000 fn%20extent%20realizer=2:6000\n"
           "103000000 fn%20owner%2Fstore=20:30000 %3Cunnamed%3E=2:2000 fn%20extent%20realizer=4:8000\n")

    def phase(self, **extra):
        return dict({"name": "R4", "kind": "read", "epoch_start": 100.5, "epoch_end": 102.5,
                     "cmd": {"ARTICLE": {"n": 4}, "POST": {"n": 20}}}, **extra)

    def test_parser_names_and_torn_tail(self):
        rows = cells.parse_locks(self.LOG + "104000000 fn%20owner%2Fstore=99:")
        self.assertEqual(len(rows), 4)
        self.assertEqual(rows[0][1]["fn owner/store"], (10, 10000))
        self.assertEqual(rows[0][1]["<unnamed>"], (1, 1000))

    def test_split_boundaries_use_previous_dumps_and_article_denominator(self):
        metrics, window = cells.phase_lock_metrics(cells.parse_locks(self.LOG), self.phase())
        self.assertEqual((window["epoch_start"], window["epoch_end"]), (100, 102))
        self.assertEqual(metrics["locks.fn owner/store.waits"], 8)
        self.assertEqual(metrics["locks.fn owner/store.wait_ms"], 16)
        self.assertEqual(metrics["locks.fn owner/store.wait_ms_per_article"], 4)
        self.assertEqual(metrics["locks.fn extent realizer.waits"], 2)
        self.assertEqual(metrics["locks.<unnamed>.wait_ms"], 1)
        exact, _ = cells.phase_lock_metrics(cells.parse_locks(self.LOG), self.phase(epoch_start=101, epoch_end=103))
        self.assertEqual(exact["locks.fn owner/store.waits"], 7)

    def test_phase_derivation_and_zero_articles(self):
        phases = [self.phase(), self.phase(name="R16", epoch_start=102, epoch_end=103, cmd={"ARTICLE": {"n": 0}})]
        cells.attach_lock_metrics(phases, self.LOG)
        metrics, nm = cells.derive("readers-locks", phases)
        self.assertEqual(metrics["locks.fn owner/store.wait_ms.R4"], 16)
        self.assertEqual(metrics["locks.fn owner/store.waits.R16"], 2)
        self.assertIn("locks.fn owner/store.wait_ms_per_article.R16", nm)

    def test_missing_coverage_and_corruption_are_not_zero_contention(self):
        for ph in (self.phase(epoch_start=99), self.phase(epoch_end=104), self.phase(epoch_end=100.8)):
            cells.attach_lock_metrics([ph], self.LOG)
            self.assertIn("locks_error", ph)
            self.assertNotIn("lock_metrics", ph)
        for log in (self.LOG + "104000000 fn%20owner%2Fstore=1:1\n",
                    self.LOG + "103000000\n", "100000000 broken\n"):
            with self.assertRaises(ValueError):
                cells.parse_locks(log)

    def test_report_top_eight_and_sample_window(self):
        ph = self.phase()
        cells.attach_lock_metrics([ph], self.LOG)
        for n in range(10):
            ph["lock_metrics"].update({"locks.extra%d.waits" % n: 1, "locks.extra%d.wait_ms" % n: 100 + n,
                                       "locks.extra%d.wait_ms_per_article" % n: (100 + n) / 4})
        text = result.report({"cells": [cell_result(phases=[ph])]}, [])
        self.assertIn("Snapshot window 100.000000–102.000000", text)
        self.assertIn("| extra9 |", text)
        self.assertIn("| extra2 |", text)
        self.assertNotIn("| extra1 |", text)
        self.assertLess(text.index("| extra9 |"), text.index("| extra2 |"))

    def test_workloads_inherit_reader_conditions(self):
        base = workloads.resolve("readers@10k").spec
        lock = workloads.resolve("W2L@10k").spec
        prof = workloads.resolve("readers-prof@10k").spec
        self.assertEqual(workloads.resolve("W2P@10k").workload, "readers-prof")
        for spec in (lock, prof):
            for key in ("preset", "store", "groups", "policy"):
                self.assertEqual(spec[key], base[key])
            for ph in spec["phases"]:
                self.assertEqual(ph["poster"], {"rate_per_s": 5, "octets": 2048})
        self.assertTrue(lock["lockwait"])
        self.assertEqual([(p["name"], p["duration_s"]) for p in lock["phases"]], [("R1", 20), ("R4", 20), ("R16", 20)])
        self.assertEqual([(p["readers"], p["duration_s"], p["measure"]) for p in prof["phases"]], [(16, 10, False), (16, 65, True)])
        self.assertEqual(prof["sprof"], {"window_s": 60})

    def test_hooks_and_fetchable_artifacts_without_image(self):
        with tempfile.TemporaryDirectory() as d:
            work, out = Path(d) / "work", Path(d) / "raw"
            work.mkdir()
            hooks, env = driver.cell_hooks(workloads.resolve("W2L").spec, work)
            self.assertIn(driver.LOCKS_HOOK, hooks)
            self.assertTrue(driver.LOCKS_HOOK.is_file())
            self.assertEqual(env["FN_LOAD_LOCKS"], str(work / "locks.log"))
            hooks, env = driver.cell_hooks(workloads.resolve("W2P").spec, work, gc_hook=True)
            self.assertIn(driver.SPROF_HOOK, hooks)
            self.assertNotIn(driver.HOOK, hooks)  # sprof already loads it
            self.assertTrue(driver.SPROF_HOOK.is_file())
            self.assertEqual(env["FN_LOAD_PROF_WINDOW"], "60")
            self.assertEqual(env["FN_LOAD_PROF"], str(work / "sprof"))
            self.assertEqual(env["FN_LOAD_PROF_START"], str(work / "sprof.start"))
            self.assertEqual(driver.cell_hooks(workloads.resolve("readers").spec, work), ([], {}))
            for name in ("locks.log.4242", "sprof.000.txt", "samples.json"):
                (work / name).write_text(name)
            files = driver.collect_measurement_artifacts(work, out, "W2P-image-x-r1")
            self.assertEqual(len(files), 3)
            for name in files:
                self.assertEqual((out / name).read_text(), Path(name).name)

    def test_invalid_measurement_settings_are_refused(self):
        for bad in (0, -1, True, 60.5, "60"):
            data = workloads.load()
            data["workloads"]["readers-prof"]["sprof"]["window_s"] = bad
            with self.assertRaises(workloads.WorkloadError):
                workloads.validate(data)
        data = workloads.load()
        data["workloads"]["readers-prof"]["phases"][-1]["measure"] = False
        with self.assertRaises(workloads.WorkloadError):
            workloads.validate(data)

    def test_read_epochs_and_profile_trigger_exclude_warmup(self):
        with tempfile.TemporaryDirectory() as d:
            trigger = Path(d) / "sprof.start"
            node = SimpleNamespace(env={"FN_LOAD_PROF_START": str(trigger)})
            ctr = driver.Counters()
            ctr.known.append(0)
            run = driver.Run(node, {"sprof": {"window_s": 60}}, ctr, None)
            # No connection or image: a refused connection ends this worker.
            with patch.object(run, "conn", return_value=None), patch.object(driver.time, "time", side_effect=[100, 110, 111, 176]):
                warm = run.phase_read({"readers": 1, "count": 1, "measure": False})
                self.assertFalse(trigger.exists())
                measured = run.phase_read({"readers": 1, "count": 1, "measure": True})
                self.assertTrue(trigger.exists())
            self.assertEqual((warm["epoch_start"], warm["epoch_end"]), (100, 110))
            self.assertEqual((measured["epoch_start"], measured["epoch_end"]), (111, 176))


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




class FaultFrameworkTests(unittest.TestCase):
    def test_outcomes_and_partial_reply(self):
        from tools.load.faults import History
        h = History()
        a, b, c = [h.plan('STAT', {'n': i}) for i in range(3)]
        h.sent(b)
        h.sent(c)
        with self.assertRaises(EOFError):
            h.complete(b, b'223 partial')
        h.complete(c, b'223 complete\r\n')
        self.assertEqual(h.counts(), {'not-attempted': 1, 'attempted-uncertain': 1, 'completed': 1})
        self.assertIsNone(a['send_time'])
        self.assertNotEqual(a['args_digest'], b['args_digest'])

    def test_durability_identity_and_uncertainty(self):
        from tools.load.faults import History, verify
        h = History()
        for mid, outcome in [('accepted', 'completed'), ('uncertain', 'attempted-uncertain'), ('unsent', 'not-attempted')]:
            op = h.plan('POST', {'msgid': mid, 'sha256': mid})
            if outcome != 'not-attempted':
                h.sent(op)
            if outcome == 'completed':
                h.complete(op, b'240 accepted\r\n')
        self.assertEqual(verify(h.ops, {'accepted': 'accepted'}), [])
        self.assertEqual(verify(h.ops, {'accepted': 'accepted', 'uncertain': 'uncertain'}), [])
        self.assertEqual({p for p, _ in verify(h.ops, {'accepted': 'wrong', 'unsent': 'unsent'})},
                         {'P1-DURABLE', 'P2-IDENTITY'})
        self.assertIn('P2-IDENTITY', [p for p, _ in verify(h.ops, {'uncertain': 'partial'})])
        self.assertIn('P2-IDENTITY', [p for p, _ in verify(h.ops, {'unknown': 'new'})])

    def test_later_conflicting_attempt_cannot_replace_accepted_identity(self):
        from tools.load.faults import History, verify
        h = History()
        a = h.plan('POST', {'msgid': 'a', 'sha256': 'original'})
        h.sent(a)
        h.complete(a, b'240 accepted\r\n')
        h.sent(h.plan('POST', {'msgid': 'a', 'sha256': 'replacement'}))
        self.assertEqual({p for p, _ in verify(h.ops, {'a': 'replacement'})}, {'P1-DURABLE', 'P2-IDENTITY'})

    def test_shrinker_reruns_and_honors_budget(self):
        from tools.load.faults import shrink
        attempts = []
        def fails(h):
            attempts.append(h)
            return 3 in h and 7 in h
        short, info = shrink(list(range(12)), fails, 100)
        self.assertEqual(short, [3, 7])
        self.assertEqual(info['minimal'], 'one-deletion')
        self.assertEqual(info['runs'], len(attempts))
        _, info = shrink(list(range(20)), lambda h: False, 2)
        self.assertEqual(info['runs'], 2)
        self.assertEqual(info['minimal'], 'budget-exhausted')

    def test_fault_hooks_and_boundary_inventory(self):
        from tools.load import faults
        root = Path(__file__).resolve().parents[1]
        data = workloads.load()
        for spec in data['workloads'].values():
            for hook in spec.get('hooks', []):
                self.assertTrue((root / hook).is_file(), hook)
        hook = (root / 'planning/evidence/load/hooks/f2-crash.lisp').read_text()
        host = (root / 'host/native/io.lisp').read_text() + (root / 'host/native/owner.lisp').read_text()
        for boundary in faults.BOUNDARIES:
            self.assertIn(boundary, hook)
            self.assertIn('(defun ' + boundary + ' ', host)
        self.assertEqual(faults.sample_points(100, 3), [1, 51, 100])
        self.assertEqual(faults.sample_points(2, 3), [1, 2])


class FakeSocket:
    """A scripted socket: greeting preloaded, replies chosen from each sendall."""
    def __init__(self, responder):
        self.responder, self.buf, self.sent = responder, bytearray(b"200 hi\r\n"), []

    def settimeout(self, t): pass
    def setsockopt(self, *a): pass
    def connect(self, addr): pass
    def close(self): pass
    def shutdown(self, how): pass

    def sendall(self, data):
        self.sent.append(bytes(data))
        self.buf.extend(self.responder(bytes(data)))

    def recv(self, n):
        out, self.buf = bytes(self.buf[:n]), self.buf[n:]
        return out


def respond(data):
    if data.startswith(b"POST"):
        return b"340 go\r\n"
    if data.endswith(b".\r\n") and not data.startswith((b"STAT", b"ARTICLE", b"LIST")):
        return b"240 ok\r\n"
    if data.startswith(b"LIST ACTIVE"):
        return b"215 list\r\n.\r\n"
    if data.startswith(b"ARTICLE"):
        return b"220 1 <a@b>\r\nSubject: x\r\n\r\nbody\r\n.\r\n"
    return b"223 1 <a@b>\r\n"


class TraceRecorderTests(unittest.TestCase):
    def setUp(self):
        from tools.load import faults
        self.faults = faults
        self.real, self.socks = faults.socket.socket, []
        def make():
            self.socks.append(FakeSocket(respond))
            return self.socks[-1]
        faults.socket.socket = make
        self.addCleanup(setattr, faults.socket, "socket", self.real)

    def test_sequential_two_connections(self):
        h = self.faults.History()
        with self.faults.Client(1, h) as a:
            self.assertTrue(a.post(1).startswith(b"240"))
        with self.faults.Client(1, h) as b:
            b.command("ARTICLE <a@b>")
        snap = h.recorder.snapshot(h.ops)
        self.assertTrue(snap["sequential"])
        kinds = [(x["t"], x.get("c"), x.get("until")) for x in snap["steps"]]
        self.assertEqual(kinds[:7], [("conn", 0, None), ("read", 0, "line"), ("send", 0, None), ("read", 0, "line"),
                                     ("send", 0, None), ("read", 0, "line"), ("close", 0, None)])
        self.assertEqual(snap["steps"][-2]["until"], "dot")
        self.assertEqual(snap["steps"][2]["hex"], b"POST\r\n".hex())
        self.assertEqual(bytes.fromhex(snap["steps"][4]["hex"])[-3:], b".\r\n")

    def test_interleaved_connections_are_not_sequential(self):
        h = self.faults.History()
        held = self.faults.Client(1, h)
        op = held.begin("ARTICLE", {"command": "ARTICLE <a@b>"}, b"ARTICLE <a@b>\r\n")
        held.mark_read("line"); held.line()          # status only; the body stays owed
        with self.faults.Client(1, h) as other:
            other.command("STAT <a@b>")
        held.close()
        snap = h.recorder.snapshot(h.ops)
        self.assertFalse(snap["sequential"])
        # two sends on different connections with no read between them
        h2 = self.faults.History()
        a, b = self.faults.Client(1, h2), self.faults.Client(1, h2)
        a.begin("STAT", {"command": "STAT"}, b"STAT\r\n")
        b.begin("STAT", {"command": "STAT"}, b"STAT\r\n")
        self.assertFalse(h2.recorder.snapshot(h2.ops)["sequential"])

    def test_fragments_are_separate_sends(self):
        h = self.faults.History()
        with self.faults.Client(1, h) as c:
            wire, ranges = self.faults.wire_operations([("STAT", {"command": "STAT <a@b>"})], h)
            for piece in (wire[:3], wire[3:]):
                idx = c.send_raw(piece)
            snap = h.recorder.snapshot(h.ops)
        sends = [x for x in snap["steps"] if x["t"] == "send"]
        self.assertEqual([bytes.fromhex(x["hex"]) for x in sends], [b"STA", b"T <a@b>\r\n"])
        self.assertTrue(snap["sequential"])

    def test_f2_like_campaign_trace(self):
        import json, os, tempfile
        from types import SimpleNamespace
        faults = self.faults
        run = SimpleNamespace(cell_id="F2", label="F2-x-A-r1", node=None)
        campaign = faults.Campaign.__new__(faults.Campaign)
        campaign.run, campaign.ph, campaign.serial = run, {}, 0
        campaign.traces, campaign.trace_serial, campaign.last_history = [], 0, None
        campaign.meta = {"schema": 1, "cell": "F2", "store": {"init_flags": ["--x"], "groups": ["fn.test"], "fixture": None},
                         "sbcl_user_args": "--dynamic-space-size 1GB"}
        node = SimpleNamespace(port=1, pid=7, work=Path(tempfile.mkdtemp()), env={}, start=lambda timeout=0: 0.1)
        campaign.recovery = 60
        h = campaign.history()
        campaign.start(node, h, ("fnn-durable-barrier", 3))
        with faults.Client(1, h) as c:
            c.post(0)
        campaign.start(node, h, ("*", 1))
        campaign.start(node, h)
        with faults.Client(1, h) as c:
            c.post(1000000)
        h.plan("POST", {"i": 5, "msgid": "<m>", "sha256": "0"})          # never attempted
        faults.inventory(1, h)
        trace = campaign.snapshot(h)
        types = [x["t"] for x in trace["steps"]]
        self.assertEqual(types[:2], ["start", "crash"])
        self.assertEqual(trace["steps"][1], {"t": "crash", "boundary": "fnn-durable-barrier", "hit": 3})
        i = types.index("restart")
        self.assertEqual(trace["steps"][i + 1], {"t": "crash", "boundary": "*", "hit": 1})
        self.assertEqual(types[i + 2], "restart")
        self.assertEqual(types[-1], "inventory")
        self.assertNotIn("crash", types[i + 2:])
        self.assertEqual(types.count("inventory"), 1)           # inventory's own connections are folded in
        self.assertTrue(trace["sequential"])
        for op in trace["ops"]:
            if op["outcome"] == "not-attempted":
                self.assertIsNone(op["step"])
            else:
                self.assertTrue(0 <= op["step"] < len(trace["steps"]))
                self.assertIn(trace["steps"][op["step"]]["t"], ("send", "inventory"))
        os.environ["FN_LOAD_TRACE_DIR"] = tempfile.mkdtemp()
        self.addCleanup(os.environ.pop, "FN_LOAD_TRACE_DIR")
        path = campaign.emit(trace, "reference")
        self.assertTrue(path.endswith("F2-x-A-r1-F2-reference-001.json"))
        loaded = json.loads(Path(path).read_text())
        self.assertEqual((loaded["schema"], loaded["cell"], loaded["id"]), (1, "F2", "F2-reference-001"))
        self.assertEqual(loaded["steps"], trace["steps"])
        self.assertEqual(campaign.traces, [path])
        TraceRecorderTests.example = loaded

    def test_control_step_and_violation_trace(self):
        import tempfile, os
        from types import SimpleNamespace
        faults = self.faults
        os.environ["FN_LOAD_TRACE_DIR"] = tempfile.mkdtemp()
        self.addCleanup(os.environ.pop, "FN_LOAD_TRACE_DIR")
        campaign = faults.Campaign.__new__(faults.Campaign)
        campaign.run, campaign.traces, campaign.trace_serial, campaign.meta = SimpleNamespace(cell_id="F3"), [], 0, {}
        h = campaign.history()
        op = h.plan("CONTROL", {"words": ["pins"]})
        h.sent(op)
        op["step"] = h.recorder.control(["pins"])
        def replay(ops, prop, detail):
            campaign.history().recorder.start()
            return True
        out = faults.report(h, [("P4-RECLAIM", "d")], ["P4-RECLAIM"], replay, 4, campaign)
        v = out["violations"][0]
        self.assertTrue(Path(v["trace"]).is_file())
        self.assertEqual(json.loads(Path(v["trace"]).read_text())["steps"], [{"t": "start"}])
        self.assertEqual(h.recorder.snapshot(h.ops)["steps"], [{"t": "control", "words": ["pins"]}])


class ImageSweepTests(unittest.TestCase):
    def args(self, **over):
        values = dict(cmd='plan', label='new', baseline='old', box='both',
                      image_dir='/images/main', persvati_image_dir='/images/persvati')
        values.update(over)
        return SimpleNamespace(**values)

    def test_matrix_resolves_and_hbox_capacity_is_structural(self):
        data = sweep.load()
        hbox = [ln for ln in data['lanes'] if ln['box'] == 'hbox']
        self.assertEqual(sorted(ln['memory'] for ln in hbox), ['16G', '16G', '32G'])
        cells = [c for ln in data['lanes'] for c in ln['cells']]
        for c in cells:
            workloads.resolve(c['cell'])
        self.assertEqual(len(cells), 26)
        for ln in hbox:
            self.assertTrue(all(c.get('memory', ln['memory']) == ln['memory'] for c in ln['cells']))
            self.assertNotIn(' &', sweep.queue_script(self.args(), ln, data))
        w15 = next(c for c in cells if c['cell'] == 'W15')
        self.assertEqual(w15['sweep'], ['1k', '10k', '25k', '50k', '100k'])
        self.assertEqual(w15['image'], 'fn-host-developer')

    def test_plan_is_offline_contains_controls_and_valid_shell(self):
        data = sweep.load()
        with patch('sys.stdout', new_callable=io.StringIO) as out, patch.object(driver, 'ssh') as ssh:
            self.assertEqual(sweep.main(['plan', '--image-dir', '/image with spaces', '--label', 'test']), 0)
        ssh.assert_not_called()
        text = out.getvalue()
        for token in ('flock /tank/fn/scratch/timing-12-23.lock', 'taskset -c 12-23',
                      'busy_cores', 'probe --out', 'MemoryMax=', 'exit', '75', 'sleep 240',
                      'SWARM_MEM_MAX=', 'swarm-build timeout', 'chmod +x',
                      'setsid nohup timeout', '2>&1 < /dev/null &', '.pid', '.done', '.skips',
                      'work-nvme-test', '--readers 1,16 --runs 3 --mode full'):
            self.assertIn(token, text)
        self.assertEqual(text.count('setsid nohup timeout'), 4)
        subprocess.run(['bash', '-n'], input=text, text=True, check=True, timeout=5)
        for ln in data['lanes']:
            subprocess.run(['bash', '-n'], input=sweep.queue_script(self.args(), ln, data),
                           text=True, check=True, timeout=5)
        self.assertLess(text.index('chmod +x'), text.index('setsid nohup timeout'))

    def test_install_uses_shared_shipper_short_ssh_and_reports_pids(self):
        args = self.args(cmd='install')
        with patch.object(driver, 'ssh', return_value=SimpleNamespace(check_returncode=lambda: None, stdout='pid: 123\n')) as ssh, \
                patch.object(driver, 'ship_tree') as ship, patch('sys.stdout', new_callable=io.StringIO) as out:
            self.assertEqual(sweep.cmd_plan_install(args), 0)
        self.assertEqual(ship.call_count, 2)
        self.assertEqual(ssh.call_count, 4)
        self.assertTrue(all(call.kwargs['timeout'] == 30 for call in ssh.call_args_list))
        self.assertIn('pid: 123', out.getvalue())
        self.assertIn('/images/persvati/fn-host', ssh.call_args_list[0].args[1])
        self.assertIn('/images/main/fn-host', ssh.call_args_list[2].args[1])
        with patch.object(driver, 'ssh', side_effect=subprocess.CalledProcessError(1, 'ssh')), \
                patch.object(driver, 'ship_tree') as ship:
            with self.assertRaises(subprocess.CalledProcessError):
                sweep.cmd_plan_install(args)
        ship.assert_not_called()

    def test_probe_samples_five_seconds_and_skips_above_four(self):
        with tempfile.TemporaryDirectory() as tmp:
            args = SimpleNamespace(image=tmp + '/fn-host', out=tmp + '/admission.json')
            for busy, expected in ((4.0, 0), (4.01, 75), (None, 75)):
                with patch.object(driver, 'busy_cores', return_value=busy) as probe, \
                        patch.object(driver, 'loadavg', return_value=[1, 1, 1]):
                    self.assertEqual(sweep.cmd_probe(args), expected)
                probe.assert_called_once_with(list(range(12, 24)), 5.0)
                self.assertEqual(json.loads(Path(args.out).read_text())['box']['busy_cores_start'], busy)

    def test_table_reds_first_baseline_pairing_and_quiet_rule(self):
        quiet = dict(name='persvati', busy_cores_set='12-23', pinned=list(range(12, 24)),
                     busy_cores_start=4.0, busy_cores_end=1.0, loadavg_start=[1], loadavg_end=[1])
        bars = [{'id': 'TIME', 'cell': 'W2', 'quantity': 'p99', 'time': True, 'source': 'test',
                 'checks': [{'metric': 'lat', 'cmp': 'le', 'threshold': 50}]},
                {'id': 'MEM', 'cell': 'W13', 'quantity': 'memory', 'source': 'test',
                 'checks': [{'metric': 'mem', 'cmp': 'le', 'threshold': 100}]}]
        cr = cell_result(cell='W2@10k/R16', box=quiet, metrics={'lat': 20})
        bad = cell_result(metrics={'mem': 200})
        old = cell_result(cell='W2@10k/R16', box=quiet, metrics={'lat': 10})
        table = sweep.render_table([('quiet', cr), ('bad', bad)], [('quiet', old)], bars)
        self.assertIn('| MEM |', table.splitlines()[2])
        self.assertIn('| 20 | PASS | 10 | 2 |', table)
        self.assertIn('core sha=' + 'ab' * 32, table)
        self.assertEqual(table.count('| bar id |'), 1)
        for change in ({'busy_cores_start': 4.01}, {'busy_cores_start': None}, {'name': 'hbox'},
                       {'busy_cores_set': '0-11'}, {'pinned': None}, {'busy_cores_end': 5}):
            cr['box'] = dict(quiet, **change)
            row = sweep.table_rows([('quiet', cr)], bars)[0]
            self.assertEqual(row['verdict'], 'not judged', change)
        # End load does not waive the start rule, and memory remains judged.
        self.assertEqual(sweep.table_rows([('bad', bad)], bars)[0]['verdict'], 'FAIL')

    def test_missing_cell_is_visible_and_fetch_does_not_write_evidence(self):
        data = sweep.load()
        data['lanes'] = [dict(data['lanes'][0], cells=[data['lanes'][0]['cells'][0]])]
        with patch.object(driver, 'fetch_run', side_effect=RuntimeError('missing result')) as fetch:
            records = sweep.fetch_records('new', 'persvati', data)
        self.assertEqual(len(records), 1)
        self.assertIn('missing result', sweep.render_table(records))
        self.assertNotIn(str(driver.ROOT), fetch.call_args.args[2].as_posix())

    def test_w7_complete_matrix_and_missing_hit_counters(self):
        data = sweep.load()
        spec = next(c for ln in data['lanes'] for c in ln['cells'] if c['cell'] == 'W7')
        raw = []
        for r in (1, 16):
            for i in range(3):
                raw.append(dict(cell='W7@scale/R%d' % r, arm='new', mode='full', run_index=i,
                                cmd={'ARTICLE': {'n': 200, 'p50_ms': 1, 'p99_ms': r,}},
                                rate={'article_per_s': 200}, extent={'hit_ratio': 0.9},
                                quiet_check={'mean': 0.1}, core_busy_measured={str(c): 0.1 for c in range(12, 24)},
                                loadavg_start=2, loadavg_end=2, errors=0))
        admission = {'box': {'name': 'persvati', 'busy_cores_set': '12-23', 'pinned': list(range(12, 24))}}
        cr = sweep.extent_result(raw, admission, spec)
        self.assertEqual(cr['metrics']['extent.p99_ratio'], 16)
        self.assertEqual(cr['metrics']['extent.hit_non_decreasing'], 1)
        self.assertEqual(sweep.table_rows([('w7', cr)], data['w7_bars'])[0]['verdict'], 'FAIL')
        self.assertEqual(sweep.extent_result(raw[:-1], admission, spec)['metrics'], {})
        raw[-1]['extent']['hit_ratio'] = None
        self.assertIsNone(sweep.extent_result(raw, admission, spec)['metrics']['extent.hit_non_decreasing'])
        raw[-1]['errors'] = 1
        self.assertEqual(sweep.extent_result(raw, admission, spec)['metrics'], {})

    def test_w6q_uses_catchup_metric_derivation(self):
        with patch.object(peers, 'derive_catchup') as derive:
            cells.derive('catchup-quiet', [])
        derive.assert_called_once()

    def test_queue_releases_lock_before_retry_and_records_failures(self):
        # Execute generated bash against fake wrappers, never a box or image.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bindir = root / 'bin'
            bindir.mkdir()
            (root / 'ship/sweep-new').mkdir(parents=True)
            wrappers = {
                'systemd-run': 'shift 5; exec "$@"',
                'flock': 'shift; echo hold >> "$EVENTS"; "$@"; rc=$?; echo release >> "$EVENTS"; exit "$rc"',
                'taskset': 'shift 2; exec "$@"',
                'timeout': 'shift; exec "$@"',
                'sleep': 'echo sleep >> "$EVENTS"',
                'python3': '''if [ "$3" = probe ]; then
  if [ ! -f "$EVENTS.once" ]; then
    touch "$EVENTS.once"; echo '{"busy":5}' > "$5"; exit 75
  fi
  echo '{"busy":1}' > "$5"; exit 0
fi
echo cell >> "$EVENTS"; exit 23''',
            }
            for name, body in wrappers.items():
                exe = bindir / name
                exe.write_text('#!/bin/bash\n' + body + '\n')
                exe.chmod(0o755)
            data = sweep.load()
            lane = dict(data['lanes'][0], cells=data['lanes'][0]['cells'][:2])
            with patch.object(driver, 'BOX_BASE', tmp):
                script = sweep.queue_script(self.args(), lane, data)
            env = dict(os.environ, PATH=str(bindir) + ':' + os.environ['PATH'], EVENTS=str(root / 'events'))
            subprocess.run(['bash'], input=script, text=True, env=env, check=True, timeout=5)
            events = (root / 'events').read_text().splitlines()
            self.assertEqual(events, ['hold', 'release', 'sleep', 'hold', 'cell', 'release', 'hold', 'cell', 'release'])
            done = (root / 'runs/new-persvati.done').read_text()
            self.assertEqual(done.count('rc=75'), 1)
            self.assertEqual(done.count('rc=23'), 2)
            self.assertIn('busy=', (root / 'runs/new-persvati.skips').read_text())
            self.assertEqual((root / 'runs/new-w2-r1/status').read_text().strip(), 'done rc=23')

    def test_table_uses_manifest_and_fetches_baseline_without_stdout_noise(self):
        data = sweep.load()
        lane = dict(data['lanes'][1], cells=[data['lanes'][1]['cells'][0]])
        data = dict(data, lanes=[lane], boxes=['hbox'], baseline='old')
        def fetch_manifest(box, remote, dest):
            if box == 'persvati':
                raise RuntimeError('not installed here')
            (Path(dest) / 'manifest.json').write_text(json.dumps(data))
        def fetch_run(box, label, dest):
            cr = cell_result(metrics={'rss_kib.hwm': 200000 if label.startswith('new') else 100000})
            (Path(dest) / 'result.json').write_text(json.dumps({'cells': [cr]}))
        with patch.object(driver, 'fetch_files', side_effect=fetch_manifest), \
                patch.object(driver, 'fetch_run', side_effect=fetch_run) as fetch, \
                patch('sys.stdout', new_callable=io.StringIO) as out:
            self.assertEqual(sweep.main(['table', '--label', 'new']), 0)
        self.assertEqual([c.args[:2] for c in fetch.call_args_list], [('hbox', 'new-w13'), ('hbox', 'old-w13')])
        self.assertTrue(out.getvalue().startswith('| bar id |'))
        self.assertIn('| 200000 | FAIL | 100000 | 2 |', out.getvalue())

    def test_ship_payload_is_shared_and_includes_w7_hook(self):
        self.assertTrue(any('w7hook.lisp' in src for src, _ in driver.SHIP_FILES))
        with patch.object(driver, 'ssh', return_value=SimpleNamespace(check_returncode=lambda: None)) as ssh, \
                patch.object(driver.subprocess, 'run', return_value=SimpleNamespace(returncode=0)) as run:
            driver.ship_tree('hbox', '/ship')
        self.assertEqual(run.call_count, len(driver.SHIP_FILES))
        self.assertEqual(ssh.call_args.kwargs['timeout'], 30)

    def test_rejects_label_path_traversal(self):
        for label in ('../x', 'a/b', 'x\ny', '-x', 'x;touch y'):
            with self.assertRaises(ValueError):
                sweep.safe_name(label)


class FaultSlotAndIndexTests(unittest.TestCase):
    def post(self, h, mid, value='original', duplicate=None, reply=b'240 accepted\r\n'):
        args = dict(msgid=mid, sha256=value)
        if duplicate:
            args['duplicate'] = duplicate
        op = h.plan('POST', args)
        h.sent(op)
        h.complete(op, reply)
        return op

    def probe(self, h, cell, mid, kind='ARTICLE', epoch=None, value='original', reply=None):
        op = h.plan(kind, dict(msgid=mid, command=kind + ' ' + mid))
        op.update(probe=cell, epoch=epoch, body_sha256=value, held=cell == 'F1')
        h.sent(op)
        if reply is None:
            reply = ('%s 1 %s retrieved\r\n' % ('220' if kind == 'ARTICLE' else '223', mid)).encode()
        h.complete(op, reply)
        return op

    def index_history(self):
        from tools.load.faults import History
        h = History()
        self.post(h, '<present>')
        self.post(h, '<present>', duplicate='same', reply=b'441 duplicate\r\n')
        self.post(h, '<present>', 'changed', duplicate='different', reply=b'441 conflict\r\n')
        for epoch in ('before', 'after'):
            for kind in ('STAT', 'ARTICLE'):
                self.probe(h, 'F4', '<present>', kind, epoch)
                self.probe(h, 'F4', '<absent>', kind, epoch, reply=b'430 no such article\r\n')
        return h

    def test_collision_search_uses_oracle_low_bits_and_finite_budget(self):
        from tools.load.faults import collision_search
        seen = []
        def tag(mid):
            seen.append(mid)
            return int(mid) * 17 + 3
        result = collision_search(map(str, range(100)), tag, 4, bits=3, bucket=3)
        self.assertEqual(result, ['0', '8', '16', '24'])
        self.assertEqual(len(seen), 25)
        self.assertEqual(collision_search(['0', '0', '8'], tag, 4, bits=3, bucket=3), ['0', '8'])
        self.assertEqual(collision_search(['1', '2'], tag, 1, bits=3, bucket=3), [])
        for bits in (0, 61):
            with self.assertRaises(ValueError):
                collision_search(['0'], tag, 1, bits=bits)

    def test_f1_requires_real_reuse_and_publication_during_hold(self):
        from tools.load.faults import History, verify_slot_reuse, report, metrics, f1_evidence
        h = History()
        self.post(h, '<a>')
        op = self.probe(h, 'F1', '<a>')
        for route, function in (('E', 'fnn-extent-cache-store'), ('W', 'fnn-extent-window-release')):
            op['route'] = route
            held = 'pool %s funded\nheld %s %s 2\n' % (route, route, function)
            row = 'released %s %s 12 1 11 10\n' % (route, function)
            ev = dict(f1_evidence(held + row, route), publication='installed', complete=True)
            self.assertEqual(ev['held_function'], function)
            self.assertEqual(ev['held_call'], 2)
            fs, checked = verify_slot_reuse(h.ops, ev)
            self.assertEqual(fs, [])
            self.assertEqual(set(checked), {'P4-RECLAIM', 'P2-IDENTITY'})
            keys = ['held', 'released', 'publication', 'installs', 'drop_calls', 'evictions', 'reuses', 'complete']
            if route == 'W':
                keys.append('funded_pool')
            for key in keys:
                missing = dict(ev, **{key: 0})
                fs, checked = verify_slot_reuse(h.ops, missing)
                self.assertEqual(checked, [], (route, key))
                self.assertEqual(metrics(report(h, fs, checked)), {}, (route, key))
            for bad in (row.replace('released', 'timeout'), row[:-1], row[:-4], row.replace('12', '-1'),
                        row.replace('12', 'bad'), row.replace(function, 'wrong-function')):
                self.assertNotIn('released', f1_evidence(held + bad, route))
            self.assertNotIn('released', f1_evidence(row, route))
            other = 'W' if route == 'E' else 'E'
            self.assertNotIn('released', f1_evidence(held + row, other))
            self.assertEqual(verify_slot_reuse(h.ops, dict(ev, route=other))[1], [])

    def test_f1_both_routes_required_and_findings_survive_missing_coverage(self):
        from tools.load import faults
        props = ['P4-RECLAIM', 'P2-IDENTITY']
        for missing in (None, 'E', 'W'):
            seen = []
            def route(campaign, h, ph, name):
                seen.append(name)
                measured = name != missing
                notes = dict(status='measured' if measured else 'not-measured', reason='no reuse')
                return notes, [('P2-IDENTITY', name + ': changed bytes')], props if measured else []
            with patch.object(faults, 'f1_route', side_effect=route), \
                    patch.object(faults.Campaign, 'emit'):
                out = faults.slot_reuse(SimpleNamespace(), {})
            self.assertEqual(seen, ['E', 'W'])
            self.assertEqual(set(out['routes']), {'E', 'W'})
            self.assertEqual(set(out['faults']['checked']), set(props) if missing is None else set())
            self.assertEqual(len(out['faults']['violations'][0]['details']), 2)
            if missing:
                self.assertEqual(out['status'], 'not-measured')
                self.assertIn(missing + ': no reuse', out['reason'])

    def test_f1_route_orchestration_release_cleanup_and_late_publication(self):
        import threading
        import time
        from tools.load import faults
        from tools import msgid_measure
        for route in ('E', 'W'):
            for mode in ('reuse', 'no-reuse', 'blocked-publication', 'unreached', 'seed-refused'):
                with self.subTest(route=route, mode=mode), tempfile.TemporaryDirectory() as tmp:
                    work = Path(tmp)
                    node = SimpleNamespace(work=work, env={}, port=1, err_n=0, stop=lambda: None)
                    h, churn_started = faults.History(), threading.Event()
                    release, witness = work / 'f1-release', work / 'f1-witness'
                    function = faults.F1_FUNCTIONS[route]
                    campaign = SimpleNamespace(deadline=1, recovery=.15, node=lambda **kw: node)
                    starts, controls = [], []
                    def start(node, history):
                        starts.append(dict(node.env))
                        node.err_n += 1
                        (work / ('owner.%d.err' % node.err_n)).touch()
                    def wait_release():
                        end = time.monotonic() + 2
                        while not release.exists() and time.monotonic() < end:
                            time.sleep(.002)
                        if not release.exists():
                            raise TimeoutError('test hook was not released')
                    def control(node, history, *words):
                        controls.append(words)
                        if len(controls) == 2:
                            if not churn_started.wait(2):
                                raise TimeoutError('publication prevented competing read dispatch')
                            if mode == 'blocked-publication':
                                wait_release()
                        return 0, 'queued'
                    campaign.start, campaign.control = start, control
                    case = self
                    class SeedClient:
                        def __init__(self, *args):
                            pass
                        def __enter__(self):
                            return self
                        def __exit__(self, *args):
                            pass
                        def post(self, i, size):
                            case.assertEqual(size, 524288)
                            if mode == 'seed-refused':
                                return b'441 refused\r\n'
                            case.post(h, msgid_measure.msgid(i))
                            return b'240 accepted\r\n'
                    def probe(client, mid, cell, held=False, route=None):
                        if held:
                            if mode != 'unreached':
                                witness.write_text('pool %s funded\nheld %s %s 1\n' % (route, route, function))
                                wait_release()
                                n = 0 if mode == 'no-reuse' else 1
                                with witness.open('a') as f:
                                    f.write('released %s %s 2 1 %d %d\n' % (route, function, n, n))
                        else:
                            churn_started.set()
                        op = self.probe(h, cell, mid)
                        op.update(route=route, held=held)
                    with patch.object(faults, 'Client', SeedClient), \
                            patch.object(faults, 'fault_probe', side_effect=probe), \
                            patch.object(faults, 'wait_log', return_value='CHECKPOINT auto sequence=2'):
                        notes, findings, checked = faults.f1_route(campaign, h, {'cold_reads': 2}, route)
                    self.assertTrue(release.exists())
                    self.assertEqual(findings, [])
                    self.assertEqual(notes['held_function'], function)
                    self.assertEqual(bool(checked), mode == 'reuse')
                    if mode != 'seed-refused':
                        self.assertEqual(starts[1]['FN_LOAD_F1_ROUTE'], route)
                    if mode in ('reuse', 'no-reuse', 'blocked-publication'):
                        self.assertTrue(churn_started.is_set())
                        self.assertEqual(controls, [('store', 'checkpoint')] * 2)
                    if mode == 'blocked-publication':
                        self.assertNotIn('publication', notes)
                    if route == 'W' and mode == 'unreached':
                        self.assertIn('Funded pool not observed', notes['reason'])
                        self.assertIn(':unpriced-complete-cold-profile', notes['reason'])

    def test_f1_other_article_bytes_and_unnamed_or_partial_refusals_fail(self):
        from tools.load.faults import History, verify_slot_reuse
        h = History()
        self.post(h, '<a>')
        op = self.probe(h, 'F1', '<a>', value='another article')
        fs, _ = verify_slot_reuse(h.ops, {})
        self.assertEqual({p for p, _ in fs}, {'P4-RECLAIM', 'P2-IDENTITY'})
        op['reply_line'] = '430 no such article\r\n'
        self.assertEqual(verify_slot_reuse(h.ops, {})[0], [])
        op['reply_line'] = '430\r\n'
        self.assertTrue(verify_slot_reuse(h.ops, {})[0])
        op['outcome'] = 'attempted-uncertain'
        self.assertTrue(verify_slot_reuse(h.ops, {})[0])

    def test_f4_saturated_identity_and_restart_success(self):
        from tools.load.faults import verify_index_saturation
        h = self.index_history()
        fs, checked = verify_index_saturation(h.ops, dict(before=[3, 2048, 1, 1], after=[3, 2048, 1, 1]),
                                             {'<present>': 'original'}, ['<absent>'])
        self.assertEqual(fs, [])
        self.assertEqual(checked, ['P2-IDENTITY'])

    def test_f4_identity_is_judged_without_saturation_which_is_reported_apart(self):
        from tools.load.faults import verify_index_saturation, metrics, report, index_saturated
        h = self.index_history()
        for health in ({}, dict(before=[3, 2048, 0, 1], after=[3, 2048, 0, 1]),
                       dict(before=[3, 2048, 1, 1]), dict(before=[3, 2048, 1, 1], after=[3, 2048, 0, 1])):
            fs, checked = verify_index_saturation(h.ops, health, {'<present>': 'original'}, ['<absent>'])
            self.assertEqual(metrics(report(h, fs, checked)), {'faults.P2-IDENTITY.violations': 0})
            self.assertFalse(index_saturated(health))
        self.assertTrue(index_saturated(dict(before=[3, 2048, 1, 1], after=[3, 2048, 1, 1])))

    def test_f4_detects_duplicate_acceptance_even_with_same_bytes(self):
        from tools.load.faults import verify_index_saturation
        for duplicate in ('same', 'different'):
            h = self.index_history()
            op = next(o for o in h.ops if o['args'].get('duplicate') == duplicate)
            op['reply_line'] = '240 accepted\r\n'
            fs, _ = verify_index_saturation(h.ops, {}, {'<present>': 'original'}, ['<absent>'])
            self.assertIn(('P2-IDENTITY', 'duplicate accepted: <present>'), fs)

    def test_f4_detects_wrong_bytes_false_absence_and_false_presence(self):
        from tools.load.faults import verify_index_saturation
        for mid, kind, field, wrong in [('<present>', 'ARTICLE', 'body_sha256', 'wrong'),
                                       ('<present>', 'STAT', 'reply_line', '430 missing\r\n'),
                                       ('<present>', 'STAT', 'reply_line', '223 1 <other>\r\n'),
                                       ('<absent>', 'ARTICLE', 'reply_line', '220 1 <absent>\r\n'),
                                       ('<absent>', 'STAT', 'reply_line', '400 busy\r\n')]:
            h = self.index_history()
            op = next(o for o in h.ops if o.get('epoch') == 'after'
                      and o['args']['msgid'] == mid and o['kind'] == kind)
            op[field] = wrong
            fs, _ = verify_index_saturation(h.ops, {}, {'<present>': 'original'}, ['<absent>'])
            self.assertTrue(fs, (mid, kind, field))

    def test_f4_missing_probe_or_repost_cannot_pass(self):
        from tools.load.faults import verify_index_saturation
        h = self.index_history()
        health = dict(before=[3, 2048, 1, 1], after=[3, 2048, 1, 1])
        for dropped in h.ops:
            fs, checked = verify_index_saturation([o for o in h.ops if o is not dropped], health,
                                                 {'<present>': 'original'}, ['<absent>'])
            self.assertEqual(checked, [], dropped)
        h.ops[-1]['outcome'] = 'attempted-uncertain'
        self.assertEqual(verify_index_saturation(h.ops, health, {'<present>': 'original'}, ['<absent>'])[1], [])

    def test_new_fault_cells_dispatch_and_keep_f7_unimplemented(self):
        from tools.load import driver, faults
        data = workloads.load()
        for cell in ('F1', 'F4'):
            spec = data['workloads'][data['cells'][cell]]
            self.assertTrue(hasattr(driver.Run, 'phase_' + spec['phases'][0]['kind']))
            self.assertTrue(spec['hooks'])
        spec = data['workloads'][data['cells']['F7']]
        self.assertEqual(spec['phases'][0]['kind'], 'unimplemented')
        self.assertIn('PCK-ADOPT', spec['about'])
        self.assertEqual(faults.fault_environment({'FN_LOAD_F1_ARM': 'x', 'FN_LOAD_F4_REQUEST': 'x',
                                                 'FN_LOAD_CRASH_AT': 'x', 'PATH': '/bin'}), {'PATH': '/bin'})

    def test_not_measured_hook_reason_reaches_fault_bars(self):
        from tools.load import faults
        for cell, workload in [('F1', 'fault-slot-reuse'), ('F4', 'fault-index-saturation')]:
            reason = 'no actual reuse' if cell == 'F1' else 'no unplaced rows'
            props = ['P4-RECLAIM', 'P2-IDENTITY'] if cell == 'F1' else ['P2-IDENTITY']
            out = faults.report(faults.History(), [], [])
            out['not_measured'] = {'faults.%s.violations' % p: reason for p in props}
            m, nm = cells.derive(workload, [dict(name='fault', status='not-measured', faults=out)])
            m.update(faults.metrics(out))
            rows = result.judge_cell(cell_result(cell=cell, workload=workload, metrics=m, not_measured=nm), result.load_bars())
            self.assertEqual(len(rows), len(props))
            for row in rows:
                self.assertEqual(row['verdict'], 'NOT-MEASURED')
                self.assertIn(reason, str(row))

    def test_custom_post_records_its_original_identity_and_wire(self):
        from tools.load import faults
        h, sock = faults.History(), FakeSocket(respond)
        body = b'Message-ID: <collision@fn.test>\r\nSubject: original\r\n\r\noriginal\r\n'
        args = dict(msgid='<collision@fn.test>', sha256=faults.digest(body))
        with patch.object(faults.socket, 'socket', return_value=sock), faults.Client(1, h) as client:
            self.assertEqual(client.post_article(body, args), b'240 ok\r\n')
        self.assertEqual(h.ops[0]['args'], args)
        self.assertEqual(h.ops[0]['outcome'], 'completed')
        self.assertEqual(sock.sent, [b'POST\r\n', body + b'.\r\n'])


if __name__ == "__main__":
    unittest.main()
