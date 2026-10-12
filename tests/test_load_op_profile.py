"""Laptop controls for profile data and window isolation; no node image required."""
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from tools.load import cells, driver, op_profile, pub_profile, workloads


class ParserTests(unittest.TestCase):
    def test_flat_sprof(self):
        sample = Path(__file__).parent / "fixtures" / "load-sprof-flat.txt"
        rows = op_profile.parse_sprof(sample.read_text())
        self.assertEqual(len(rows), 3)
        self.assertEqual(rows[0], {"count": 60, "percent": 60.0,
                                  "cumulative_percent": 60.0, "function": "ACL2::FNN-CALL"})
        self.assertEqual(rows[1]["function"], "(SB-VM::OPTIMIZED-DATA-VECTOR-REF T)")
        self.assertEqual(len(op_profile.parse_sprof(sample.read_text(), limit=2)), 2)
        self.assertEqual(op_profile.parse_sprof("Number of samples: 0\n"), [])
        self.assertEqual(op_profile.parse_sprof(" 1 60 60.0 60 60.0 80 80.0 ACL2::FNN-CALL")[0], rows[0])

    def test_strace_optional_errors_column(self):
        text = '''% time     seconds  usecs/call     calls    errors syscall
 60.00    0.060000         200       300           write
 20.00    0.020000         100       200       10 futex
 20.00    0.020000         200       100           fdatasync
100.00    0.100000                   600       10 total
'''
        got = op_profile.parse_strace(text, 100)
        self.assertEqual(got["per_command"]["write"], 3)
        self.assertEqual(got["per_command"]["futex"], 2)
        self.assertEqual(got["per_command"]["fdatasync"], 1)
        self.assertEqual(got["per_command"]["rename"], 0)
        self.assertNotIn("total", got["per_command"])
        self.assertEqual(got["top20"][0]["syscall"], "write")
        with self.assertRaises(ValueError):
            op_profile.parse_strace("strace: attach: Operation not permitted", 100)

    def test_consed(self):
        self.assertEqual(op_profile.parse_consed("consed_bytes 6000 gc_ms 12.5 gcs 2\n", 100),
                         {"consed_bytes": 60, "gc_ms": .125, "gcs": .02})
        for text, n in (("", 100), ("consed_bytes 10 gc_ms 0 gcs 0", 0)):
            with self.assertRaises(ValueError):
                op_profile.parse_consed(text, n)

    def test_calls_separates_barrier_and_log_sync(self):
        text = '''window_ms 100 gc_ms 0 consed_mb 1
acl2-entry ACL2::ONE 300 12.0
acl2-entry ACL2::TWO 100 4.0
barrier ACL2::FNN-DURABLE-BARRIER 100 30.0
barrier ACL2::FNN-LOG-FDATASYNC 200 40.0
gate FNN-OWNER-GATE-LEAVE 100 3.0
'''
        got = op_profile.parse_calls(text, 100)
        self.assertEqual(got["acl2_calls_per_command"], 4)
        self.assertEqual(got["barriers"], {"count_per_command": 1, "ms_per_command": .3})
        self.assertEqual(got["fdatasyncs"], {"count_per_command": 2, "ms_per_command": .4})
        with self.assertRaises(ValueError):
            op_profile.parse_calls("window_ms 1 gc_ms 0 consed_mb 1\n", 100)

    def test_proc_deltas_and_missing_are_not_zero(self):
        before = {"cpu_s": 2, "io": {"syscr": 10}, "faults": {"minor": 3, "major": 0}}
        after = {"cpu_s": 3, "io": {"syscr": 20}, "faults": {"minor": 5, "major": 0}}
        got, missing = op_profile.clean_metrics(before, after, [.01] * 100,
                                               driver.res_mod.lat_stats([.01] * 100))
        self.assertEqual(got["cpu_ms"], 10)
        self.assertEqual(got["io"]["syscr"], .1)
        self.assertEqual(got["faults"]["minor"], .02)
        self.assertAlmostEqual(got["wall_ms"]["mean"], 10)
        self.assertIn("clean.io.rchar", missing)
        self.assertIn("clean.wall_ms.p99", missing)

    def test_cells_and_operation_variants(self):
        all_ops = workloads.resolve("OPPROF@10k")
        self.assertEqual(all_ops.workload, "op-prof")
        self.assertEqual(all_ops.spec["preset"], "scale-1m")
        self.assertEqual(all_ops.spec["store"]["fixture"], "curve/n{N}")
        self.assertEqual(all_ops.spec["store"]["preload"], 10000)
        self.assertEqual(all_ops.spec["phases"][0]["ops"], list(op_profile.OPS))
        for op in op_profile.OPS:
            one = workloads.resolve("OPPROF@10k/" + op)
            self.assertEqual(one.spec["phases"][0]["ops"], [op])
        self.assertEqual(workloads.resolve("OPPROF@50k/OVER40").spec["store"]["preload"], 50000)
        self.assertEqual(workloads.resolve("FLOOR").spec["phases"][0]["kind"], "floor")
        with self.assertRaises(workloads.WorkloadError):
            workloads.resolve("OPPROF@10k/UNKNOWN")
        # Initial store loading is never hooked by op_profile.
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(driver.cell_hooks(all_ops.spec, Path(d)), ([], {}))

    def test_not_measured_reaches_cell_result(self):
        _, nm = cells.derive("op-prof", [{"not_measured": {"GROUP.syscalls": "sudo denied"}}])
        self.assertEqual(nm["GROUP.syscalls"], "sudo denied")


class PublicationParserTests(unittest.TestCase):
    def test_exit_counters_are_operation_totals(self):
        got = pub_profile.parse_exit_consed("consed_bytes 6000 gc_ms 12.500000 cpu_ms 90.250000 write_bytes 8192\n")
        self.assertEqual(got, {"consed_bytes": 6000, "gc_ms": 12.5,
                               "profile_cpu_ms": 90.25, "profile_write_bytes": 8192})
        got = pub_profile.parse_exit_consed("consed_bytes 0 gc_ms 1.5d+1 cpu_ms 2e+2 write_bytes unavailable")
        self.assertEqual(got["gc_ms"], 15)
        self.assertEqual(got["profile_cpu_ms"], 200)
        self.assertIsNone(got["profile_write_bytes"])
        for text in ("", "consed_bytes -10 gc_ms 0 cpu_ms 0 write_bytes 0", "consed_bytes 10 gc_ms 0 gcs 1"):
            with self.assertRaises(ValueError):
                pub_profile.parse_exit_consed(text)

    def test_combined_report_parses_only_flat_frames(self):
        flat = (Path(__file__).parent / "fixtures/load-sprof-flat.txt").read_text()
        report = "=== flat ===\n" + flat + "=== graph ===\n 1 99 99.0 99 99.0 - GRAPH-ONLY\n"
        self.assertEqual(pub_profile.parse_exit_report(report), op_profile.parse_sprof(flat))
        with self.assertRaises(ValueError):
            pub_profile.parse_exit_report(flat)

    def test_publication_syscalls_are_integer_counts(self):
        text = '''% time seconds usecs/call calls errors syscall
 50.00 0.050000 100 500 pread64
 25.00 0.025000 100 250 1 openat
 25.00 0.025000 250 100 fdatasync
100.00 0.100000 850 1 total
'''
        got = pub_profile.parse_syscalls(text)
        self.assertEqual(got["counts"]["pread64"], 500)
        self.assertIsInstance(got["counts"]["pread64"], int)
        self.assertEqual(got["counts"]["fdatasync"], 100)
        self.assertEqual(got["counts"]["madvise"], 0)
        self.assertEqual(got["top20"][0], {"syscall": "pread64", "count": 500})
        with self.assertRaises(ValueError):
            pub_profile.parse_syscalls("strace: ptrace denied")

    def test_owner_open_path_is_observed(self):
        replay = pub_profile.parse_owner_open("noise\nOWNER-OPEN open=full-replay reason=missing ms=1234\n")
        self.assertEqual(replay["kind"], "replay")
        checkpoint = pub_profile.parse_owner_open("OWNER-OPEN open=checkpoint:50000 suffix=0 ms=800\n")
        self.assertEqual(checkpoint["kind"], "checkpoint")
        self.assertEqual(checkpoint["checkpoint_records"], 50000)
        with self.assertRaises(ValueError):
            pub_profile.parse_owner_open("LISTENING 8119")

    def test_publication_cell_resolution(self):
        for cell_id, n in (("PUBPROF@50k", 50000), ("PUBPROF@10k", 10000)):
            cell = workloads.resolve(cell_id)
            self.assertEqual(cell.workload, "pub-prof")
            self.assertEqual(cell.spec["store"]["preload"], n)
            self.assertEqual(cell.spec["store"]["fixture"], "curve/n{N}")
            self.assertTrue(cell.spec["store"]["require_fixture"])
            self.assertTrue(cell.spec["own_nodes"])
            self.assertEqual(cell.spec["preset"], "scale-1m")
            self.assertEqual(cell.spec["phases"][0]["kind"], "pub_profile")


class WindowTests(unittest.TestCase):
    def test_each_window_restarts_with_only_its_hook_and_warmup_is_excluded(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            launches, commands = [], []
            class Target:
                def launcher(self, work, hooks, env):
                    launches.append((list(hooks), dict(env)))
                    return "launcher", env
            node = SimpleNamespace(work=work, env={}, launcher="base", target=Target(), pid=123,
                                   port=1234, stop=lambda: None, start=lambda: None)
            class Conn:
                def __init__(self):
                    self.sock = SimpleNamespace(settimeout=lambda _: None, close=lambda: None)
                    self.stream = self.reader = object()
                def line(self, command):
                    commands.append(command)
                    return b"211 100 1 100 fn.test\r\n"
            run = driver.Run(node, {}, driver.Counters(), SimpleNamespace(out=str(work), box="local"))
            run.label = "test"
            run.conn = Conn
            def ready(path, seconds=15):
                path.touch()
                if path.name == "done":
                    (path.parent / "consed.txt").write_text("consed_bytes 100 gc_ms 0 gcs 0\n")
                    (path.parent / "timing.txt").write_text("window_ms 1 gc_ms 0 consed_mb 1\nacl2-entry ONE 2 1\n")
                    sample = Path(__file__).parent / "fixtures" / "load-sprof-flat.txt"
                    (path.parent / "sprof.000.txt").write_text(sample.read_text())
                    (path.parent / "sprof.000.graph.txt").write_text("graph")
            with patch.object(driver, "discover_ids", return_value=(["<fixture>"], "fn.test")), \
                 patch.object(driver, "proc_snapshot", return_value={"cpu_s": 1, "io": {}, "faults": {}}), \
                 patch.object(op_profile, "wait_file", side_effect=ready), \
                 patch.object(op_profile.time, "sleep"):
                out = op_profile.run(run, {"ops": ["GROUP"], "reps": 3, "warmup": 50}, driver)
            self.assertEqual(len(launches), 4)
            self.assertEqual([h[0][0].name for h in launches],
                             ["op-consed.lisp", "w6-prof.lisp", "w6-prof.lisp", "prof2.lisp"])
            self.assertEqual(len(commands), 4 * (1 + 50 + 3))
            got = out["op_profile"]["GROUP"]
            self.assertEqual(got["clean"]["n"], 3)
            self.assertEqual(got["calls"]["acl2_calls_per_command"], 2 / 3)
            self.assertIn("syscalls", got["not_measured"])
            self.assertTrue((work / "test/op-profile/GROUP/result.json").exists())
            self.assertEqual(node.env, {})
            self.assertEqual(node.launcher, "base")


if __name__ == "__main__":
    unittest.main()
