"""Laptop controls for profile data and window isolation; no node image required."""
import tempfile
import unittest
import json
import os
import shutil
import subprocess
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from tools.load import cells, driver, op_profile, pub_profile, workloads
from tools.load.profile_common import sanitize_environment


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

    def test_counter_duration_and_idle_correction_are_visible(self):
        self.assertEqual(op_profile.parse_consed("consed_bytes 6000 gc_ms 12.5 gcs 2 window_ms 2000", 100)["window_ms"], 2000)
        operations = {"GROUP": {"clean": {"n": 10, "window_ms": 1000, "consed_bytes": 5}, "not_measured": {}}}
        op_profile.apply_hook_overhead(operations, {"duration_s": 2, "consed_bytes": 400})
        self.assertEqual(operations["GROUP"]["clean"]["consed_bytes"], 5)
        self.assertEqual(operations["GROUP"]["clean"]["consed_bytes_corrected_estimate"], -15)
        self.assertIn("clean.gc_ms_corrected_estimate", operations["GROUP"]["not_measured"])

    def test_controller_subtraction_preserves_later_syncer_and_shared_frames(self):
        sidecar = "\n".join(json.dumps(row) for row in (
            dict(thread="fn-load-prof", function="SLEEP", count=60),
            dict(thread="fn owner", function="SLEEP", count=10),
            dict(thread="fn owner syncer", function="FDATASYNC", count=30)))
        rows = op_profile.parse_sprof("raw flat report", thread_samples=sidecar)
        self.assertEqual(rows[0], dict(count=30, percent=75.0, cumulative_percent=75.0, function="FDATASYNC"))
        self.assertEqual(rows[1], dict(count=10, percent=25.0, cumulative_percent=100.0, function="SLEEP"))
        with self.assertRaises(ValueError):
            op_profile.parse_thread_samples('{"thread":"owner","function":"F","count":-1}')
        with self.assertRaises(ValueError):
            op_profile.parse_sprof("Number of samples: 101", thread_samples=sidecar)

    def test_foreign_names_survive_flat_and_thread_parsing(self):
        name = "foreign function call_into_lisp_"
        flat = "Number of samples: 4\nSelf Total Cumul\n 1 4 100.0 4 100.0 4 100.0 - " + name
        raw = op_profile.parse_sprof(flat)
        sidecar = json.dumps(dict(thread="fn owner", function=name, count=4))
        self.assertEqual(op_profile.parse_sprof(flat, thread_samples=sidecar), raw)
        self.assertEqual(raw[0]["function"], name)

    def test_sprof_export_failures_preserve_flat_report_and_explain_controller(self):
        flat = (Path(__file__).parent / "fixtures/load-sprof-flat.txt").read_text()
        cases = (
            (None, None, "FileNotFoundError"),
            ("partial JSON", None, "JSONDecodeError"),
            (json.dumps(dict(thread="fn owner", function="F", count=-1)), None, "invalid sprof"),
            (json.dumps(dict(thread="fn owner", function="F", count=1)), None, "totals differ"),
            (None, 'The value "foreign function call_into_lisp_" is not of type SB-DI:DEBUG-FUN',
             "foreign function call_into_lisp_"),
        )
        for sidecar, error, reason in cases:
            with self.subTest(reason=reason), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                (directory / "sprof.000.txt").write_text(flat)
                if sidecar is not None:
                    (directory / "sprof.000.threads.jsonl").write_text(sidecar)
                if error is not None:
                    (directory / "sprof.000.threads.error.txt").write_text(error)
                rows, meta = op_profile.read_sprof_frames(directory)
                self.assertEqual(rows, op_profile.parse_sprof(flat))
                self.assertFalse(meta["controller_excluded"])
                self.assertEqual(meta["controller_samples_removed"], 0)
                self.assertIn(reason, meta["controller_exclusion_reason"])

    def test_sprof_valid_export_excludes_controller_and_missing_flat_is_an_error(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            with self.assertRaises(FileNotFoundError):
                op_profile.read_sprof_frames(directory)
            flat = (Path(__file__).parent / "fixtures/load-sprof-flat.txt").read_text()
            sidecar = "\n".join(json.dumps(row) for row in (
                dict(thread="fn-load-prof", function="SLEEP", count=20),
                dict(thread="fn owner", function="foreign function poll", count=80)))
            (directory / "sprof.000.txt").write_text(flat)
            (directory / "sprof.000.threads.jsonl").write_text(sidecar)
            rows, meta = op_profile.read_sprof_frames(directory)
            self.assertEqual(meta, dict(controller_excluded=True, controller_samples_removed=20))
            self.assertEqual(rows, [dict(count=80, percent=100.0, cumulative_percent=100.0,
                                         function="foreign function poll")])

    def test_current_sbcl_flat_column_order(self):
        text = "Self Total Cumul\n 1 60 60.0 80 80.0 60 60.0 - F\n 2 25 25.0 40 40.0 85 85.0 - G\n"
        self.assertEqual(op_profile.parse_sprof(text)[1]["cumulative_percent"], 85)

    def test_shared_environment_sanitizer(self):
        env = {"XL_PROF": "1", "XL_PROF_SECONDS": "3", "XL_HOOK": "old", "XL_PROF_DIR": "old",
               "FN_LOAD_PROF": "old", "FN_LOAD_CONSED_DIR": "old", "SBCL_USER_ARGS": "--heap", "PATH": "path"}
        self.assertEqual(sanitize_environment(env), {"SBCL_USER_ARGS": "--heap", "PATH": "path"})
        self.assertEqual(env["XL_PROF"], "1")  # caller's environment remains intact
        self.assertIs(op_profile.sanitize_environment, pub_profile.sanitize_environment)

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


class TracerIdentityTests(unittest.TestCase):
    def test_stop_checks_start_time_and_command_before_sudo_signal(self):
        with tempfile.TemporaryDirectory() as temp:
            trace = op_profile.Trace(77, Path(temp), 1)
            trace.pidfile.write_text("123")
            trace.proc = Mock()
            trace.proc.poll.return_value = None
            trace.identity = (123, 456)
            command = ["/usr/bin/strace", "-f", "-c", "-o", str(trace.summary)]
            for actual in ((457, command), (456, ["sbcl", "-o", str(trace.summary)]),
                           (456, ["strace", "-o", "another-window"])):
                with patch.object(trace, "read_identity", return_value=actual), patch.object(op_profile.subprocess, "run") as signal:
                    with self.assertRaises(RuntimeError):
                        trace.stop()
                    signal.assert_not_called()
                    self.assertIn("syscalls.stop", trace.not_measured)
            with patch.object(trace, "read_identity", return_value=(456, command)), \
                 patch.object(op_profile.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as signal:
                trace.stop()
                self.assertEqual(signal.call_args.args[0], ["sudo", "-n", "kill", "-INT", "123"])

    def test_stat_start_time_field_handles_parentheses_in_comm(self):
        with tempfile.TemporaryDirectory() as temp:
            trace = op_profile.Trace(77, Path(temp), 1)
            fields = ["S"] + ["0"] * 18 + ["98765"] + ["0"] * 3
            stat = "123 (strace (worker)) " + " ".join(fields)
            with patch.object(Path, "read_text", return_value=stat), \
                 patch.object(Path, "read_bytes", return_value=b"/usr/bin/strace\0-o\0window\0"):
                self.assertEqual(trace.read_identity(123), (98765, ["/usr/bin/strace", "-o", "window"]))


@unittest.skipUnless(shutil.which("sbcl"), "SBCL unavailable for image-free hook controls")
class HookRuntimeTests(unittest.TestCase):
    def lisp(self, code, directory, **extra_env):
        script = directory / "test.lisp"
        script.write_text('(defpackage "ACL2" (:use "COMMON-LISP"))\n' + code)
        env = sanitize_environment(os.environ)
        env.update(extra_env)
        result = subprocess.run([shutil.which("sbcl"), "--noinform", "--script", str(script)],
                                cwd=Path(__file__).resolve().parents[1], env=env,
                                capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 0, (result.stdout + result.stderr)[-4000:])
        return result.stdout

    def test_aborting_exit_forwards_when_all_reporting_files_fail(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            text = self.lisp('''
(in-package "ACL2")
(defun fnn-exit (&rest args) (throw 'forwarded args))
(load "planning/evidence/load/hooks/exit-prof.lisp")
(format t "FORWARDED ~s~%" (catch 'forwarded (fnn-exit 7 :abort t)))
''', directory, FN_LOAD_EXITPROF=str(directory / "missing-parent" / "report"))
            self.assertIn("FORWARDED (7 :ABORT T)", text)
            self.assertFalse((directory / "missing-parent").exists())

    def test_exit_baseline_excludes_profiler_and_observer_setup(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            self.lisp('''
(in-package "ACL2")
(require :sb-sprof)
(defvar *setup* nil)
(defvar *operation* nil)
(sb-int:encapsulate 'sb-sprof:start-profiling 'test-setup
 (lambda (fn &rest args)
   (setf *setup* (make-array (* 32 1024 1024) :element-type '(unsigned-byte 8) :initial-element 1))
   (apply fn args)))
(defun fnn-exit (&rest args) (throw 'forwarded args))
(load "planning/evidence/load/hooks/exit-prof.lisp")
(setf *operation* (make-array (* 1024 1024) :element-type '(unsigned-byte 8) :initial-element 1))
(catch 'forwarded (fnn-exit 0))
''', directory, FN_LOAD_EXITPROF=str(directory / "report"), FN_LOAD_EXITPROF_STOP=str(directory / "stop"))
            counters = pub_profile.parse_exit_consed((directory / "report.consed.txt").read_text())
            self.assertGreater(counters["consed_bytes"], 0)
            self.assertLess(counters["consed_bytes"], 2 * 1024 * 1024,
                            "32 MiB profiler setup must be outside the 1 MiB operation window")

    def test_trigger_poll_and_sleep_allocate_no_lisp_objects(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            text = self.lisp('''
(in-package "ACL2")
(load "planning/evidence/load/hooks/profile-support.lisp")
(let ((name (fn-load-trigger-name (sb-ext:posix-getenv "FN_TEST_TRIGGER"))))
 (dotimes (i 5) (fn-load-trigger-present-p name) (sleep 0.02))
 (let ((before (sb-ext:get-bytes-consed)))
   (dotimes (i 10000) (fn-load-trigger-present-p name))
   (dotimes (i 10) (fn-load-trigger-present-p name) (sleep 0.02))
   (let ((delta (- (sb-ext:get-bytes-consed) before)))
     (format t "POLL-BYTES ~d~%" delta))))
''', directory, FN_TEST_TRIGGER=str(directory / "absent"))
            self.assertIn("POLL-BYTES 0", text)

    def test_consed_end_counters_precede_tick_read_and_report_arithmetic(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            (directory / "start").touch()
            (directory / "stop").touch()
            self.lisp('''
(in-package "ACL2")
(defvar *controller* nil)
(defvar *tick-reads* 0)
(defvar *tick-work* nil)
(sb-int:encapsulate 'sb-thread:make-thread 'capture-controller
 (lambda (fn &rest args) (setf *controller* (apply fn args))))
(sb-int:encapsulate 'get-internal-real-time 'end-tick-work
 (lambda (fn)
   (when (and (equal (sb-thread:thread-name sb-thread:*current-thread*) "fn-load-consed")
              (= (incf *tick-reads*) 2))
     ;; Make contamination observable even with SBCL allocation regions. The
     ;; tick read and everything after it must be outside the raw counters.
     (setf *tick-work* (make-array (* 32 1024 1024)
                                  :element-type '(unsigned-byte 8) :initial-element 1))
     (sb-ext:gc :full t))
   (funcall fn)))
(load "planning/evidence/load/hooks/op-consed.lisp")
(sb-thread:join-thread *controller*)
(assert *tick-work*)
''', directory, FN_LOAD_CONSED_DIR=str(directory))
            counters = op_profile.parse_consed((directory / "consed.txt").read_text(), 1)
            self.assertLess(counters["consed_bytes"], 2 * 1024 * 1024,
                            "final tick conversion/reporting work must not enter the byte delta")
            self.assertEqual(counters["gcs"], 0)
            self.assertEqual(counters["gc_ms"], 0)

    def test_w6_legacy_and_triggered_controller_windows(self):
        for controlled in (False, True):
            with self.subTest(controlled=controlled), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                trigger = directory / "start"
                trigger.touch()
                env = {"FN_LOAD_PROF": str(directory / "report"),
                       "FN_LOAD_PROF_START": str(trigger)}
                if controlled:
                    env.update(FN_LOAD_PROF_INTERVAL="0.001", FN_LOAD_PROF_GRAPH="1",
                               FN_LOAD_PROF_MODE="alloc", FN_LOAD_PROF_WINDOW="0")
                text = self.lisp('''
(in-package "ACL2")
(require :sb-sprof)
(defvar *controller* nil)
(defvar *sampling* nil)
(defvar *events* nil)
(defvar *controlled* (sb-ext:posix-getenv "FN_LOAD_PROF_INTERVAL"))
(defvar *ready* (merge-pathnames "ready" (sb-ext:posix-getenv "FN_LOAD_PROF_START")))
(sb-int:encapsulate 'sb-thread:make-thread 'capture-controller
 (lambda (fn &rest args) (setf *controller* (apply fn args))))
(sb-int:encapsulate 'sb-sprof:start-profiling 'observe-start
 (lambda (fn &rest args)
   (declare (ignore fn))
   (assert (eql (not (null (probe-file *ready*))) (not (null *controlled*))))
   (push (cons :start args) *events*)
   (setf *sampling* t)))
(sb-int:encapsulate 'probe-file 'no-sampled-pathname-probes
 (lambda (fn &rest args) (assert (not *sampling*)) (apply fn args)))
(sb-int:encapsulate 'merge-pathnames 'no-sampled-pathname-building
 (lambda (fn &rest args) (assert (not *sampling*)) (apply fn args)))
(sb-int:encapsulate 'sleep 'observe-timed-window
 (lambda (fn seconds)
   (if *sampling*
       (progn (assert (not *controlled*)) (push (list :sleep seconds) *events*))
       (funcall fn seconds))))
(sb-int:encapsulate 'sb-sprof:stop-profiling 'observe-stop
 (lambda (fn) (declare (ignore fn)) (setf *sampling* nil) (push :stop *events*)))
(sb-int:encapsulate 'sb-sprof:report 'observe-report
 (lambda (fn &rest args)
   (declare (ignore fn)) (push (cons :report args) *events*) (write-line "test report")))
(sb-int:encapsulate 'sb-sprof:reset 'observe-reset
 (lambda (fn) (declare (ignore fn)) (push :reset *events*)))
(sb-int:encapsulate 'sb-sprof:map-traces 'empty-test-samples
 (lambda (fn &rest args) (declare (ignore fn args))))
(load "planning/evidence/load/hooks/w6-prof.lisp")
(sb-thread:join-thread *controller*)
(format t "EVENTS ~s~%" (reverse *events*))
''', directory, **env)
                text = " ".join(text.split())
                self.assertIn(":MAX-SAMPLES 400000", text)
                self.assertIn(":THREADS :ALL", text)
                self.assertIn(":REPORT :TYPE :FLAT :MAX 60", text)
                self.assertEqual(text.count(":START "), 1)
                self.assertEqual(text.count(":STOP"), 1)
                self.assertEqual(text.count(":RESET"), 1)
                if controlled:
                    self.assertIn(":MODE :ALLOC :SAMPLE-INTERVAL 0.001", text)
                    self.assertIn(":REPORT :TYPE :GRAPH :MAX 40", text)
                    self.assertTrue((directory / "done").exists())
                    self.assertTrue((directory / "report.000.threads.jsonl").exists())
                else:
                    self.assertIn(":MODE :CPU :SAMPLE-INTERVAL 0.01", text)
                    self.assertIn("(:SLEEP 120)", text)
                    self.assertNotIn(":TYPE :GRAPH", text)
                    self.assertFalse((directory / "ready").exists())
                    self.assertFalse((directory / "done").exists())
                    self.assertFalse((directory / "report.000.threads.jsonl").exists())
                self.assertTrue((directory / "report.000.txt").exists())

    def test_thread_export_names_all_recorded_frame_types_like_sprof_report(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            self.lisp('''
(in-package "ACL2")
(require :sb-sprof)
(load "planning/evidence/load/hooks/profile-support.lisp")
(defun frame-witness () 42)
(defvar *infos*
  (list "foreign function call_into_lisp_"
        (let ((name (concatenate 'string "foreign function named" (string (code-char 92)) "path")))
          (make-array (length name) :element-type 'character :initial-contents name
                                   :fill-pointer (length name)))
        'sb-fasl:*assembler-routines*
        (sb-di:fun-debug-fun #'frame-witness)
        (sb-kernel:fun-code-header #'frame-witness)
        nil))
;; Exercise the exporter with the same opaque INFO objects that samples hold.
;; Each trace starts with the live failure's foreign string; its last frame is
;; the self PC. These mocks replace traversal only, never the naming mapper.
(sb-int:encapsulate 'sb-sprof:map-traces 'test-frame-types
 (lambda (fn callback samples)
   (declare (ignore fn samples))
   (dolist (info *infos*) (funcall callback sb-thread:*current-thread* info))))
(sb-int:encapsulate 'sb-sprof::map-trace-pc-locs 'test-frame-types
 (lambda (fn callback info)
   (declare (ignore fn))
   (funcall callback "foreign function call_into_lisp_" 0)
   (funcall callback info 0)))
(fn-load-thread-samples (sb-ext:posix-getenv "FN_TEST_SIDECAR"))
;; Use the actual flat report as the oracle for string/symbol/debug-fun/code
;; names. Unknown NIL information is represented by its elsewhere count.
(let ((nodes (loop for info in *infos* when info collect
                   (let ((node (sb-sprof::make-node info)))
                     (setf (sb-sprof::node-count node) 1
                           (sb-sprof::node-accrued-count node) 1)
                     node))))
  (loop for node in nodes for i from 1 do (setf (sb-sprof::node-index node) i))
  (with-open-file (stream (sb-ext:posix-getenv "FN_TEST_FLAT")
                         :direction :output :if-exists :supersede)
    (sb-sprof::print-flat
      (sb-sprof::%make-call-graph :vertices nodes :sample-interval 0.001
          :sampling-mode :cpu :nsamples (length *infos*)
          :unique-trace-count (length *infos*) :elsewhere-count 1)
      :max 60 :stream stream)))
''', directory, FN_TEST_SIDECAR=str(directory / "threads.jsonl"),
                FN_TEST_FLAT=str(directory / "flat.txt"))
            samples = op_profile.parse_thread_samples((directory / "threads.jsonl").read_text())
            names = {row["function"] for row in samples}
            self.assertIn("foreign function call_into_lisp_", names)
            self.assertIn("foreign function named\\path", names)
            self.assertIn("elsewhere", names)
            self.assertEqual(sum(row["count"] for row in samples), 6)
            flat_names = {row["function"] for row in op_profile.parse_sprof((directory / "flat.txt").read_text())}
            self.assertEqual(flat_names, names - {"elsewhere"}, (directory / "flat.txt").read_text())

    def test_thread_sample_export_retains_a_later_created_syncer(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            self.lisp('''
(in-package "ACL2")
(load "planning/evidence/load/hooks/profile-support.lisp")
(require :sb-sprof)
(sb-sprof:start-profiling :mode :alloc :threads :all :max-samples 10000)
(let ((thread (sb-thread:make-thread
 (lambda () (let ((keep (make-array 1000)))
              (dotimes (i 1000) (setf (aref keep i) (make-array 10000 :initial-element i)))))
 :name "fn owner syncer")))
 (sb-thread:join-thread thread))
(sb-sprof:stop-profiling)
(let ((*standard-output* (make-broadcast-stream))) (sb-sprof:report :type :flat :max 1))
(fn-load-thread-samples (sb-ext:posix-getenv "FN_TEST_SIDECAR"))
''', directory, FN_TEST_SIDECAR=str(directory / "threads.jsonl"))
            rows = op_profile.parse_thread_samples((directory / "threads.jsonl").read_text())
            self.assertTrue(any(row["thread"] == "fn owner syncer" and row["count"] > 0 for row in rows))


class WindowTests(unittest.TestCase):
    def test_cell_idle_calibration_issues_no_commands(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            (work / "test").mkdir()
            target = SimpleNamespace(path="base", launcher=lambda work, hooks, env: ("hooked", env))
            node = SimpleNamespace(work=work, env={}, target=target, pid=123, launcher="base", stop=Mock(), start=Mock())
            run = SimpleNamespace(node=node, args=SimpleNamespace(out=str(work)), label="test", conn=Mock())
            def ready(path, seconds=15, **kwargs):
                path.write_text("1")
                if path.name == "done":
                    (path.parent / "consed.txt").write_text("consed_bytes 400 gc_ms 0 gcs 0 window_ms 2000")
            snapshots = []
            def snapshot(pid):
                # Both CPU reads precede stop: stop-file handling belongs to
                # neither the idle CPU delta nor the command-window CPU delta.
                self.assertFalse(any((work / "test").glob("hook-overhead-*/stop")))
                snapshots.append(pid)
                return {"cpu_s": 0 if len(snapshots) == 1 else .001}
            with patch.object(op_profile, "wait_file", side_effect=ready), \
                 patch.object(op_profile.time, "monotonic", side_effect=[10, 12]), \
                 patch.object(driver, "proc_snapshot", side_effect=snapshot):
                control = op_profile.measure_hook_overhead(run, driver, 2)
            run.conn.assert_not_called()
            node.start.assert_called_once()
            self.assertEqual(control["consed_bytes"], 400)
            self.assertEqual(control["duration_s"], 2)
            self.assertEqual(control["cpu_ms"], 1)
            self.assertEqual(snapshots, [123, 123])

    def test_each_window_restarts_with_only_its_hook_and_warmup_is_excluded(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            launches, commands = [], []
            class Target:
                path = "base"
                def launcher(self, work, hooks, env):
                    launches.append((list(hooks), dict(env)))
                    return "launcher", env
            node = SimpleNamespace(work=work, env={"XL_PROF": "1", "XL_PROF_SECONDS": "3"}, launcher="base", target=Target(), pid=123,
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
            def ready(path, seconds=15, **kwargs):
                path.write_text("1")
                if path.name == "done":
                    (path.parent / "consed.txt").write_text("consed_bytes 100 gc_ms 0 gcs 0 window_ms 1\n")
                    (path.parent / "timing.txt").write_text("window_ms 1 gc_ms 0 consed_mb 1\nacl2-entry ONE 2 1\n")
                    sample = Path(__file__).parent / "fixtures" / "load-sprof-flat.txt"
                    (path.parent / "sprof.000.txt").write_text(sample.read_text())
                    (path.parent / "sprof.000.graph.txt").write_text("graph")
                    (path.parent / "sprof.000.threads.jsonl").write_text('{"thread":"fn owner","function":"F","count":1}\n')
            with patch.object(driver, "discover_ids", return_value=(["<fixture>"], "fn.test")), \
                 patch.object(driver, "proc_snapshot", return_value={"cpu_s": 1, "io": {}, "faults": {}}), \
                 patch.object(op_profile, "wait_file", side_effect=ready), \
                 patch.object(op_profile.time, "sleep"), \
                 patch.object(op_profile, "measure_hook_overhead", return_value={"duration_s": .001, "consed_bytes": 0, "not_measured": {}}) as overhead:
                out = op_profile.run(run, {"ops": ["GROUP"], "reps": 3, "warmup": 50}, driver)
            self.assertEqual(len(launches), 4)
            self.assertTrue(all("XL_PROF" not in env and "XL_PROF_SECONDS" not in env for _, env in launches))
            self.assertEqual([h[0][0].name for h in launches],
                             ["op-consed.lisp", "w6-prof.lisp", "w6-prof.lisp", "prof2.lisp"])
            self.assertEqual(len(commands), 4 * (1 + 50 + 3))
            got = out["op_profile"]["GROUP"]
            self.assertEqual(got["clean"]["n"], 3)
            self.assertEqual(got["calls"]["acl2_calls_per_command"], 2 / 3)
            for window in ("cpu", "alloc"):
                self.assertFalse(got["windows"][window]["controller_excluded"])
                self.assertIn("totals differ", got["windows"][window]["controller_exclusion_reason"])
                self.assertIn(window + ".controller_excluded", got["not_measured"])
                self.assertNotIn("top_frames_" + window, got["not_measured"])
                self.assertEqual(len(got["top_frames_" + window]), 3)
            self.assertIn("graph", got["sprof"])
            self.assertIn("syscalls", got["not_measured"])
            self.assertTrue((work / "test/op-profile/GROUP/result.json").exists())
            self.assertEqual(node.env, {})
            self.assertEqual(node.launcher, "base")
            overhead.assert_called_once()
            self.assertEqual(overhead.call_args.args[2], .001)


if __name__ == "__main__":
    unittest.main()
