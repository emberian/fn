"""PUBPROF: replay, offline checkpoint publication, checkpoint reopen.

Each CPU/alloc/strace sequence has a fresh curve fixture copy. Heap decisions
and filesystem rebinding run before hook installation; only the actual owner
or store verb is profiled. Native hooks enter through Target.launcher; fn-core
hooks enter through XL_HOOK, which Node.verb already inherits unchanged.
"""
from __future__ import annotations

import json
import re
import resource
import shlex
import shutil
import tempfile
import time
from pathlib import Path

from tools.load.op_profile import parse_sprof, parse_strace, wait_file

OPERATIONS = ("open_replay", "publish", "reopen_checkpoint")
SYSCALLS = ("fsync", "fdatasync", "write", "pwrite64", "read", "pread64", "openat",
            "rename", "mmap", "munmap", "madvise", "futex")


def parse_exit_consed(text):
    """exit-prof counters are totals for one operation, before report generation."""
    number = r"\d+(?:\.\d*)?(?:[eEdD][+-]?\d+)?"
    match = re.fullmatch(r"\s*consed_bytes (\d+) gc_ms (" + number + r") cpu_ms (" + number +
                         r") write_bytes (\d+|unavailable)\s*", text)
    if not match:
        raise ValueError("invalid exit-prof consed counters")
    bytes_, gc, cpu, written = match.groups()
    return {"consed_bytes": int(bytes_), "gc_ms": float(gc.lower().replace("d", "e")),
            "profile_cpu_ms": float(cpu.lower().replace("d", "e")),
            "profile_write_bytes": None if written == "unavailable" else int(written)}


def parse_exit_report(text):
    """Only the flat section is passed to parse_sprof; graph rows are excluded."""
    flat, separator, _ = text.partition("=== graph ===")
    if not separator or not flat.startswith("=== flat ==="):
        raise ValueError("exit-prof report lacks its flat/graph sections")
    return parse_sprof(flat)


def parse_syscalls(text):
    # One process operation, hence n=1: retain integer totals, no command average.
    parsed = parse_strace(text, 1)
    counts = {name: int(value) for name, value in parsed["per_command"].items()}
    counts.update({name: counts.get(name, 0) for name in SYSCALLS})
    return {"counts": counts,
            "top20": [{"syscall": row["syscall"], "count": int(row["calls_per_command"])}
                      for row in parsed["top20"]]}


def parse_owner_open(text):
    match = re.search(r"OWNER-OPEN (open=(full-replay|checkpoint:(\d+))[^\r\n]*)", text)
    if not match:
        raise ValueError("OWNER-OPEN report absent; open path unconfirmed")
    return {"report": match.group(1), "kind": "checkpoint" if match.group(3) else "replay",
            "checkpoint_records": int(match.group(3)) if match.group(3) else None}


def store_delta(before, after):
    return {"octets_written": sum(size for name, (size, stamp) in after.items()
                                  if before.get(name) != (size, stamp)),
            "octets_written_scope": "sum of final sizes of newly created or changed store files",
            "store_octets_before": sum(size for size, _ in before.values()),
            "store_octets_after": sum(size for size, _ in after.values())}


class ChildCommand:
    """Bounded child launch; PID written by the shell that execs the actual node.

    The timeout/strace wrapper PID is never used to signal the owner. strace
    launches and follows the child, so this path needs no sudo/attach privilege.
    """
    def __init__(self, directory, trace=False):
        self.pidfile = directory / "child.pid"
        self.summary = directory / "syscalls.txt"
        self.trace = trace

    def wrap(self, command, seconds):
        script = 'echo $$ > %s; exec "$@"' % shlex.quote(str(self.pidfile))
        child = ["sh", "-c", script, "fn-load-child", *command]
        if self.trace:
            child = ["strace", "-f", "-c", "-S", "calls", "-o", str(self.summary), *child]
        return ["timeout", "--signal=TERM", "--kill-after=30", str(seconds), *child]


def base_environment(env):
    return {key: value for key, value in env.items()
            if not key.startswith("FN_LOAD_") and key not in ("XL_HOOK", "XL_PROF", "XL_PROF_SECONDS")}


def collect_profile(prefix, record, report_timeout):
    wait_file(Path(str(prefix) + ".done"), report_timeout)
    error = Path(str(prefix) + ".error.txt")
    if error.exists():
        raise RuntimeError("exit-prof report failed: " + error.read_text().strip())
    counters = parse_exit_consed(Path(str(prefix) + ".consed.txt").read_text())
    record.update(counters)
    if counters["profile_write_bytes"] is None:
        record["not_measured"]["profile_write_bytes"] = "hook could not read /proc/self/io"
    report = Path(str(prefix) + ".txt")
    record["top_frames"] = parse_exit_report(report.read_text())
    if not record["top_frames"]:
        record["not_measured"]["top_frames"] = "flat report contains no sample rows"


def run(run, ph, driver):
    node = run.node
    original = (node.store, node.launcher, dict(node.env), node.launcher_decides)
    env = base_environment(node.env)
    out = Path(run.args.out).resolve() / run.label / "pub-profile"
    out.mkdir(parents=True, exist_ok=True)
    operations = {op: {"windows": {}, "not_measured": {}} for op in OPERATIONS}
    fixture_info = {}
    intervals = str(ph.get("sample_interval", "0.005"))
    report_timeout = ph.get("report_timeout_s", 120)
    # Copies, PID files and triggers belong to this invocation, including reruns
    # with the same label. Reports stay in the fetchable output directory.
    scratch = Path(tempfile.mkdtemp(prefix="pub-prof-", dir=node.work))
    fatal = False

    def save():
        (out / "result.json").write_text(json.dumps(operations, indent=1))

    def missing(record, why):
        for key in ("wall_s", "cpu_s", "octets_written", "write_bytes", "consed_bytes", "gc_ms",
                    "top_frames", "syscalls"):
            if key not in record:
                record["not_measured"][key] = why

    try:
        for mode in ("cpu", "alloc", "strace"):
            if mode == "strace" and not shutil.which("strace"):
                for op in OPERATIONS:
                    record = {"status": "not_measured", "not_measured": {}}
                    operations[op]["windows"][mode] = record
                    missing(record, "strace executable unavailable")
                save()
                continue
            node.stop()
            node.store = scratch / mode / "store"
            node.store.parent.mkdir(parents=True)
            node.launcher, node.env = node.target.path, dict(env)
            # start_owner=False leaves the first owner replay to this phase.
            try:
                fixture_info[mode] = driver.prepare_store(node, run, run.spec, run.args.cache, "pub-prof",
                                                         start_owner=False)
            except Exception as exc:
                for op in OPERATIONS:
                    record = {"status": "not_measured", "not_measured": {}}
                    operations[op]["windows"][mode] = record
                    missing(record, "fixture preparation failed: %s" % exc)
                save()
                continue
            prerequisite = None
            for op in OPERATIONS:
                record = {"status": "running", "not_measured": {}}
                operations[op]["windows"][mode] = record
                if prerequisite:
                    record["status"] = "not_measured"
                    missing(record, prerequisite)
                    continue
                directory = Path(tempfile.mkdtemp(prefix=op + "-" + mode + "-", dir=out))
                prefix = directory / "sprof"
                stop = directory / "stop"
                wrapper = ChildCommand(directory, trace=mode == "strace")
                record["artifacts"] = str(directory.relative_to(Path(run.args.out).resolve()))
                record["mode"] = mode
                try:
                    node.stop()
                    node.env, node.launcher = dict(env), node.target.path
                    # Probe the exact command, unhooked. A hooked probe would
                    # exit first and steal/overwrite the operation's report.
                    command = ["store", str(node.store), "checkpoint"] if op == "publish" else None
                    node.decide_heap(command=command)
                    node.launcher_decides = False
                    if mode != "strace":
                        node.env.update(FN_LOAD_EXITPROF=str(prefix), FN_LOAD_EXITPROF_STOP=str(stop),
                                        FN_LOAD_EXITPROF_MODE=mode, FN_LOAD_EXITPROF_INTERVAL=intervals)
                        node.launcher, node.env = node.target.launcher(node.work,
                                                                    [driver.HOOKS / "exit-prof.lisp"], node.env)
                        record["sprof_file"] = str(Path(str(prefix) + ".txt").relative_to(Path(run.args.out).resolve()))
                        record["counter_scope"] = "hook load through profile stop, before report generation"
                        record["trigger_poll_s"] = 0.05
                        record["sample_interval_s"] = float(intervals)
                        record["max_samples"] = 1000000
                    before = driver.store_files(node.store)
                    if op == "publish":
                        r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
                        rc, secs, tail = node.verb("checkpoint", command_wrapper=wrapper,
                                                   timeout=ph.get("publish_timeout_s", 3600))
                        r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
                        record.update(wall_s=secs, cpu_s=(r1.ru_utime + r1.ru_stime) -
                                      (r0.ru_utime + r0.ru_stime), exit_code=rc, checkpoint_report=tail.strip())
                        record["cpu_scope"] = "RUSAGE_CHILDREN delta, including wrapper and exit-report work"
                        record["wall_scope"] = "verb process through exit, including exit-report work"
                        if rc:
                            raise driver.CellError("checkpoint exit %d: %s" % (rc, tail))
                        record["not_measured"]["write_bytes"] = "verb exited before final driver /proc snapshot"
                    else:
                        secs = node.start(timeout=ph.get("open_timeout_s", 1800), probe_heap=False,
                                          command_wrapper=wrapper)
                        # The owner CPU/I/O snapshot is captured by Node.start at
                        # LISTENING. strace has no hook and is stopped right here.
                        if mode == "strace":
                            record["exit_code"] = node.stop()
                            record["syscall_scope"] = "startup through LISTENING plus immediate owner shutdown"
                        else:
                            stop.touch()
                        snapshot = node.open_snapshot or {}
                        record.update(wall_s=secs, cpu_s=snapshot.get("cpu_s"),
                                      write_bytes=snapshot.get("io", {}).get("write_bytes"))
                        record["wall_scope"] = "owner launch through LISTENING"
                        record["cpu_scope"] = "owner /proc CPU at LISTENING"
                        if record["cpu_s"] is None:
                            record["not_measured"]["cpu_s"] = "owner /proc CPU unavailable at LISTENING"
                        if record["write_bytes"] is None:
                            record["not_measured"]["write_bytes"] = "owner /proc/io unavailable at LISTENING"
                        err = node.work / ("owner.%d.err" % node.err_n)
                        try:
                            observed = parse_owner_open(err.read_text())
                            record["observed_open"] = observed
                            expected = "replay" if op == "open_replay" else "checkpoint"
                            if observed["kind"] != expected:
                                raise ValueError("expected %s, observed %s" % (expected, observed["kind"]))
                        except (ValueError, OSError) as exc:
                            record["not_measured"]["open_path"] = str(exc)
                    if mode != "strace":
                        collect_profile(prefix, record, report_timeout)
                        if op == "publish" and record["profile_write_bytes"] is not None:
                            record["write_bytes"] = record["profile_write_bytes"]
                            record["write_bytes_scope"] = "hook /proc/self/io at verb exit, before reports"
                            record["not_measured"].pop("write_bytes", None)
                        operations[op]["top_frames_" + mode] = record["top_frames"]
                    else:
                        record["syscalls"] = parse_syscalls(wrapper.summary.read_text())
                        record["strace_file"] = str(wrapper.summary.relative_to(Path(run.args.out).resolve()))
                        for key in ("consed_bytes", "gc_ms", "top_frames"):
                            record["not_measured"][key] = "strace window runs without an allocation/profile hook"
                    record["status"] = "complete" if not record["not_measured"].get("open_path") else "path_unconfirmed"
                except Exception as exc:
                    record["status"] = "not_measured"
                    reason = "%s: %s" % (type(exc).__name__, exc)
                    missing(record, reason)
                    record["error"] = reason
                    # A profiler report failure still leaves a successful store
                    # operation; only an operation/start failure blocks its sequel.
                    if "wall_s" not in record or (op == "publish" and record.get("exit_code")):
                        prerequisite = "%s failed in %s window: %s" % (op, mode, reason)
                finally:
                    try:
                        node.stop()
                    except Exception:
                        fatal = True  # retain files/PID for coordinator; no alternate signal
                        save()
                        raise
                    after = driver.store_files(node.store)
                    if "wall_s" in record:
                        record.update(store_delta(before, after))
                        record["sizes_before"], record["sizes_after"] = driver.components(before), driver.components(after)
                        record["store_files_end"] = "after process exit/owner shutdown"
                    if mode != "strace":
                        record["not_measured"]["syscalls"] = "separate strace window owns syscall counts"
                    save()
            if not run.args.keep:
                shutil.rmtree(node.store)  # this invocation's fixture copy only
    finally:
        node.store, node.launcher, node.env, node.launcher_decides = original
        if not fatal and not node.proc:
            node.write_config()
    return {"pub_profile": operations, "fixture_copies": fixture_info,
            "not_measured": {"pub_profile.%s.%s.%s" % (op, mode, key): reason
                             for op, operation in operations.items()
                             for mode, record in operation["windows"].items()
                             for key, reason in record["not_measured"].items()}}
