"""Isolated per-command measurement windows; no node/image implementation changes."""
from __future__ import annotations

import datetime as dt
import json
import re
import shlex
import subprocess
import tempfile
import time
from pathlib import Path

OPS = ("POST_2k", "ARTICLE_2k", "ARTICLE_128k", "HEAD", "STAT", "GROUP",
       "OVER40", "NEWNEWS", "LIST", "greeting")
IO_KEYS = ("rchar", "wchar", "syscr", "syscw", "read_bytes", "write_bytes")
SYSCALLS = ("fsync", "fdatasync", "write", "pwrite64", "writev", "sendto", "read",
            "recvfrom", "futex", "epoll_wait", "poll", "mmap", "munmap", "madvise",
            "openat", "rename", "renameat")


def parse_sprof(text, limit=25):
    """SBCL flat rows: rank, self count/%, cumulative count/%, calls or total, name.

    Names (including spaces and printed Lisp forms) are retained verbatim.
    """
    rows = []
    pattern = re.compile(r"^\s*\d+\s+(\d+)\s+([\d.]+)%?\s+\d+\s+([\d.]+)%?\s+(.+?)\s*$")
    for line in text.splitlines():
        match = pattern.match(line)
        if match:
            count, percent, cumulative, tail = match.groups()
            # SBCL versions print either Calls (often '-') or Total Count/%.
            name = re.sub(r"^(?:\d+\s+[\d.]+%?\s+|(?:\d+|-)\s+)", "", tail)
            rows.append(dict(count=int(count), percent=float(percent),
                             cumulative_percent=float(cumulative), function=name))
    return rows[:limit]


def parse_strace(text, n):
    """strace -f -c summary; optional errors column does not shift the calls column."""
    calls = {}
    for line in text.splitlines():
        fields = line.split()
        if len(fields) not in (5, 6) or fields[-1] == "total":
            continue
        try:
            float(fields[0]); float(fields[1]); float(fields[2])
            count = int(fields[3])
        except ValueError:
            continue
        if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", fields[-1]):
            calls[fields[-1]] = count
    if not calls:
        raise ValueError("strace produced no syscall summary rows")
    if not n:
        raise ValueError("no completed commands in syscall window")
    per = {name: count / n for name, count in calls.items()}
    # An absent syscall in a valid summary is measured zero.
    per.update({name: per.get(name, 0.0) for name in SYSCALLS})
    return {"n": n, "per_command": per,
            "top20": [{"syscall": name, "calls_per_command": count / n}
                      for name, count in sorted(calls.items(), key=lambda x: -x[1])[:20]]}


def parse_consed(text, n):
    match = re.fullmatch(r"\s*consed_bytes (\d+) gc_ms ([\d.]+) gcs (\d+)\s*", text)
    if not match or not n:
        raise ValueError("invalid consed.txt or no completed commands")
    b, ms, gcs = match.groups()
    return {"consed_bytes": int(b) / n, "gc_ms": float(ms) / n, "gcs": int(gcs) / n}


def parse_calls(text, n):
    if not n or not re.match(r"window_ms [\d.]+ gc_ms [\d.]+ consed_mb [\d.]+", text):
        raise ValueError("invalid prof2 timing.txt or no completed commands")
    entries, barriers, syncs = {}, {}, {}
    for line in text.splitlines()[1:]:
        fields = line.split()
        if len(fields) < 4:
            continue
        kind, name = fields[0], " ".join(fields[1:-2])
        count, ms = int(fields[-2]), float(fields[-1])
        row = {"count_per_command": count / n, "ms_per_command": ms / n}
        if kind == "acl2-entry":
            entries[name] = row
        elif "fdatasync" in name.lower() or "fdatasync" in kind.lower():
            syncs[name] = row
        elif kind == "barrier" or "durable-barrier" in name.lower():
            barriers[name] = row
    if not entries or not sum(r["count_per_command"] for r in entries.values()):
        raise ValueError("prof2 counted no ACL2 entries; encapsulations may not fire for compiled direct calls")
    def totals(rows):
        return {key: sum(row[key] for row in rows.values())
                for key in ("count_per_command", "ms_per_command")}
    return {"n": n, "acl2_calls_per_command": totals(entries)["count_per_command"],
            "entries_per_command": entries,
            "top15": [{"entry": name, **row} for name, row in
                      sorted(entries.items(), key=lambda item: -item[1]["count_per_command"])[:15]],
            "barriers": totals(barriers), "fdatasyncs": totals(syncs)}


def wait_file(path, seconds=15):
    deadline = time.monotonic() + seconds
    while not path.exists():
        if time.monotonic() >= deadline:
            raise RuntimeError("measurement hook did not produce %s" % path.name)
        time.sleep(0.01)


def close_connection(c):
    """No QUIT command in the measured window (including greeting-only windows)."""
    if c is not None:
        if c.reader is not c.stream:
            c.reader.close()
        c.sock.close()


class Trace:
    """Root tracer PID is written by the shell that execs strace, never sudo's wrapper."""
    def __init__(self, owner, directory, budget):
        self.directory = directory
        self.summary = directory / "syscalls.txt"
        self.pidfile = directory / "strace.pid"
        self.errpath = directory / "strace.err"
        self.proc = None
        self.budget = budget
        self.owner = owner

    def start(self):
        check = subprocess.run(["sudo", "-n", "true"], capture_output=True, text=True, timeout=10)
        if check.returncode:
            raise RuntimeError("sudo -n true failed: " + check.stderr.strip())
        script = 'echo $$ > %s; exec strace -f -c -S calls -p %d -o %s' % (
            shlex.quote(str(self.pidfile)), self.owner, shlex.quote(str(self.summary)))
        with open(self.errpath, "wb") as err:
            self.proc = subprocess.Popen(["timeout", "--signal=INT", str(self.budget + 30),
                                          "sudo", "-n", "sh", "-c", script],
                                         stdout=subprocess.DEVNULL, stderr=err)
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            if self.proc.poll() is not None:
                raise RuntimeError("strace attach failed: " + self.errpath.read_text().strip())
            if self.pidfile.exists() and "attached" in self.errpath.read_text():
                return
            time.sleep(0.02)
        raise RuntimeError("strace did not acknowledge attachment: " + self.errpath.read_text().strip())

    def stop(self):
        if self.proc is None:
            return
        if self.proc.poll() is None:
            if not self.pidfile.exists():
                # No PID means no signal: bounded timeout owns cleanup.
                self.proc.wait(timeout=self.budget + 35)
                raise RuntimeError("strace PID file absent; no signal sent; tell the coordinator")
            pid = int(self.pidfile.read_text().strip())
            if pid <= 1:
                raise RuntimeError("invalid strace PID file; no signal sent")
            p = subprocess.run(["sudo", "-n", "kill", "-INT", str(pid)],
                               capture_output=True, text=True, timeout=10)
            if p.returncode:
                raise RuntimeError("cannot stop tracer PID %d: %s" % (pid, p.stderr.strip()))
        self.proc.wait(timeout=15)


def clean_metrics(before, after, ts, stats):
    n = len(ts)
    clean, missing = {"n": n, "wall_ms": {"p50": stats["p50_ms"], "p99": stats["p99_ms"],
                                            "mean": sum(ts) * 1000 / n if n else None}}, {}
    for key, value in clean["wall_ms"].items():
        if value is None:
            missing["clean.wall_ms." + key] = "fewer than 200 samples" if key == "p99" and n else "no completed commands"
    if n and before and after and before.get("cpu_s") is not None and after.get("cpu_s") is not None:
        clean["cpu_ms"] = (after["cpu_s"] - before["cpu_s"]) * 1000 / n
    else:
        missing["clean.cpu_ms"] = "owner /proc CPU unavailable or no completed commands"
    for field, keys in (("io", IO_KEYS), ("faults", ("minor", "major"))):
        clean[field] = {}
        for key in keys:
            a, b = (before or {}).get(field, {}), (after or {}).get(field, {})
            if n and key in a and key in b:
                clean[field][key] = (b[key] - a[key]) / n
            else:
                missing["clean.%s.%s" % (field, key)] = "owner /proc counter unavailable or no completed commands"
    return clean, missing


def run(run, ph, driver):
    node = run.node
    ops = ph.get("ops", OPS)
    if set(ops) - set(OPS):
        raise driver.CellError("unknown profile operations")
    # Unique POST IDs even if the fixture was made by this harness's article generator.
    run.ctr._ids = __import__("itertools").count(int(time.time_ns()))
    ids = {}
    c = run.conn()
    try:
        if c is None:
            raise driver.CellError("setup connection refused")
        for kib in (2, 128):
            if "ARTICLE_%dk" % kib in ops:
                if driver.post_one(c, run.ctr, kib * 1024, retries=1) is None:
                    raise driver.CellError("setup ARTICLE_%dk POST refused" % kib)
                ids[kib] = driver.mid(run.ctr.known[-1])
    finally:
        close_connection(c)
    # Discover fixture IDs and its group through the existing wire path.
    known, group = driver.discover_ids(node.port, want=40)
    if not known:
        raise driver.CellError("profile needs discoverable fixture articles")
    base_env, base_launcher = dict(node.env), node.launcher
    result = {}
    for op in ops:
        record = {"not_measured": {}, "windows": {}, "sprof": {},
                  "counter_scope": "process-wide; clean uses only a trigger/counter observer, no encapsulation"}
        result[op] = record
        since = None
        if op == "NEWNEWS":
            node.stop()
            node.env, node.launcher = dict(base_env), base_launcher
            node.start()
            c = run.conn()
            try:
                date = c.line("DATE").split()
                if len(date) != 2 or date[0] != b"111":
                    raise driver.CellError("NEWNEWS setup DATE unavailable")
                # Cross a server second so none of the earlier setup/POST window
                # articles are included; acceptance uses the server's clock.
                deadline = time.monotonic() + 10
                while True:
                    newer = c.line("DATE").split()
                    if len(newer) == 2 and newer[0] == b"111" and newer[1] > date[1]:
                        stamp = dt.datetime.strptime(newer[1].decode(), "%Y%m%d%H%M%S")
                        since = stamp.strftime("%Y%m%d %H%M%S GMT")
                        break
                    if time.monotonic() >= deadline:
                        raise driver.CellError("server DATE did not advance for NEWNEWS setup")
                    time.sleep(0.05)
                for _ in range(40):
                    if driver.post_one(c, run.ctr, 2048, retries=1) is None:
                        raise driver.CellError("NEWNEWS setup POST refused")
            finally:
                close_connection(c)
            record["since"] = since
        reps = ph.get("reps", 100 if op in ("POST_2k", "ARTICLE_128k") else 300)
        budget = ph.get("budget_s", 60)
        for window in ("clean", "cpu", "alloc", "calls", "syscalls"):
            if window == "syscalls" and not run.spec.get("strace", run.args.box == "persvati"):
                record["not_measured"]["syscalls"] = "strace disabled (default enabled only on persvati)"
                continue
            op_dir = Path(run.args.out) / run.label / "op-profile" / op
            op_dir.mkdir(parents=True, exist_ok=True)
            directory = Path(tempfile.mkdtemp(prefix=window + "-", dir=op_dir))
            # No profile hook from any earlier window survives this owner restart.
            node.stop()
            node.env = dict(base_env)
            for key in list(node.env):
                if key.startswith("FN_LOAD_PROF") or key in ("FN_LOAD_CONSED_DIR", "XL_PROF_DIR", "XL_HOOK", "FN_LOAD_GC_LOG", "FN_LOAD_IDLE_GC"):
                    node.env.pop(key)
            hooks = []
            if window == "clean":
                hooks = [driver.HOOKS / "op-consed.lisp"]
                node.env["FN_LOAD_CONSED_DIR"] = str(directory)
            elif window in ("cpu", "alloc"):
                hooks = [driver.SPROF_HOOK]
                node.env.update(FN_LOAD_PROF=str(directory / "sprof"), FN_LOAD_PROF_START=str(directory / "start"),
                                FN_LOAD_PROF_WINDOW=str(budget + 5), FN_LOAD_PROF_INTERVAL="0.001",
                                FN_LOAD_PROF_MODE=window, FN_LOAD_PROF_GRAPH="1" if window == "cpu" else "0")
            elif window == "calls":
                hooks = [driver.PROF_HOOK]
                node.env["XL_PROF_DIR"] = str(directory)
            trace, c, measurement_incomplete = None, None, False
            wr = {"n": 0, "requested_reps": reps, "budget_s": budget, "warmup": ph.get("warmup", 50),
                  "artifacts": str(directory.relative_to(run.args.out))}
            record["windows"][window] = wr
            try:
                node.launcher, node.env = node.target.launcher(node.work, hooks, node.env)
                node.start()
                c = run.conn() if op != "greeting" else None
                if op != "greeting" and c is None:
                    raise driver.CellError("window connection refused")
                if c:
                    g = c.line("GROUP %s" % group).split()
                    if not g or g[0] != b"211":
                        raise driver.CellError("profile GROUP setup failed")
                    hi = int(g[3]); lo = max(int(g[2]), hi - 39)
                    c.sock.settimeout(min(10, budget))
                def command(k, timeout=None):
                    start = time.perf_counter()
                    deadline = start + timeout if timeout is not None else None
                    def line(text=None):
                        if deadline is not None:
                            left = deadline - time.perf_counter()
                            if left <= 0:
                                raise TimeoutError("command exceeded window wall budget")
                            c.sock.settimeout(left)
                        return c.line(text) if text is not None else c.readline()
                    if op == "greeting":
                        cc = driver._clients()[0].Conn(node.port, buffered=True,
                                                       timeout=timeout or min(10, budget))
                        close_connection(cc)
                    elif op == "POST_2k":
                        if driver.post_one(c, run.ctr, 2048, retries=1,
                                           deadline=time.monotonic() + timeout if timeout is not None else None) is None:
                            raise driver.CellError("profile POST refused")
                    else:
                        cmd, code, multi = {
                            "GROUP": ("GROUP " + group, b"211", False),
                            "OVER40": ("OVER %d-%d" % (lo, hi), b"224", True),
                            "STAT": ("STAT " + driver.mid(known[k % len(known)]), b"223", False),
                            "HEAD": ("HEAD " + driver.mid(known[k % len(known)]), b"221", True),
                            "LIST": ("LIST", b"215", True),
                            "NEWNEWS": ("NEWNEWS %s %s" % (group, since), b"230", True),
                            "ARTICLE_2k": ("ARTICLE " + ids.get(2, ""), b"220", True),
                            "ARTICLE_128k": ("ARTICLE " + ids.get(128, ""), b"220", True)}[op]
                        reply = line(cmd)
                        if not reply.startswith(code):
                            raise driver.CellError("%s unexpected reply %r" % (op, reply))
                        if op == "NEWNEWS":
                            returned = []
                            while True:
                                reply_line = line()
                                if reply_line == b".\r\n":
                                    break
                                if not reply_line:
                                    raise driver.CellError("EOF in NEWNEWS block")
                                returned.append(reply_line.decode("ascii").strip())
                            return time.perf_counter() - start, returned
                        if multi:
                            while True:
                                reply_line = line()
                                if reply_line == b".\r\n":
                                    break
                                if not reply_line:
                                    raise driver.CellError("EOF in multiline profile reply")
                    return time.perf_counter() - start, None
                for k in range(wr["warmup"]):
                    command(k)
                if window == "syscalls":
                    trace = Trace(node.pid, directory, budget)
                    trace.start()
                else:
                    (directory / "start").touch()
                    if window == "calls":
                        # prof2's existing protocol has no ready file; phase_prof
                        # uses the same settling interval before issuing commands.
                        time.sleep(0.5)
                    else:
                        wait_file(directory / "ready")
                before = driver.proc_snapshot(node.pid)
                ts, returned_ids = [], []
                start = time.monotonic()
                try:
                    for k in range(reps):
                        remaining = budget - (time.monotonic() - start)
                        if remaining <= 0:
                            break
                        if c:
                            c.sock.settimeout(remaining)
                        elapsed, returned = command(k, remaining)
                        ts.append(elapsed)
                        if returned is not None:
                            returned_ids.append(returned)
                except Exception:
                    measurement_incomplete = True
                    raise
                finally:
                    wr["n"] = len(ts)
                    wr["wall_s"] = time.monotonic() - start
                    wr["budget_exhausted"] = wr["wall_s"] >= budget
                    after = driver.proc_snapshot(node.pid)
                    if window != "syscalls":
                        (directory / "stop").touch()
                    if op == "NEWNEWS":
                        wr["ids_returned"] = returned_ids
                        wr["ids_per_command"] = [len(row) for row in returned_ids]
                    if window == "clean":
                        record["clean"], missing = clean_metrics(before, after, ts, driver.res_mod.lat_stats(ts))
                        record["not_measured"].update(missing)
                if trace:
                    trace.stop()
                    record["syscalls"] = parse_strace(trace.summary.read_text(), len(ts))
                else:
                    wait_file(directory / "done", 120)
                    if window == "clean":
                        record["clean"].update(parse_consed((directory / "consed.txt").read_text(), len(ts)))
                    elif window == "calls":
                        record["calls"] = parse_calls((directory / "timing.txt").read_text(), len(ts))
                        if op == "POST_2k" and not (record["calls"]["barriers"]["count_per_command"] or
                                                   record["calls"]["fdatasyncs"]["count_per_command"]):
                            for key in ("barriers", "fdatasyncs"):
                                record["calls"].pop(key)
                                record["not_measured"]["calls." + key] = "prof2 counted no POST syncs; encapsulations may not fire for compiled direct calls"
                    else:
                        flat = directory / "sprof.000.txt"
                        record["sprof"][window] = str(flat.relative_to(run.args.out))
                        frames = parse_sprof(flat.read_text())
                        record["top_frames_" + window] = frames
                        if not frames:
                            record["not_measured"]["top_frames_" + window] = "flat report has no sample rows"
                        if window == "cpu":
                            graph = directory / "sprof.000.graph.txt"
                            record["sprof"]["graph"] = str(graph.relative_to(run.args.out))
            except Exception as exc:
                wr["error"] = "%s: %s" % (type(exc).__name__, exc)
                record["not_measured"][window] = wr["error"]
                if window == "clean":
                    # A failed/incomplete command contributes to process counters
                    # but not n. Never normalize its CPU/I/O/faults by completed n.
                    if "clean" in record and measurement_incomplete:
                        for field, keys in (("io", IO_KEYS), ("faults", ("minor", "major"))):
                            record["clean"].pop(field, None)
                            for key in keys:
                                record["not_measured"]["clean.%s.%s" % (field, key)] = wr["error"]
                        record["clean"].pop("cpu_ms", None)
                        record["not_measured"]["clean.cpu_ms"] = wr["error"]
                    for key in ("consed_bytes", "gc_ms", "gcs"):
                        if key not in record.get("clean", {}):
                            record["not_measured"]["clean." + key] = wr["error"]
                elif window in ("cpu", "alloc"):
                    record["not_measured"]["top_frames_" + window] = wr["error"]
            finally:
                if trace and trace.proc and trace.proc.poll() is None:
                    try:
                        trace.stop()
                    except Exception as exc:
                        record["not_measured"]["syscalls.stop"] = str(exc)
                        raise
                close_connection(c)
                node.stop()
            # Keep a recoverable per-operation result even if a later setup fails.
            (directory.parent / "result.json").write_text(json.dumps(record, indent=1))
        node.env, node.launcher = dict(base_env), base_launcher
    return {"op_profile": result, "not_measured": {
        "%s.%s" % (op, key): reason for op, record in result.items()
        for key, reason in record["not_measured"].items()}}
