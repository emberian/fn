#!/usr/bin/env python3
"""Concurrent POST rate, latency and fsyncs per POST of one native image
(lane group-commit, 2026-09-26).  Runs ON hbox inside a systemd-run unit.

    gc_measure.py --image IMG --dir DIR --json OUT [--seconds S]
                  [--connections 1,8,32] [--fsync-posts K]

DIR (fresh) holds the store; its filesystem is the row's (tmpfs or the
pool).  For each C in --connections, on a FRESH store (`operator init`
with the scale-1m profile of tools/service_envelope.py) and a fresh owner:
100 warm-up POSTs on one connection, then a closed-loop window of S seconds
or --cap POSTs on C connections (every connection opened before the window,
no readers):
POSTs a second and the latency distribution (command to the durable 240)
with p50/p95/p99.  Then the fsync count: the owner restarted under
`strace -f -c -e trace=fsync,fdatasync` twice (yama ptrace_scope 1: the
tracer must be the parent), once with no POST (open and stop) and once
with K POSTs on 8 connections; fsyncs per POST is the difference over K.
The fsync step runs on the last row's store.  The box's load and the ZFS ARC size are recorded beside every row.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time

TREE = Path(os.environ.get("FN_TREE", Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(TREE / "tools"))
sys.path.insert(0, str(TREE))
import msgid_measure as m  # noqa: E402
import rep_measure as r  # noqa: E402
import service_envelope as se  # noqa: E402
from tests.native_process import wait_for_announcement  # noqa: E402


def box():
    arc = None
    try:
        for row in Path("/proc/spl/kstat/zfs/arcstats").read_text().splitlines():
            if row.startswith("size "):
                arc = int(row.split()[2])
    except OSError:
        pass
    return {"utc": se.now(), "loadavg": os.getloadavg(), "arc_octets": arc}


def pct(ms, q):
    return ms[min(len(ms) - 1, max(0, int(round(q * len(ms))) - 1))]


def dist(seconds):
    ms = sorted(s * 1000.0 for s in seconds)
    if not ms:
        return None
    return {"n": len(ms), "p50_ms": round(pct(ms, 0.50), 3), "p95_ms": round(pct(ms, 0.95), 3),
            "p99_ms": round(pct(ms, 0.99), 3), "max_ms": round(ms[-1], 3)}


class Counter:
    def __init__(self, start):
        self.lock, self.i = threading.Lock(), start

    def next(self):
        with self.lock:
            self.i += 1
            return self.i - 1


def window(port, connections, seconds, counter, octets, max_posts=None):
    """Closed loop on CONNECTIONS for SECONDS (or until MAX_POSTS)."""
    done, lat, errors = [], [], []
    lock = threading.Lock()
    opened, go = threading.Barrier(connections + 1), threading.Event()
    deadline = [None]

    def poster():
        try:
            c = m.Conn(port)
            opened.wait()
            go.wait()
            while time.perf_counter() < deadline[0]:
                i = counter.next()
                if max_posts is not None and i >= max_posts[0]:
                    break
                dt = r.post(c, i, octets)
                with lock:
                    done.append(time.perf_counter())
                    lat.append(dt)
            c.close()
        except BaseException as e:  # noqa: BLE001 - reported
            errors.append(repr(e))

    ts = [threading.Thread(target=poster, daemon=True) for _ in range(connections)]
    for t in ts:
        t.start()
    opened.wait(timeout=600)
    t0 = time.perf_counter()
    deadline[0] = t0 + seconds
    go.set()
    for t in ts:
        t.join(timeout=seconds + 600)
    wall = time.perf_counter() - t0
    return {"connections": connections, "seconds": round(wall, 3), "posts": len(done),
            "post_per_s": round(len(done) / wall, 3), "latency": dist(lat), "errors": errors[:5]}


def start_traced(image, config, env, stderr_path, trace_path):
    stderr = open(stderr_path, "ab")
    proc = subprocess.Popen(["strace", "-f", "-c", "-e", "trace=fsync,fdatasync", "-o", str(trace_path),
                             str(image), "--fn", "operator", str(config), "run"],
                            env=env, stdout=subprocess.PIPE, stderr=stderr)
    wait_for_announcement(proc, b"LISTENING ", timeout=1200)
    return proc, stderr


def stop_traced(proc, stderr):
    # SIGTERM to strace would detach it; stop the traced owner (its child) instead.
    kids = Path("/proc/%d/task/%d/children" % (proc.pid, proc.pid)).read_text().split()
    for k in kids:
        os.kill(int(k), signal.SIGTERM)
    proc.wait(timeout=600)
    stderr.close()


def fsyncs(trace_path):
    total = 0
    for row in Path(trace_path).read_text().splitlines():
        f = row.split()
        if f and f[-1] in ("fsync", "fdatasync"):
            total += int(f[3] if len(f) >= 6 else f[3])
    return total


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--image", required=True)
    p.add_argument("--dir", required=True)
    p.add_argument("--json", required=True)
    p.add_argument("--label", required=True)
    p.add_argument("--seconds", type=int, default=30)
    p.add_argument("--connections", default="1,8,32")
    p.add_argument("--fsync-posts", type=int, default=64)
    p.add_argument("--octets", type=int, default=2048)
    p.add_argument("--cap", type=int, default=2000, help="at most this many POSTs a row")
    a = p.parse_args()
    image, d = Path(a.image), Path(a.dir)
    env = se.image_env()
    d.mkdir(parents=True, exist_ok=False)
    out = {"label": a.label, "image": str(image), "core_sha256": m.digest(str(image) + ".core"),
           "filesystem": se.filesystem(d), "profile": se.PROFILE_NAME, "octets": a.octets,
           "seconds": a.seconds, "rows": [], "fsync": {}}

    def write():
        Path(a.json).write_text(json.dumps(out, indent=2) + "\n")

    counter = Counter(0)
    # One fresh store per row: the served path has a per-POST term linear in
    # the store's size (publish-program 1.4), so rows that share a store
    # would compare different N.  Each row: init, 100 warm-up POSTs on one
    # connection, then the window (at most --cap POSTs or --seconds).
    for c in [int(x) for x in a.connections.split(",")]:
        rd = d / ("c%d" % c)
        rd.mkdir()
        rc = se.write_config(rd, 1)
        ri = subprocess.run([str(image), "--fn", "operator", str(rc), "init"] + se.PROFILE + [se.GROUP],
                            env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if ri.returncode:
            raise SystemExit("init rc=%d: %r" % (ri.returncode, ri.stdout[-600:]))
        owner = se.Owner(image, rd, env, "rate", 1200)
        try:
            warm = window(owner.port, 1, 3600, counter, a.octets, max_posts=[counter.i + 100])
            b0, c0 = box(), owner.cpu()
            row = window(owner.port, c, a.seconds, counter, a.octets, max_posts=[counter.i + a.cap])
            row["warmup_posts"] = warm["posts"]
            row["owner_cpu_ms_per_post"] = round(1000.0 * (owner.cpu() - c0) / max(1, row["posts"]), 3)
            row["box_before"], row["box_after"] = b0, box()
            out["rows"].append(row)
            write()
        finally:
            owner.stop()
    for label, k in (("open-only", 0), ("posts", a.fsync_posts)):
        config = se.write_config(rd, m.free_port())
        port = int(config.read_text().split("port = ")[1].split()[0])
        trace = rd / ("strace-%s.txt" % label)
        proc, err = start_traced(image, config, env, rd / ("owner-trace-%s.stderr" % label), trace)
        try:
            if k:
                start = counter.i
                w = window(port, 8, 3600, counter, a.octets, max_posts=[start + k])
                out["fsync"]["window"] = w
        finally:
            stop_traced(proc, err)
        out["fsync"][label] = fsyncs(trace)
        out["fsync"][label + "_trace"] = trace.read_text()
    k = out["fsync"]["window"]["posts"]
    out["fsync"]["per_post"] = round((out["fsync"]["posts"] - out["fsync"]["open-only"]) / max(1, k), 3)
    write()
    print(json.dumps({"rows": [(x["connections"], x["post_per_s"], x["latency"]) for x in out["rows"]],
                      "fsync_per_post": out["fsync"]["per_post"]}, indent=1))


if __name__ == "__main__":
    main()
