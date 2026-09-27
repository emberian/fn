#!/usr/bin/env python3
"""The record log's barrier, measured: fsync vs fdatasync vs O_DSYNC, append vs preallocated.

usage: log_barrier_probe.py DIR [DIR ...] [--iters N] [--json OUT]

In a fresh mkdtemp under each DIR (removed at the end) it drives the log's
write pattern: a batch of B entries of ENTRY octets padded to UNIT, written
at the frontier with one write(2) loop, then ONE barrier. Modes:
  append-fsync       file grows (O_APPEND-like offsets), fsync(fd)
  append-fdatasync   file grows, fdatasync(fd) (the size change is metadata it must still flush)
  prealloc-fsync     segment preallocated (posix_fallocate, else zeros written once and fsynced), fsync
  prealloc-fdatasync preallocated, fdatasync: data only, no inode size/mtime
  prealloc-odsync    preallocated, opened O_DSYNC: each write(2) is its own barrier (no separate call)
It reports the median and p90 wall per batch and per entry, and octets per entry.
Python is a measuring client here: it decides nothing the store decides.
"""
import os, sys, time, json, tempfile, statistics, platform, shutil

ENTRY = 3277          # a 2 KiB article's FNST record in an FNLG frame, about 3.2 KiB
UNITS = (4096, 512)
BATCHES = (1, 8, 64)

def padded(n, unit):
    return n if n % unit == 0 else n + unit - n % unit

def prealloc(fd, size):
    try:
        os.posix_fallocate(fd, 0, size)
        how = "posix_fallocate"
    except (AttributeError, OSError):
        z = b"\0" * (1 << 20)
        left = size
        while left > 0:
            left -= os.write(fd, z[:min(left, len(z))])
        how = "zeros"
    os.fsync(fd)
    return how

def run(dirpath, mode, unit, batch, iters):
    d = tempfile.mkdtemp(prefix="logprobe-", dir=dirpath)
    try:
        path = os.path.join(d, "000001.log")
        step = padded(ENTRY, unit)
        buf = (b"\x5a" * ENTRY + b"\0" * (step - ENTRY)) * batch
        flags = os.O_RDWR | os.O_CREAT
        pre = mode.startswith("prealloc")
        how = None
        if pre:
            fd = os.open(path, flags, 0o600)
            how = prealloc(fd, len(buf) * (iters + 2))
            os.close(fd)
        if mode == "prealloc-odsync":
            flags |= os.O_DSYNC
        fd = os.open(path, flags, 0o600)
        off = 0
        walls = []
        for _ in range(iters):
            t0 = time.perf_counter()
            mv = memoryview(buf); o = off
            while len(mv):
                n = os.pwrite(fd, mv, o); mv = mv[n:]; o += n
            if mode.endswith("fdatasync"):
                os.fdatasync(fd)
            elif mode.endswith("fsync"):
                os.fsync(fd)
            walls.append(time.perf_counter() - t0)
            off += len(buf)
        os.close(fd)
        walls.sort()
        med = statistics.median(walls); p90 = walls[int(0.9 * (len(walls) - 1))]
        return {"mode": mode, "unit": unit, "batch": batch, "iters": iters, "prealloc": how,
                "median_ms_per_batch": round(med * 1e3, 3), "p90_ms_per_batch": round(p90 * 1e3, 3),
                "median_ms_per_entry": round(med * 1e3 / batch, 4),
                "barriers_per_entry": (1.0 / batch) if mode != "prealloc-odsync" else "1 per write(2) call",
                "octets_per_entry": step, "padding_fraction": round((step - ENTRY) / ENTRY, 4)}
    finally:
        shutil.rmtree(d, ignore_errors=True)

def main():
    args = sys.argv[1:]
    iters = 60; out = None
    if "--iters" in args:
        i = args.index("--iters"); iters = int(args[i + 1]); del args[i:i + 2]
    if "--json" in args:
        i = args.index("--json"); out = args[i + 1]; del args[i:i + 2]
    res = {"host": platform.node(), "kernel": platform.platform(), "entry_octets": ENTRY, "rows": []}
    for dirpath in args:
        modes = ["append-fsync", "append-fdatasync", "prealloc-fsync", "prealloc-fdatasync", "prealloc-odsync"]
        if not hasattr(os, "fdatasync"):
            modes = [m for m in modes if not m.endswith("fdatasync")]
        if not hasattr(os, "O_DSYNC"):
            modes = [m for m in modes if m != "prealloc-odsync"]
        for mode in modes:
            for unit in UNITS:
                for batch in BATCHES:
                    r = run(dirpath, mode, unit, batch, iters); r["dir"] = dirpath
                    res["rows"].append(r)
                    print(f"{dirpath} {mode:18} unit {unit:4} B {batch:2}: {r['median_ms_per_batch']:9.3f} ms/batch "
                          f"(p90 {r['p90_ms_per_batch']:9.3f}) {r['median_ms_per_entry']:8.4f} ms/entry", flush=True)
    if out:
        with open(out, "w") as f:
            json.dump(res, f, indent=1)

if __name__ == "__main__":
    main()
