#!/usr/bin/env python3
"""Resident memory of a started native owner by mapping (lane runtime-floor).
Runs ON hbox from a tree with tools/runtime_image/node_measure.py.

    mapbreak.py WORK IMAGE [IMAGE...]

For each image in turn: a fresh scale-profile store, the owner started
(node_measure's fresh/start_owner), 2 s idle, /proc/PID/smaps summed by
mapping class (Rss and Anonymous KiB), then stopped.  One JSON line per image.
A measurement only.
"""
import json, os, sys, time
from pathlib import Path
sys.path.insert(0, str(Path.cwd() / "tools"))
sys.path.insert(0, str(Path.cwd() / "tools" / "runtime_image"))
import node_measure as nm  # noqa: E402
import rep_measure as r    # noqa: E402


def classify(name, size_kib):
    if name.endswith(".core"):
        return "core file"
    if "libssl" in name or "libcrypto" in name:
        return "openssl"
    if "libsodium" in name or "mldsa" in name:
        return "sodium+mldsa"
    if name.endswith("/sbcl"):
        return "sbcl runtime"
    if name.startswith("/") and ".so" in name:
        return "other shared libs"
    if name == "[heap]":
        return "malloc heap"
    if name in ("[stack]",):
        return "main stack"
    if name == "":
        return "anon >= 256 MiB (dynamic space)" if size_kib >= 262144 else "anon < 256 MiB (thread stacks, GC tables, alien)"
    return name


def breakdown(pid):
    rows = {}
    cur = None
    for line in Path("/proc/%d/smaps" % pid).read_text().splitlines():
        parts = line.split()
        if "-" in parts[0] and len(parts) >= 5 and not parts[0].endswith(":"):
            lo, hi = (int(x, 16) for x in parts[0].split("-"))
            name = parts[5] if len(parts) > 5 else ""
            cur = classify(name, (hi - lo) // 1024)
            rows.setdefault(cur, {"rss": 0, "anon": 0, "size": 0})
            rows[cur]["size"] += (hi - lo) // 1024
        elif parts[0] == "Rss:":
            rows[cur]["rss"] += int(parts[1])
        elif parts[0] == "Anonymous:":
            rows[cur]["anon"] += int(parts[1])
    return rows


def main():
    work = Path(sys.argv[1])
    for image in sys.argv[2:]:
        env = nm.env_for(1024)
        config, port = nm.fresh(Path(image), work / Path(image).name, env, nm.SCALE)
        proc, start_s, err = r.start_owner(image, config, env, work / (Path(image).name + ".stderr"), timeout=600)
        time.sleep(2)
        rows = breakdown(proc.pid)
        total = {k: sum(v[k] for v in rows.values()) for k in ("rss", "anon", "size")}
        threads = r.status_kib(proc.pid, "Threads")
        r.stop_owner(proc, err)
        print(json.dumps({"image": image, "threads": threads, "total": total, "rows": rows}))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
