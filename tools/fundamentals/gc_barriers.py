#!/usr/bin/env python3
"""Durability barriers per POST: owner under strace -f -c, 1 arm per connection count. Run from a tree copy."""
import json, os, re, subprocess, sys
from pathlib import Path
TREE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(TREE / "tools" / "fundamentals")); sys.path.insert(0, str(TREE / "tools")); sys.path.insert(0, str(TREE))
import gc_measure as g
import msgid_measure as m, rep_measure as r, service_envelope as se
from tests.native_harness import wait_for_announcement
if os.environ.get("GC_HISTORY"):
    se.PROFILE[se.PROFILE.index("--max-history-octets") + 1] = os.environ["GC_HISTORY"]
CALLS = "fdatasync,fsync,sync_file_range"

def traced(image, config, env, out, extra):
    env = r.decided_heap_env(image, config, env)
    proc = subprocess.Popen(["strace", "-f", *extra, "-e", "trace=" + CALLS, "-o", str(out),
                             str(image), "--fn", "operator", str(config), "run"],
                            env=env, stdout=subprocess.PIPE, stderr=open(str(out) + ".err", "ab"))
    wait_for_announcement(proc, b"LISTENING ", timeout=1200)
    return proc

def stop(proc):
    for k in Path("/proc/%d/task/%d/children" % (proc.pid, proc.pid)).read_text().split():
        os.kill(int(k), 15)
    proc.wait(timeout=600)

def fresh(image, d, env):
    d.mkdir(parents=True)
    rc = se.write_config(d, 1)
    ri = subprocess.run([str(image), "--fn", "operator", str(rc), "init"] + se.PROFILE + [se.GROUP],
                        env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if ri.returncode: raise SystemExit("init rc=%d" % ri.returncode)
    config = se.write_config(d, m.free_port())
    return config, int(config.read_text().split("port = ")[1].split()[0])

def parse_c(path):
    rows = {}
    for line in Path(path).read_text().splitlines():
        f = line.split()
        if len(f) >= 5 and f[-1] in CALLS.split(","):
            rows[f[-1]] = {"calls": int(f[3] if len(f) == 6 else f[3]), "usecs_per_call": int(f[2]), "seconds": float(f[1])}
    return rows

def arm(image, base, env, conns, posts):
    config, port = fresh(image, base / ("open%d" % conns), env)
    t = base / ("open%d.txt" % conns)
    p = traced(image, config, env, t, ["-c"]); stop(p)
    open_only = parse_c(t)
    config, port = fresh(image, base / ("c%d" % conns), env)
    t = base / ("c%d.txt" % conns)
    p = traced(image, config, env, t, ["-c"])
    counter = g.Counter(0)
    try:
        w = g.window(port, conns, 3600, counter, 2048, max_posts=[posts])
    finally:
        stop(p)
    run = parse_c(t)
    res = {"connections": conns, "posts": w["posts"], "post_per_s_strace": w["post_per_s"], "latency": w["latency"], "errors": w["errors"], "calls": {}}
    for k in CALLS.split(","):
        n = run.get(k, {}).get("calls", 0) - open_only.get(k, {}).get("calls", 0)
        res["calls"][k] = {"calls": n, "per_post": round(n / max(1, w["posts"]), 3),
                           "usecs_per_call": run.get(k, {}).get("usecs_per_call"), "open_only_calls": open_only.get(k, {}).get("calls", 0)}
    return res

def sample(image, base, env):
    config, port = fresh(image, base / "ysample", env)
    t = base / "ysample.txt"
    p = traced(image, config, env, t, ["-y"])
    try: g.window(port, 8, 3600, g.Counter(0), 2048, max_posts=[40])
    finally: stop(p)
    cnt = {}
    for line in t.read_text().splitlines():
        mm = re.match(r"\d+\s+(\w+)\((\d+)<([^>]*)>", line)
        if mm:
            path = re.sub(r"\d{6,}", "N", mm.group(3).replace(str(base), "<store>"))
            key = (mm.group(1), path); cnt[key] = cnt.get(key, 0) + 1
    return [{"call": a, "target": b, "n": n} for (a, b), n in sorted(cnt.items(), key=lambda x: -x[1])]

if __name__ == "__main__":
    image, base, out, posts = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    conns = [int(x) for x in sys.argv[5].split(",")]
    env = se.image_env()
    res = {"image": str(image), "filesystem": se.filesystem(base.parent) if base.parent.exists() else None, "arms": [], "loadavg": os.getloadavg()}
    for c in conns:
        res["arms"].append(arm(image, base, env, c, posts)); Path(out).write_text(json.dumps(res, indent=1))
    res["ysample"] = sample(image, base, env)
    res["loadavg_end"] = os.getloadavg()
    Path(out).write_text(json.dumps(res, indent=1)); print("done")
