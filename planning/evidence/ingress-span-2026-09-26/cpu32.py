#!/usr/bin/env python3
"""Owner CPU per 32 KiB POST, before and after, alternating (ingress-span-2).

tools/throughput_gate.py's served row on the default profile (which admits
32 KiB articles, as rep_measure uses it): 120 POSTs of 32,768 octets on one connection to
`operator run`, owner CPU (utime+stime of the owner process) per POST.
Usage: cpu32.py TREE BEFORE_IMAGE AFTER_IMAGE OUT.json
"""
import json, shutil, sys, time
from pathlib import Path
tree, before, after, out_path = sys.argv[1:5]
sys.path.insert(0, tree + "/tools")
import throughput_gate as g
import msgid_measure as m
import rep_measure as r

env = g.os.environ.copy()
env["ACL2_CUSTOMIZATION"] = "NONE"
rows = []
for rnd in (1, 2, 3):
    for side, image in (("before", before), ("after", after)):
        work = Path("/dev/shm/ingress-span-2/cpu32-%s-%d" % (side, rnd))
        shutil.rmtree(work, ignore_errors=True)
        work.mkdir(parents=True)
        port = m.free_port()
        config = g.write_config(work, port, work / "store")
        g.init_store(image, config, env, ["--profile", "default", "fn.letters", "fn.test"])
        proc, _, err = r.start_owner(Path(image), config, env, work / "owner.stderr")
        try:
            c = m.Conn(port)
            for i in range(8):  # warm the owner (first-call paths) outside the window
                r.post(c, 10000 + i, 32768)
            c0, t0 = g.owner_cpu(proc.pid), time.perf_counter()
            times = [r.post(c, i, 32768) for i in range(120)]
            cpu = g.owner_cpu(proc.pid) - c0
            wall = time.perf_counter() - t0
            c.close()
            s = m.summary(times)
            row = {"side": side, "round": rnd, "image": image, "posts": 120,
                   "article_octets": len(r.article(0, 32768)),
                   "owner_cpu_ms_per_post": round(1000.0 * cpu / 120, 3),
                   "post_median_ms": round(s["median_ms"], 3), "post_p95_ms": round(s["p95_ms"], 3),
                   "load_s": round(wall, 3), "loadavg": open("/proc/loadavg").read().split()[:3]}
        finally:
            proc.terminate()
            proc.wait(timeout=60)
        shutil.rmtree(work, ignore_errors=True)
        print(json.dumps(row), flush=True)
        rows.append(row)
Path(out_path).write_text(json.dumps(rows, indent=1) + "\n")
