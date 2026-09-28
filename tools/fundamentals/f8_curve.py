#!/usr/bin/env python3
"""F8 by curve (lane f8-reservation, 2026-09-28; ember: SCALE BY CURVE).

usage: f8_curve.py TREE HEAP-IMAGE WORK [--points 1000,2000,...] [--octets L]
                   [--heap MB] [--flags ...]

One store under FLAGS (default: T 131,072, H 512 MiB, the small preset's R,
G and suffix, so that it holds the largest point), one owner at a fixed
--dynamic-space-size HEAP, POSTs of L octets, and at 0 and at each point N:
the process's VmRSS/VmHWM/anonymous and thread count (before), then through
the heap hook (tools/fundamentals/hook.lisp, FN_PROF_LOAD) the dynamic usage
before and after a full collection and ROOM's per-type breakdown of the live
heap.  Then status, the launcher's figure over the store on disk, and a
reopen with the same snapshot.  JSON on stdout.  A measurement: it decides
nothing; tools/f8_breakdown.py fits it against the model's terms.
"""
import argparse, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
ap = argparse.ArgumentParser()
ap.add_argument("tree"); ap.add_argument("image"); ap.add_argument("work")
ap.add_argument("--points", default="1000,2000,5000,10000,25000,50000,100000")
ap.add_argument("--octets", type=int, default=2048)
ap.add_argument("--heap", type=int, default=4096)
ap.add_argument("--msgid-octets", type=int, default=0, help="pad each Message-ID to this many octets (250: RFC 5536's ceiling)")
ap.add_argument("--subject-octets", type=int, default=0, help="pad each Subject to about this many octets (folded)")
ap.add_argument("--flags", default="--profile development --max-transactions 131072 --max-history-octets 536870912 --max-record-octets 196608 --max-groups-per-article 16 --max-open-suffix 128")
a = ap.parse_args()
sys.path.insert(0, a.tree + "/tools"); sys.path.insert(0, a.tree)
import rep_measure as r, msgid_measure as m
sys.path.insert(0, a.tree + "/tools/runtime_image"); import node_measure as nm
if a.msgid_octets:
    base_id = m.msgid
    def long_id(i, _b=base_id, _n=a.msgid_octets):
        x = _b(i); pad = max(0, _n - len(x) - 1)
        return x[:-1].replace("@", "-" + "p" * pad + "@", 1) + ">" if pad else x
    m.msgid = long_id
if a.subject_octets:
    fold = "\r\n " + ("s" * 70)
    r.HEAD = r.HEAD.replace("Subject: rep %d\r\n", "Subject: rep %d" + fold * (a.subject_octets // 73) + "\r\n", 1)
points = [int(x) for x in a.points.split(",")]
work = Path(a.work); shutil.rmtree(work, ignore_errors=True); work.mkdir(parents=True)
heapd = work / "heap"; heapd.mkdir()
env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
env["FN_HEAP_DIR"] = str(heapd); env["FN_PROF_LOAD"] = str(Path(a.tree) / "tools/fundamentals/hook.lisp")
env["SBCL_USER_ARGS"] = "--dynamic-space-size %dMB" % a.heap
env["FN_INIT_BUDGET_MB"] = "1048576"
port = m.free_port(); config = work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (work / "store", port, work / "c.sock"))
res = subprocess.run([a.image, "--fn", "operator", str(config), "init"] + a.flags.split() + ["fn.letters", "fn.test"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out = {"image": a.image, "flags": a.flags, "msgid_octets": a.msgid_octets, "subject_octets": a.subject_octets, "octets": a.octets, "heap_mb": a.heap, "init": res.stdout.decode(errors="replace")[-400:], "points": {}}
ROOM = re.compile(r"^\s*([\d,]+) bytes for\s+([\d,]+) (.+?) objects")
def snap(tag):
    (heapd / "go").write_text(tag)
    t = time.time()
    while not (heapd / ("done-" + tag)).exists():
        if time.time() - t > 600: return {"error": "timeout"}
        time.sleep(0.05)
    doc, types = {}, {}
    for line in (heapd / ("heap-" + tag + ".txt")).read_text().splitlines():
        p = line.split()
        if len(p) == 2 and p[1].isdigit(): doc[p[0]] = int(p[1])
        mm = ROOM.match(line)
        if mm and mm.group(3) not in ("dynamic", "immobile") and len(types) < 12:
            types[mm.group(3)] = int(mm.group(1).replace(",", ""))
    doc["room"] = types
    return doc
def proc_doc(pid):
    d = nm.rss(pid)
    try: d["threads"] = len(os.listdir("/proc/%d/task" % pid))
    except OSError: pass
    return d
proc, secs, err = r.start_owner(Path(a.image), config, env, work / "owner.stderr", timeout=600)
try:
    time.sleep(1)
    out["points"]["0"] = {"proc": proc_doc(proc.pid), "heap": snap("gc-0")}
    c = m.Conn(port); t0 = time.time(); i = 0
    for n in points:
        while i < n:
            r.post(c, i, a.octets); i += 1
        pd = proc_doc(proc.pid)
        out["points"][str(n)] = {"proc": pd, "heap": snap("gc-%d" % n), "post_s": round(time.time() - t0, 2)}
        print("point", n, pd.get("rss_kib"), out["points"][str(n)]["heap"].get("dynamic-usage-after-gc"), file=sys.stderr, flush=True)
    c.close()
except BaseException as e:
    out["post_error"] = str(e)[-600:]
finally:
    r.stop_owner(proc, err)
def finish():
    print(json.dumps(out, indent=1))
try:
    st = subprocess.run([a.image, "--fn", "operator", str(config), "status"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.decode(errors="replace")
    out["status"] = [l for l in st.splitlines() if l.startswith(("headroom", "open=", "heap="))]
    fig = subprocess.run([a.image, "--fn", "heap", "--", "operator", str(config), "run"], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out["figure_after"] = fig.stdout.decode(errors="replace").strip()[-300:]
    mm = re.search(r"heap=(\d+) MB", out["figure_after"])
    # The reopen runs at the launcher's own figure for the store on disk (never
    # less than --heap), so its VmHWM is the open's peak under the figure.
    rh = max(a.heap, int(mm.group(1))) if mm else a.heap
    env["SBCL_USER_ARGS"] = "--dynamic-space-size %dMB" % rh
    out["reopen_heap_mb"] = rh
    proc, secs, err = r.start_owner(Path(a.image), config, env, work / "owner.stderr", timeout=1800)
    try:
        out["reopen_s"] = round(secs, 3); time.sleep(1)
        out["reopen"] = {"proc": proc_doc(proc.pid), "heap": snap("gc-reopen")}
    finally:
        r.stop_owner(proc, err)
except BaseException as e:
    out["reopen_error"] = str(e)[-600:]
finally:
    out["stderr_tail"] = [l for l in (work / "owner.stderr").read_text(errors="replace")[-4000:].splitlines() if "FN-SRS-DECODE" not in l][-12:]
    finish()
