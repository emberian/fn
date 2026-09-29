#!/usr/bin/env python3
"""F8 measurement (reservation-after-flip scratch).  One store under FLAGS:
init; the launcher's figure (`heap -- operator CONFIG run`); N POSTs of L octets
at HEAP_BUILD MB (RSS at start/after N, the in-use figure when --build-heap is the figure);
stop; reopen at the figure (RSS after); then bisect the least --dynamic-space-size at which
(a) the owner reopens and serves ARTICLE 0, (b) the owner reopens and takes EXTRA more POSTs.
usage: floor.py TREE IMAGE WORK --posts N --octets L [--flags ...] [--build-heap MB|figure] [--extra K]"""
import argparse, json, os, re, shutil, subprocess, sys, threading, time
from pathlib import Path
ap = argparse.ArgumentParser()
ap.add_argument("tree"); ap.add_argument("image"); ap.add_argument("work")
ap.add_argument("--posts", type=int, default=1000); ap.add_argument("--octets", type=int, default=2048)
ap.add_argument("--flags", default="--profile development --max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-groups-per-article 16 --max-open-suffix 128")
ap.add_argument("--build-heap", default="figure"); ap.add_argument("--extra", type=int, default=50)
ap.add_argument("--lo", type=int, default=96); ap.add_argument("--hi", type=int, default=0)
ap.add_argument("--no-bisect", action="store_true")
a = ap.parse_args()
sys.path.insert(0, a.tree + "/tools"); sys.path.insert(0, a.tree)
import rep_measure as r, msgid_measure as m
sys.path.insert(0, a.tree + "/tools/runtime_image"); import node_measure as nm
work = Path(a.work); shutil.rmtree(work, ignore_errors=True); work.mkdir(parents=True)
base = dict(os.environ); base["ACL2_CUSTOMIZATION"] = "NONE"; base.pop("ACL2_SYSTEM_BOOKS", None)
def env(mb, stack=None):
    e = dict(base); e["SBCL_USER_ARGS"] = "--dynamic-space-size %dMB" % mb + (" --control-stack-size %dKB" % stack if stack else ""); return e
port = m.free_port(); config = work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (work / "store", port, work / "c.sock"))
out = {"image": a.image, "flags": a.flags, "posts": a.posts, "octets": a.octets}
res = subprocess.run([a.image, "--fn", "operator", str(config), "init"] + a.flags.split() + ["fn.letters", "fn.test"], env=env(2048), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out["init"] = res.stdout.decode(errors="replace").strip()[-300:]
def figure():
    f = subprocess.run([a.image, "--fn", "heap", "--", "operator", str(config), "run"], env=env(2048), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    t = f.stdout.decode(errors="replace").strip()
    mm = re.search(r"heap=(\d+) MB", t); ss = re.search(r"stack=(\d+) KB", t)
    return t, (int(mm.group(1)) if mm else None), (int(ss.group(1)) if ss else None)
out["figure_line"], fig, stack = figure()
bh = fig if a.build_heap == "figure" else int(a.build_heap)
out["build_heap_mb"] = bh
proc, s, err = r.start_owner(Path(a.image), config, env(bh, stack), work / "owner.stderr", timeout=600)
try:
    time.sleep(1); out["start"] = nm.rss(proc.pid)
    c = m.Conn(port); t0 = time.time()
    for i in range(a.posts):
        r.post(c, i, a.octets)
        if i + 1 in (100, 1000, 4000, 10000, 16000): out["after_%d" % (i + 1)] = nm.rss(proc.pid)
    out["post_s"] = round(time.time() - t0, 2); c.close(); time.sleep(1); out["end"] = nm.rss(proc.pid)
finally:
    r.stop_owner(proc, err)
st = subprocess.run([a.image, "--fn", "operator", str(config), "status"], env=env(2048), stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.decode(errors="replace")
out["status_headroom"] = next((l for l in st.splitlines() if l.startswith("headroom")), None)
out["status_open"] = next((l for l in st.splitlines() if l.startswith("open=")), None)
out["figure_line_after"], fig2, _ = figure()
try:
    # The reopen's anonymous peak (F1's measure, J2): RssAnon sampled every
    # 20 ms from the spawn through LISTENING and one settled second after.
    err = open(work / "owner.stderr", "ab"); t0 = time.perf_counter()
    proc = subprocess.Popen([a.image, "--fn", "operator", str(config), "run"], env=env(bh, stack),
                            stdout=subprocess.PIPE, stderr=err)
    peak, stop = {"anon": 0}, threading.Event()
    def sample():
        while not stop.is_set():
            v = r.status_kib(proc.pid, "RssAnon") if os.path.exists("/proc/%d/status" % proc.pid) else None
            if v is None: return
            peak["anon"] = max(peak["anon"], v); stop.wait(0.02)
    threading.Thread(target=sample, daemon=True).start()
    try:
        r.wait_for_announcement(proc, b"LISTENING ", timeout=600, stderr_path=work / "owner.stderr")
        out["reopen_s"] = round(time.perf_counter() - t0, 3); time.sleep(1); out["after_reopen"] = nm.rss(proc.pid)
        stop.set(); out["after_reopen"]["anon_peak_kib"] = peak["anon"] or None
    finally:
        stop.set(); r.stop_owner(proc, err)
except BaseException as e:
    out["reopen_at_figure"] = "failed: %s" % str(e)[:200]
snap = work / "snap"; shutil.copytree(work / "store", snap, symlinks=True)
def restore():
    shutil.rmtree(work / "store"); shutil.copytree(snap, work / "store", symlinks=True)
def attempt(mb, extra):
    restore()
    try:
        proc, s, err = r.start_owner(Path(a.image), config, env(mb, stack), work / "probe.stderr", timeout=600)
    except BaseException as e:
        return False, "start: %s" % str(e)[-160:]
    try:
        c = m.Conn(port)
        if extra:
            for i in range(a.posts, a.posts + extra): r.post(c, i, a.octets)
            c.close(); c = m.Conn(port)
        reply = c.line("STAT %s" % m.msgid(0)); c.close()
        return reply.startswith(b"223"), "%.2f s %r" % (s, reply[:12])
    except BaseException as e:
        return False, "session: %s" % str(e)[-160:]
    finally:
        try: r.stop_owner(proc, err)
        except BaseException: pass
def bisect(extra):
    lo, hi = a.lo, a.hi or fig2 or 2048; rows = []
    ok, why = attempt(hi, extra); rows.append([hi, ok, why])
    if not ok: return {"floor_mb": None, "trials": rows}
    while hi - lo > 4:
        mid = (lo + hi) // 2; ok, why = attempt(mid, extra); rows.append([mid, ok, why])
        if ok: hi = mid
        else: lo = mid
    return {"floor_mb": hi, "failed_at_mb": lo, "trials": rows}
if not a.no_bisect:
    out["reopen_floor"] = bisect(0)
    if a.extra: out["reopen_post_floor"] = bisect(a.extra)
print(json.dumps(out, indent=1))
