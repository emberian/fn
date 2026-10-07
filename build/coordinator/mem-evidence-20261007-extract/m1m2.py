#!/usr/bin/env python3
"""M1/M2 one-shot: floor, fn-core identity, fn-core empty open, ACL2 image empty open.
usage: m1m2.py OUTDIR [--core LAUNCHER] [--steps floor,identity,open-core,open-image] [--repeats 3] [--note TEXT]
Run on hbox under ONE `SWARM_MEM_MAX=36G swarm-build`. Same options for every step: tls 16384, heap 1068MB.
Kills only PIDs it started (Popen), every wait has a deadline. Records uptime, VmRSS/VmHWM, smaps core Rss, anon."""
import argparse, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("--core"); ap.add_argument("--repeats", type=int, default=3)
ap.add_argument("--steps", default="floor,identity,open-core,open-image"); ap.add_argument("--note", default=""); ap.add_argument("--tls", default="16384")
a = ap.parse_args()
OUT = Path(a.out); OUT.mkdir(parents=True, exist_ok=True)
SB = "/tank/fn/sbcl"; IMG = "/tank/fn/images/3e53d7bc5dbd72de73042b46e6174d316ef7a63d/fn-host"
RT = ["--tls-limit", a.tls, "--dynamic-space-size", "1068MB"]
FLAGS = "--profile development --max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-groups-per-article 16 --max-open-suffix 128".split()
rows = []
def kb(t, k):
    m = re.search(k + r":\s+(\d+)", t); return int(m.group(1)) if m else None
def snap(pid, corepath):
    st = Path(f"/proc/{pid}/status").read_text(); ro = Path(f"/proc/{pid}/smaps_rollup").read_text()
    core = 0; on = False
    for l in Path(f"/proc/{pid}/smaps").read_text().splitlines():
        if re.match(r"^[0-9a-f]+-[0-9a-f]+ ", l): on = l.rstrip().endswith(corepath)
        elif on and l.startswith("Rss:"): core += int(l.split()[1])
    return dict(vmrss=kb(st, "VmRSS"), vmhwm=kb(st, "VmHWM"), anon=kb(ro, "Anonymous"), core_rss=core)
def rec(step, i, d):
    d.update(step=step, rep=i, uptime=open("/proc/loadavg").read().split()[:3], t=time.strftime("%H:%M:%S")); rows.append(d)
    print(json.dumps(d), flush=True)
def poll_until_exit(p, corepath, limit=60):
    last = None; t0 = time.time()
    while p.poll() is None and time.time() - t0 < limit:
        try: last = snap(p.pid, corepath)
        except Exception: pass
        time.sleep(0.01)
    if p.poll() is None: p.terminate(); p.wait(30)
    return last
def floor(i):
    core = f"{SB}/lib/sbcl/sbcl.core"; e = dict(os.environ, SBCL_HOME=f"{SB}/lib/sbcl/")
    p = subprocess.Popen([f"{SB}/bin/sbcl", *RT, "--control-stack-size", "1024KB", "--disable-ldb", "--core", core, "--noinform", "--end-runtime-options",
        "--no-userinit", "--no-sysinit", "--eval", "(sleep 12)", "--disable-debugger", "--end-toplevel-options"], env=e, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    time.sleep(6); rec("floor", i, snap(p.pid, core)); p.terminate(); p.wait(30)
def identity(i):
    core = str(Path(a.core).with_suffix(".core")); e = dict(os.environ, SBCL_USER_ARGS=" ".join(RT))
    p = subprocess.Popen([a.core, "identity"], env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    s = poll_until_exit(p, core); rec("identity", i, dict(s or {}, exit=p.returncode))
def open_(step, launcher, core, i):
    work = OUT / f"{step}-{i}"; shutil.rmtree(work, ignore_errors=True); work.mkdir(parents=True)
    port = 20000 + (os.getpid() + i * 7 + len(step)) % 20000
    cfg = work / "fn.toml"; cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (work / "store", port, work / "c.sock"))
    e = dict(os.environ, ACL2_CUSTOMIZATION="NONE", SBCL_USER_ARGS=" ".join(RT))
    r = subprocess.run([launcher, "--fn", "operator", str(cfg), "init", *FLAGS, "fn.letters", "fn.test"], env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
    (work / "init.log").write_bytes(r.stdout)
    err = open(work / "owner.err", "wb")
    p = subprocess.Popen([launcher, "--fn", "operator", str(cfg), "run"], env=e, stdout=subprocess.PIPE, stderr=err)
    t0 = time.time(); ok = False
    import select
    buf = b""
    while time.time() - t0 < 600 and p.poll() is None:
        if select.select([p.stdout], [], [], 1)[0]:
            c = os.read(p.stdout.fileno(), 4096)
            if not c: break
            buf += c
            if b"LISTENING " in buf: ok = True; break
    if not ok: rec(step, i, dict(error="no LISTENING", init_exit=r.returncode, tail=buf[-300:].decode("latin-1"))); p.terminate(); p.wait(30); return
    time.sleep(6); rec(step, i, dict(snap(p.pid, core), init_exit=r.returncode, open_s=round(time.time() - t0, 1)))
    p.terminate(); p.wait(60)
for step in a.steps.split(","):
    for i in range(a.repeats):
        if step == "floor": floor(i)
        elif step == "identity": identity(i)
        elif step == "open-core": open_(step, a.core, str(Path(a.core).with_suffix(".core")), i)
        elif step == "open-image": open_(step, IMG, IMG + ".core", i)
(OUT / "results.json").write_text(json.dumps(dict(note=a.note, tls=a.tls, rows=rows), indent=1))
print("\nsummary (median VmRSS / anon / core_rss kB):")
for step in dict.fromkeys(r["step"] for r in rows):
    rr = sorted([r for r in rows if r["step"] == step and r.get("vmrss")], key=lambda r: r["vmrss"])
    if rr: m = rr[len(rr) // 2]; print(step, m["vmrss"], m["anon"], m["core_rss"], "load", m["uptime"])
