#!/usr/bin/env python3
"""MEM-007: one run = fresh store, N POSTs at the small preset, per-POST (t, latency) + publication/GC log + RSS samples.
usage: mem7.py RUNDIR SETTING(64|8) POSTS     (SETTING 64 = image default, 8 = 8 MiB publication trigger)"""
import os, sys, time, subprocess, re, json, threading, shutil
from pathlib import Path
B = Path("/tank/fn/scratch/n-mem"); sys.path.insert(0, str(B/"tools")); sys.path.insert(0, str(B))
import rep_measure as r, msgid_measure as m
S = Path("/tank/fn/scratch/n-mem7")
work = Path(sys.argv[1]); setting = sys.argv[2]; posts = int(sys.argv[3])
shutil.rmtree(work, ignore_errors=True); work.mkdir(parents=True)
port = m.free_port(); cfg = work/"fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (work/"store", port, work/"c.sock"))
e = dict(os.environ); e["ACL2_CUSTOMIZATION"] = "NONE"; e["MEM7_LOG"] = str(work/"events.log")
e["SBCL_USER_ARGS"] = "--dynamic-space-size 1068MB"
if setting == "8": e["MEM7_PUBNURSERY"] = str(8*1024*1024)
IMG = str(S/"fn-host-mem7.sh")
flags = "--profile development --max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-groups-per-article 16 --max-open-suffix 128".split()
subprocess.run([IMG,"--fn","operator",str(cfg),"init"]+flags+["fn.letters","fn.test"], env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
p = subprocess.Popen([IMG,"--fn","operator",str(cfg),"run"], env=e, stdout=subprocess.PIPE, stderr=open(work/"owner.err","ab"))
r.wait_for_announcement(p, b"LISTENING ", timeout=900, stderr_path=work/"owner.err"); time.sleep(3)
def snap():
    st = Path("/proc/%d/status"%p.pid).read_text()
    g = lambda k: int(re.search(k+r":\s+(\d+)", st).group(1))
    return g("VmRSS"), g("VmHWM")
stop = threading.Event(); rows = []
def sampler():
    while not stop.is_set():
        rss, hwm = snap(); rows.append((time.time(), rss, hwm)); time.sleep(0.05)
th = threading.Thread(target=sampler); th.start()
c = m.Conn(port); lat = []; errs = []; t0 = time.time()
for i in range(posts):
    s = time.time(); t = time.perf_counter()
    try:
        r.post(c, i, 2048); lat.append((s, time.perf_counter()-t))
    except SystemExit as ex:
        errs.append((i, str(ex)[:120])); break
c.close(); wall = time.time()-t0; time.sleep(2); stop.set(); th.join()
steady = rows[-1][1]; hwm = rows[-1][2]
(work/"posts.csv").write_text("\n".join("%.6f,%.6f" % x for x in lat))
(work/"samples.csv").write_text("\n".join("%.3f,%d,%d" % x for x in rows))
json.dump({"setting": setting, "posts_ok": len(lat), "errors": errs, "wall_s": round(wall,1), "hwm_kb": hwm, "steady_rss_kb": steady,
           "peak_sampled_rss_kb": max(x[1] for x in rows), "load1": os.getloadavg()[0]}, open(work/"out.json","w"))
p.terminate(); p.wait(120); print(open(work/"out.json").read())
