#!/usr/bin/env python3
"""N POSTs of about OCTETS octets over one NNTP connection to an owner of IMAGE
(`operator CONFIG run`) on a fresh store under WORK; prints one JSON line:
per-POST median and p95, the owner's CPU seconds over the load, and (with
--strace) the owner's sync-family syscall counts over the load.  The client
is the dev tree's rep_measure article/post and msgid_measure connection, the
same bytes for every image."""
import argparse, json, os, subprocess, sys, time
from pathlib import Path
CLIENT = Path(os.environ.get("FN_CLIENT_TREE", "/tank/fn/scratch/publish-program/native-base-17ff24aa/tree"))
sys.path.insert(0, str(CLIENT / "tools")); sys.path.insert(0, str(CLIENT))
import msgid_measure as m  # noqa: E402
import rep_measure as r  # noqa: E402

def cpu_seconds(pid):
    fields = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")

p = argparse.ArgumentParser()
p.add_argument("--image", required=True); p.add_argument("--work", required=True)
p.add_argument("--n", type=int, default=100); p.add_argument("--octets", type=int, default=2048)
p.add_argument("--strace", default=None)
a = p.parse_args()
work = Path(a.work); work.mkdir(parents=True, exist_ok=False)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None)
port = m.free_port()
cfg = work / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
               % (work / "store", port, work / "c.sock"), encoding="ascii")
init = subprocess.run([a.image, "--fn", "operator", str(cfg), "init", "--profile", "scale",
                       "--max-transactions", "1048576", "--max-article-octets", "4096", "fn.letters", "fn.test"],
                      env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if init.returncode:
    raise SystemExit("init rc=%d %r" % (init.returncode, init.stdout[-300:]))
proc, open_s, err = r.start_owner(Path(a.image), cfg, env, work / "owner.stderr")
tracer = None
try:
    if a.strace:
        tracer = subprocess.Popen(["strace", "-f", "-c", "-o", a.strace, "-e",
                                   "trace=fsync,fdatasync,syncfs,sync_file_range,rename,renameat,renameat2,link,linkat",
                                   "-p", str(proc.pid)], stderr=subprocess.DEVNULL)
        time.sleep(1.0)
    c = m.Conn(port)
    c0, t0 = cpu_seconds(proc.pid), time.perf_counter()
    times = [r.post(c, i, a.octets) for i in range(a.n)]
    wall, cpu = time.perf_counter() - t0, cpu_seconds(proc.pid) - c0
    c.close()
finally:
    if tracer:
        tracer.terminate(); tracer.wait(timeout=60)
    r.stop_owner(proc, err)
s = m.summary(times)
print(json.dumps({"n": a.n, "octets": len(r.article(0, a.octets)), "median_ms": round(s["median_ms"], 2),
                  "p95_ms": round(s["p95_ms"], 2), "max_ms": round(s["max_ms"], 2), "load_s": round(wall, 3),
                  "owner_cpu_s": round(cpu, 3), "owner_cpu_ms_per_post": round(1000 * cpu / a.n, 2)}))
