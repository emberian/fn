#!/usr/bin/env python3
"""N POSTs of about OCTETS octets over one NNTP connection to an owner of
IMAGE (`operator CONFIG run`) on a fresh store under WORK, every POST timed;
prints one JSON line and writes every time to OUT.times.  Per-quarter
medians show growth with N; a POST that exceeds --timeout seconds is a stall:
the driver then records the owner's thread states (/proc), traces its
syscalls for a few seconds (strace -f -p), asks the profiler to report
(SIGUSR1, with --prof), and stops the owner.

With --prof OUT the owner runs under prof-owner.lisp (sb-sprof :cpu from
inside the image, no polling thread): the launcher's own sbcl command line
with the profiler loaded before ACL2's restart.  PROF_SECONDS caps the
profile; the driver sends SIGUSR1 at the end of a completed load so the
report covers the whole run.

The client is the base tree's rep_measure article/post and msgid_measure
connection (FN_CLIENT_TREE), the same bytes for every image."""
import argparse, json, os, signal, shlex, statistics, subprocess, sys, time
from pathlib import Path
CLIENT = Path(os.environ.get("FN_CLIENT_TREE", "/tank/fn/scratch/publish-program/native-base-17ff24aa/tree"))
sys.path.insert(0, str(CLIENT / "tools")); sys.path.insert(0, str(CLIENT))
import msgid_measure as m  # noqa: E402
import rep_measure as r  # noqa: E402
from tests.native_process import wait_for_announcement  # noqa: E402

def cpu_seconds(pid):
    fields = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")

def thread_states(pid):
    rows = []
    task = Path("/proc/%d/task" % pid)
    for t in sorted(task.iterdir(), key=lambda p: int(p.name)):
        try:
            stat = (t / "stat").read_text().rsplit(")", 1)
            name = stat[0].split("(", 1)[1]
            state = stat[1].split()[0]
            wchan = (t / "wchan").read_text().strip()
            rows.append("%s %s state=%s wchan=%s" % (t.name, name, state, wchan))
        except OSError:
            pass
    return rows

def launcher_argv(image, prof_out):
    """The launcher's exec line with prof-owner.lisp loaded before ACL2's restart."""
    text = Path(image).read_text()
    exec_line = [l for l in text.splitlines() if l.startswith("exec ")][0]
    argv = shlex.split(exec_line[len("exec "):])
    argv = [a for a in argv if a not in ("${SBCL_USER_ARGS}", "$@")]
    i = argv.index("(acl2::sbcl-restart)")
    prof = str(Path(__file__).resolve().parent / "prof-owner.lisp")
    argv[i - 1:i - 1] = ["--eval", '(load "%s")' % prof]
    return argv

p = argparse.ArgumentParser()
p.add_argument("--image", required=True); p.add_argument("--work", required=True)
p.add_argument("--n", type=int, default=10000); p.add_argument("--octets", type=int, default=2048)
p.add_argument("--profile", default="default", help="init profile: default (rep-wave-c's) or scale")
p.add_argument("--timeout", type=float, default=900.0, help="seconds one POST may take before it is a stall")
p.add_argument("--prof", default=None, help="sb-sprof report path (runs the owner under prof-owner.lisp)")
p.add_argument("--prof-seconds", type=int, default=1800)
p.add_argument("--out", required=True, help="prefix for .json, .times, .stall, owner.stderr copies")
a = p.parse_args()
work = Path(a.work); work.mkdir(parents=True, exist_ok=False)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None)
port = m.free_port()
cfg = work / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
               % (work / "store", port, work / "c.sock"), encoding="ascii")
init_args = ["--profile", a.profile] + (["--max-transactions", "1048576", "--max-article-octets",
                                          str(max(4096, a.octets + 1024))] if a.profile == "scale" else [])
init = subprocess.run([a.image, "--fn", "operator", str(cfg), "init"] + init_args + ["fn.letters", "fn.test"],
                      env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if init.returncode:
    raise SystemExit("init rc=%d %r" % (init.returncode, init.stdout[-300:]))
err = open(work / "owner.stderr", "ab")
if a.prof:
    env["PROF_OUT"] = a.prof; env["PROF_SECONDS"] = str(a.prof_seconds)
    env.setdefault("SBCL_HOME", "/tank/fn/sbcl/lib/sbcl/")
    argv = launcher_argv(a.image, a.prof) + ["--fn", "operator", str(cfg), "run"]
    proc = subprocess.Popen(argv, env=env, stdout=subprocess.PIPE, stderr=err)
    wait_for_announcement(proc, b"LISTENING ", timeout=3600)
else:
    proc, _, err = r.start_owner(Path(a.image), cfg, env, work / "owner.stderr")
result = {"n": a.n, "octets": a.octets, "profile": a.profile, "image": a.image, "prof": a.prof,
          "core_sha256": m.digest(a.image + ".core"), "filesystem": "tmpfs" if str(work).startswith("/dev/shm") else "zfs",
          "load_before": open("/proc/loadavg").read().split()[:3]}
times, stalled = [], None
try:
    c = m.Conn(port)
    c.sock.settimeout(a.timeout)
    c0, t0 = cpu_seconds(proc.pid), time.perf_counter()
    for i in range(a.n):
        try:
            times.append(r.post(c, i, a.octets))
        except (TimeoutError, OSError) as e:
            stalled = {"index": i, "error": repr(e), "elapsed_s": round(time.perf_counter() - t0, 3),
                       "threads": thread_states(proc.pid), "rss_kib": m.rss_kib(proc.pid)}
            tr = subprocess.run(["timeout", "10", "strace", "-f", "-tt", "-T", "-p", str(proc.pid)],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            Path(a.out + ".stall").write_text(json.dumps(stalled, indent=1) + "\n== strace 10 s\n" + tr.stdout[-20000:])
            print("STALL at POST %d after %.1f s: %r" % (i, stalled["elapsed_s"], e), flush=True)
            break
        if (i + 1) % 1000 == 0:
            last = times[-1000:]
            print("posted %d: last-1000 median %.2f ms p95 %.2f max %.2f; %.1f s elapsed; rss %d KiB" % (
                i + 1, 1000 * statistics.median(last), 1000 * sorted(last)[int(0.95 * len(last)) - 1],
                1000 * max(last), time.perf_counter() - t0, m.rss_kib(proc.pid)), flush=True)
    wall, cpu = time.perf_counter() - t0, cpu_seconds(proc.pid) - c0
    result["rss_after_load_kib"] = m.rss_kib(proc.pid)
    if a.prof:
        os.kill(proc.pid, signal.SIGUSR1)
        for _ in range(600):
            if Path(a.prof).exists() and proc.poll() is not None:
                break
            time.sleep(0.5)
    try:
        c.close()
    except OSError:
        pass
finally:
    r.stop_owner(proc, err)
    try:
        (Path(a.out + ".owner.stderr")).write_bytes((work / "owner.stderr").read_bytes()[-200000:])
    except OSError:
        pass
Path(a.out + ".times").write_text("".join("%.6f\n" % t for t in times))
q = max(1, len(times) // 4)
def summ(xs):
    if not xs:
        return None
    s = sorted(xs)
    return {"n": len(xs), "median_ms": round(1000 * statistics.median(xs), 3),
            "p95_ms": round(1000 * s[max(0, int(0.95 * len(s)) - 1)], 3), "max_ms": round(1000 * s[-1], 3),
            "argmax": xs.index(s[-1])}
result.update({"completed": len(times), "load_s": round(wall, 3), "owner_cpu_s": round(cpu, 3),
               "owner_cpu_ms_per_post": round(1000 * cpu / max(1, len(times)), 3),
               "first_quarter": summ(times[:q]), "last_quarter": summ(times[-q:]), "all": summ(times),
               "stalled": stalled and {k: stalled[k] for k in ("index", "error", "elapsed_s")},
               "load_after": open("/proc/loadavg").read().split()[:3]})
Path(a.out + ".json").write_text(json.dumps(result, indent=1) + "\n")
print(json.dumps({k: result[k] for k in ("completed", "load_s", "owner_cpu_ms_per_post", "first_quarter", "last_quarter", "all", "stalled")}))
