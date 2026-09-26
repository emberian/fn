#!/usr/bin/env python3
"""perf-ledger (2026-09-26): one measured phase on the profiling twin of dev.

    python3 perf.py PHASE WORK [ARGS]   (run from the image's tree root)

Every phase runs `operator run` of build/fn-host-developer-prof (the developer
image plus the scratch profiling entry prof-raw.lisp) with FN_PROF_LOAD =
hooks.lisp (the heap hook: bytes consed on demand; the alloc-mode sampler) and
writes WORK/PHASE.json.  A CPU window is sb-sprof :cpu at 1 ms over all
threads between FN_SPROF_DIR/start and /stop; an alloc window is sb-sprof
:alloc between FN_ALLOC_DIR/start and /stop.  sb-sprof allows one session per
process, so a phase has one window.  Owner CPU is /proc/PID/stat utime+stime
over the window.

Phases:
  load WORK N OCTETS          init (default profile, group fn.test), N POSTs
  post WORK K cpu|alloc       reopen; the window over K POSTs of 2,048 octets
  reads WORK                  reopen; timings (greeting, GROUP, STAT, ARTICLE,
                              OVER 40-row, OVER 1-2000); the CPU window over
                              five OVER 1-2000
  greet WORK K                reopen; the CPU window over K greetings
  ckptopen WORK               offline `store checkpoint`, then the open from it
                              with the CPU window from launch to LISTENING
  chain WORK FIXTURE          a copy of FIXTURE/store: the first open, the CPU
                              window from LISTENING to the automatic capture's
                              CHECKPOINT line; then the reopen from that
                              checkpoint with the CPU window over the open;
                              greeting, GROUP, OVER 1-2000 at N = 20,000
  big WORK                    a 4 MiB-article profile: POST and ARTICLE of
                              2 KiB, 32 KiB and 3 MiB, bytes consed per op;
                              the CPU window over three 3 MiB ARTICLEs
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path.cwd()
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
import msgid_measure as m  # noqa: E402
import rep_measure as r  # noqa: E402

S = Path("/tank/fn/scratch/perf-ledger")
IMAGE = ROOT / "build/fn-host-developer-prof"
TICK = os.sysconf("SC_CLK_TCK")


def env_for(work, sprof=None, alloc=None):
    e = dict(os.environ)
    e["ACL2_CUSTOMIZATION"] = "NONE"
    e.pop("ACL2_SYSTEM_BOOKS", None)
    e["FN_PROF_LOAD"] = str(S / "hooks.lisp")
    e["FN_HEAP_DIR"] = str(work / "heap")
    (work / "heap").mkdir(parents=True, exist_ok=True)
    for key, d in (("FN_SPROF_DIR", sprof), ("FN_ALLOC_DIR", alloc)):
        if d is not None:
            shutil.rmtree(d, ignore_errors=True)
            d.mkdir(parents=True)
            e[key] = str(d)
    return e


def cpu_s(pid):
    f = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(f[11]) + int(f[12])) / TICK


def write_config(work, store):
    port = m.free_port()
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, work / "control.sock"), encoding="ascii")
    return config, port


class Window:
    def __init__(self, d, proc):
        self.d, self.proc = d, proc

    def start(self):
        self.c0 = cpu_s(self.proc.pid)
        self.t0 = time.perf_counter()
        (self.d / "start").write_text("1")
        time.sleep(0.2)

    def stop(self):
        (self.d / "stop").write_text("1")
        out = {"window_wall_s": time.perf_counter() - self.t0,
               "window_owner_cpu_s": cpu_s(self.proc.pid) - self.c0}
        t = time.perf_counter()
        while not (self.d / "done").exists():
            time.sleep(0.1)
            if time.perf_counter() - t > 900:
                out["report"] = "no done file in 900 s"
                return out
        out["error"] = (self.d / "error.txt").read_text() if (self.d / "error.txt").exists() else None
        return out


def open_line(stderr_path):
    try:
        text = Path(stderr_path).read_text(errors="replace")
    except OSError:
        return None
    rows = [l for l in text.splitlines() if "OWNER-OPEN" in l]
    return rows[-1] if rows else None


def checkpoint_lines(stderr_path):
    try:
        text = Path(stderr_path).read_text(errors="replace")
    except OSError:
        return []
    return [l for l in text.splitlines() if l.startswith("CHECKPOINT")]


def start(work, config, e, tag, timeout=3600):
    t = time.perf_counter()
    proc, secs, err = r.start_owner(IMAGE, config, e, work / ("%s.stderr" % tag), timeout=timeout)
    return proc, secs, err


def multiline(c, text):
    dt, reply, octets = r.timed_multiline(c, text)
    return dt, reply, octets


def greetings(port, k):
    g = []
    for _ in range(k):
        t0 = time.perf_counter()
        c = m.Conn(port)
        g.append(time.perf_counter() - t0)
        c.close()
    return m.summary(g)


def bytes_per(heap, label, fn, k):
    return r.alloc_batch(heap, label, fn, k)


def box():
    try:
        units = subprocess.run(["systemctl", "--user", "list-units", "--state=running", "--no-legend",
                                "--plain"], stdout=subprocess.PIPE, text=True, timeout=30).stdout
    except Exception as ex:  # noqa: BLE001
        units = repr(ex)
    return {"loadavg": Path("/proc/loadavg").read_text().strip(),
            "running_user_units": [u.split()[0] for u in units.splitlines() if u.strip()]}


def phase_load(work, n, octets):
    work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    config, port = write_config(work, store)
    e = env_for(work)
    init = [str(IMAGE), "--fn", "operator", str(config), "init", "--profile", "default", "fn.test"]
    ir = subprocess.run(init, env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = {"init_rc": ir.returncode, "init_tail": ir.stdout.decode("ascii", "replace")[-300:]}
    proc, out["first_open_s"], err = start(work, config, e, "load")
    try:
        c = m.Conn(port)
        t = time.perf_counter()
        load = [r.post(c, i, octets) for i in range(n)]
        out["load_s"] = time.perf_counter() - t
        c.close()
        q = max(1, n // 4)
        out["post_first_quarter"] = m.summary(load[:q])
        out["post_last_quarter"] = m.summary(load[-q:])
        out["owner_cpu_s_total"] = cpu_s(proc.pid)
    finally:
        r.stop_owner(proc, err)
    out["checkpoint_lines"] = checkpoint_lines(work / "load.stderr")[-3:]
    out["n"], out["octets"] = n, octets
    return out


def reopen(work, tag, sprof=None, alloc=None, timeout=3600):
    config = work / "fn.toml"
    port = int(re.search(r"port = (\d+)", config.read_text()).group(1))
    e = env_for(work, sprof, alloc)
    proc, secs, err = start(work, config, e, tag, timeout)
    return proc, err, port, {"open_s": secs, "open_line": open_line(work / ("%s.stderr" % tag)),
                             "vmhwm_kib_at_listening": r.status_kib(proc.pid, "VmHWM")}


def phase_post(work, k, mode):
    d = work / ("sprof-post" if mode == "cpu" else "alloc-post")
    proc, err, port, out = reopen(work, "post-" + mode, sprof=d if mode == "cpu" else None,
                                  alloc=d if mode == "alloc" else None)
    heap = r.Heap(str(work / "heap"), proc)
    try:
        c = m.Conn(port)
        base = 900000 + (0 if mode == "cpu" else 100000)
        r.post(c, base - 1, 2048)
        h0 = heap.snap("p0")
        w = Window(d, proc)
        w.start()
        times = [r.post(c, base + i, 2048) for i in range(k)]
        out["window"] = w.stop()
        h1 = heap.snap("p1")
        out["post"] = m.summary(times)
        out["bytes_consed_per_post"] = (h1["bytes_consed"] - h0["bytes_consed"]) / k
        out["owner_cpu_ms_per_post"] = 1000 * out["window"]["window_owner_cpu_s"] / k
        c.close()
    finally:
        r.stop_owner(proc, err)
    out["k"], out["mode"] = k, mode
    return out


def phase_reads(work):
    d = work / "sprof-over2000"
    proc, err, port, out = reopen(work, "reads", sprof=d)
    heap = r.Heap(str(work / "heap"), proc)
    try:
        out["greeting_loaded"] = greetings(port, 32)
        c = m.Conn(port)
        g = []
        for _ in range(5):
            t0 = time.perf_counter()
            reply = c.line("GROUP fn.test")
            g.append(time.perf_counter() - t0)
        out["group"] = m.summary(g)
        out["group_reply"] = reply.decode("ascii", "replace").strip()
        high = int(reply.split()[3])
        nums = [1 + (i * (high - 41)) // 31 for i in range(32)]
        out["stat"] = bytes_per(heap, "stat", lambda i: c.timed("STAT %d" % nums[i % 32])[0], 32)
        out["article_2k"] = bytes_per(heap, "art", lambda i: multiline(c, "ARTICLE %d" % nums[i % 32])[0], 32)
        out["over_1"] = bytes_per(heap, "over1", lambda i: multiline(c, "OVER %d" % nums[i % 32])[0], 32)
        out["over_40"] = bytes_per(heap, "over40", lambda i: multiline(c, "OVER %d-%d" % (nums[i % 20], nums[i % 20] + 39))[0], 20)
        out["over_2000_uncovered"] = bytes_per(heap, "over2000", lambda i: multiline(c, "OVER 1-2000")[0], 3)
        w = Window(d, proc)
        w.start()
        t = [multiline(c, "OVER 1-2000")[0] for _ in range(5)]
        out["over_2000_profiled"] = m.summary(t)
        out["window"] = w.stop()
        c.close()
    finally:
        r.stop_owner(proc, err)
    return out


def phase_greet(work, k):
    d = work / "sprof-greet"
    proc, err, port, out = reopen(work, "greet", sprof=d)
    try:
        w = Window(d, proc)
        w.start()
        out["greeting"] = greetings(port, k)
        out["window"] = w.stop()
        out["owner_cpu_ms_per_greeting"] = 1000 * out["window"]["window_owner_cpu_s"] / k
    finally:
        r.stop_owner(proc, err)
    return out


def offline_checkpoint(work, store):
    e = env_for(work)
    t = time.perf_counter()
    run = subprocess.run(["/usr/bin/time", "-v", str(IMAGE), "--fn", "store", str(store), "checkpoint"],
                         env=e, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    peak = re.search(rb"Maximum resident set size \(kbytes\): (\d+)", run.stderr)
    usr = re.search(rb"User time \(seconds\): ([0-9.]+)", run.stderr)
    return {"rc": run.returncode, "wall_s": time.perf_counter() - t,
            "peak_kib": int(peak.group(1)) if peak else None,
            "user_s": float(usr.group(1)) if usr else None,
            "stdout": run.stdout.decode("utf-8", "replace")[-300:]}


def open_profiled(work, tag):
    """The CPU window from launch (start pre-written) to LISTENING."""
    d = work / ("sprof-" + tag)
    config = work / "fn.toml"
    port = int(re.search(r"port = (\d+)", config.read_text()).group(1))
    e = env_for(work, sprof=d)
    (d / "start").write_text("1")
    proc, secs, err = start(work, config, e, tag)
    out = {"open_s": secs, "open_line": open_line(work / ("%s.stderr" % tag)),
           "vmhwm_kib_at_listening": r.status_kib(proc.pid, "VmHWM"),
           "owner_cpu_s_at_listening": cpu_s(proc.pid)}
    (d / "stop").write_text("1")
    t = time.perf_counter()
    while not (d / "done").exists() and time.perf_counter() - t < 900:
        time.sleep(0.1)
    return proc, err, port, out


def phase_ckptopen(work):
    out = {"store_checkpoint": offline_checkpoint(work, work / "store")}
    proc, err, port, o = open_profiled(work, "ckptopen")
    out.update(o)
    r.stop_owner(proc, err)
    return out


def wait_checkpoint(path, before, timeout):
    t = time.perf_counter()
    while time.perf_counter() - t < timeout:
        rows = checkpoint_lines(path)
        if len(rows) > before:
            return rows[-1], time.perf_counter() - t
        time.sleep(0.2)
    return None, time.perf_counter() - t


def phase_chain(work, fixture):
    work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    shutil.copytree(Path(fixture) / "store", store, symlinks=True)
    config, port = write_config(work, store)
    out = {"fixture": str(fixture)}
    d = work / "sprof-capture"
    e = env_for(work, sprof=d)
    proc, secs, err = start(work, config, e, "first")
    out["first_open_s"] = secs
    out["first_open_line"] = open_line(work / "first.stderr")
    out["first_vmhwm_kib"] = r.status_kib(proc.pid, "VmHWM")
    try:
        before = len(checkpoint_lines(work / "first.stderr"))
        w = Window(d, proc)
        w.start()
        line, waited = wait_checkpoint(work / "first.stderr", before, 1800)
        out["capture_line"], out["capture_waited_s"] = line, waited
        out["capture_window"] = w.stop()
        out["vmhwm_kib_after_capture"] = r.status_kib(proc.pid, "VmHWM")
    finally:
        r.stop_owner(proc, err)
    proc, err, port, o = open_profiled(work, "reopen")
    out["reopen"] = o
    try:
        out["greeting"] = greetings(port, 32)
        c = m.Conn(port)
        t0 = time.perf_counter()
        reply = c.line("GROUP fn.letters")
        out["group_s"] = time.perf_counter() - t0
        out["group_reply"] = reply.decode("ascii", "replace").strip()
        out["over_2000"] = m.summary([multiline(c, "OVER 1-2000")[0] for _ in range(3)])
        out["over_40"] = m.summary([multiline(c, "OVER %d-%d" % (1 + 997 * i, 40 + 997 * i))[0] for i in range(20)])
        c.close()
    finally:
        r.stop_owner(proc, err)
    return out


def phase_big(work):
    work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    config, port = write_config(work, store)
    d = work / "sprof-article3m"
    e = env_for(work, sprof=d)
    init = [str(IMAGE), "--fn", "operator", str(config), "init", "--max-article-octets", "4194304", "fn.test"]
    ir = subprocess.run(init, env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = {"init_rc": ir.returncode, "init_tail": ir.stdout.decode("ascii", "replace")[-400:]}
    if ir.returncode != 0:
        return out
    proc, out["open_s"], err = start(work, config, e, "big")
    heap = r.Heap(str(work / "heap"), proc)
    try:
        c = m.Conn(port)
        c.line("GROUP fn.test")
        nxt = [0]
        sizes = {"2k": 2048, "32k": 32768, "3m": 3 * 1024 * 1024}
        firsts = {}
        for name, octets in sizes.items():
            firsts[name] = nxt[0] + 1

            def one(_i, octets=octets):
                i = nxt[0]
                nxt[0] += 1
                return r.post(c, i, octets)
            k = 3 if name == "3m" else 10
            c0 = cpu_s(proc.pid)
            out["post_" + name] = bytes_per(heap, "post" + name, one, k)
            out["post_" + name]["owner_cpu_ms_per_op"] = 1000 * (cpu_s(proc.pid) - c0) / k
        c.line("GROUP fn.test")
        for name in sizes:
            k = 3 if name == "3m" else 10
            n0 = firsts[name]
            c0 = cpu_s(proc.pid)
            out["article_" + name] = bytes_per(heap, "art" + name, lambda i: multiline(c, "ARTICLE %d" % (n0 + i % k))[0], k)
            out["article_" + name]["owner_cpu_ms_per_op"] = 1000 * (cpu_s(proc.pid) - c0) / k
        w = Window(d, proc)
        w.start()
        out["article_3m_profiled"] = m.summary([multiline(c, "ARTICLE %d" % (firsts["3m"] + i))[0] for i in range(3)])
        out["window"] = w.stop()
        c.close()
    finally:
        r.stop_owner(proc, err)
    return out


def main():
    phase, work = sys.argv[1], Path(sys.argv[2])
    a = sys.argv[3:]
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    b0 = box()
    if phase == "load":
        out = phase_load(work, int(a[0]), int(a[1]))
    elif phase == "post":
        out = phase_post(work, int(a[0]), a[1])
    elif phase == "reads":
        out = phase_reads(work)
    elif phase == "greet":
        out = phase_greet(work, int(a[0]))
    elif phase == "ckptopen":
        out = phase_ckptopen(work)
    elif phase == "chain":
        out = phase_chain(work, a[0])
    elif phase == "big":
        out = phase_big(work)
    else:
        raise SystemExit("unknown phase " + phase)
    out.update({"phase": phase, "args": a, "started_utc": started,
                "ended_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "box_before": b0, "box_after": box(),
                "image": str(IMAGE), "core_sha256": m.digest(str(IMAGE) + ".core")})
    name = "-".join([phase] + [x for x in a if "/" not in x])
    (work / ("%s.json" % name)).write_text(json.dumps(out, indent=1))
    print(phase, "done", json.dumps({k: v for k, v in out.items() if k not in ("box_before", "box_after")})[:1500])


if __name__ == "__main__":
    main()
