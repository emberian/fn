#!/usr/bin/env python3
"""The throughput gate: one matched measurement of a native image on hbox,
a baseline per operation, and the `make check` comparison (PKT-407, PKT-408).

Why: a ~20x commit slowdown reached dev through green merges (2026-09-25);
nothing compared a merged image's throughput with the release's.  Lane
commit-regression then found that half of the "20x" was a tmpfs-to-ZFS
comparison: a per-commit figure names its filesystem.  So every figure here
is taken on tmpfs (/dev/shm), in one unit, on a box checked quiet.

    box     (runs ON hbox, inside the unit `run` starts) for one image:
              quiet  every other running user unit that is transient or
                     fn-named is sampled for CPU over QUIET_WINDOW seconds;
                     one above QUIET_CPU of a core refuses the run (exit 3)
                     and names it.  Idle ones (the live node, idle spike
                     daemons) are recorded, not refused.
              probe  `store STORE probe 1000` through the image's launcher:
                     wall, CPU (user+sys, rusage of the child), the reported
                     commit and reopen seconds.
              alloc  the same probe in-process in the image's core, bracketed
                     by SBCL's get-bytes-consed (commit loop and reopen), a
                     second fresh store; bytes per commit.
              post   100 NNTP POSTs of 2,048 octets on one connection to
                     `operator run` (median, p95; owner CPU per POST), then
              article 100 ARTICLEs of those identifiers on a fresh connection,
              reopen stop and start the owner on that store: seconds to the
                     LISTENING line.
              checkpoint  a development-profile store (K = T = 128): POSTs of
                     31,744 octets (A less 1 KiB for the injected fields)
                     until the owner publishes at K/2 (`CHECKPOINT auto ...
                     ms=N`).
            The box load (loadavg, whole-box CPU busy fraction) is sampled
            every 5 s through the run.  Output: one JSON.
    run     (laptop) ship this script and the client (tools/msgid_measure.py,
            tools/rep_measure.py, tests/native_process.py) to hbox, start the
            box half in `systemd-run --user -p MemoryMax=24G`, wait, fetch the
            JSON into planning/evidence/throughput/REV12-LABEL.json.
    check   (make check) the newest committed run whose revision is HEAD or
            its nearest measured ancestor, against planning/throughput-
            baseline.json: a metric over max(base * 1.25, base + floor)
            fails, unless planning/throughput-causes.json names that
            revision with a reason (the proof_cost pattern).  No run in
            HEAD's ancestry prints NOT MEASURED and passes; a run older than
            a later host/ or books/ change prints STALE and passes (the merge
            batch's run is the NIGHT.md step, not this check).
    baseline  write planning/throughput-baseline.json from the release run
            and the dev-head run, both kept beside each metric; a dev figure
            over the release's limit is printed (it needs a named cause).
            Each metric's value
            is the smaller of the two (a ratchet, as proof_cost's); `check`
            prints IMPROVED for a figure past the tolerance below it.  Refuses
            to raise an existing figure without --allow-regression.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import resource
import shlex
import shutil
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "planning" / "throughput-baseline.json"
CAUSES = ROOT / "planning" / "throughput-causes.json"
RUNS = ROOT / "planning" / "evidence" / "throughput"
TOLERANCE = 0.25
QUIET_WINDOW = 10.0
QUIET_CPU = 0.05
HOST = os.environ.get("FN_HBOX", "hbox")
BOX_ROOT = "/tank/fn/scratch/throughput-gate"
OPENSSL = "/tank/fn/toolchains/openssl-3.5.8"
CLIENT_FILES = ("tools/throughput_gate.py", "tools/msgid_measure.py", "tools/rep_measure.py",
                "tests/__init__.py", "tests/native_process.py")
# Metrics the gate compares (all: lower is better).  The floor is the
# absolute slack: a loopback millisecond figure on a shared box moves by
# more than 25% of itself between repetitions of one image (commit-
# regression's table: POST p95 2.2 to 4.0 ms on one image), so a figure
# fails only past both the tolerance and its floor.  A 2x step fails at
# every floor here.
METRICS = {
    "probe_wall_s": 0.5,
    "probe_cpu_s": 0.5,
    "probe_commit_ms": 0.5,
    "probe_reopen_s": 0.5,
    "probe_bytes_consed_per_commit": 262144,
    "post_median_ms": 1.0,
    "post_p95_ms": 2.0,
    "post_owner_cpu_ms": 1.0,
    "article_median_ms": 1.0,
    "article_p95_ms": 2.0,
    "reopen_s": 0.5,
    "checkpoint_publish_ms": 50.0,
}
# CPU seconds and allocation of the measured process: to first order
# independent of other tenants on a 24-core box that is not saturated.  A run
# taken on a busy box (--under-load) is compared on these only.
LOAD_INSENSITIVE = ("probe_cpu_s", "probe_bytes_consed_per_commit", "post_owner_cpu_ms")


# ---------------------------------------------------------------------------
# The box half.

def unit_rows():
    out = subprocess.run(["systemctl", "--user", "list-units", "--state=running", "--no-legend",
                          "--plain", "--type=service,scope"], stdout=subprocess.PIPE, text=True).stdout
    return [line.split()[0] for line in out.splitlines() if line.strip()]


def unit_show(unit):
    out = subprocess.run(["systemctl", "--user", "show", "-p", "Transient", "-p", "CPUUsageNSec",
                          "-p", "Description", unit], stdout=subprocess.PIPE, text=True).stdout
    row = dict(line.split("=", 1) for line in out.splitlines() if "=" in line)
    try:
        cpu = int(row.get("CPUUsageNSec", ""))
    except ValueError:
        cpu = None
    return row.get("Transient") == "yes", cpu, row.get("Description", "")


def own_unit():
    try:
        for line in Path("/proc/self/cgroup").read_text().splitlines():
            return line.rsplit("/", 1)[-1]
    except OSError:
        return None
    return None


def fn_candidate(unit, transient, description):
    return transient or unit.startswith(("fn-", "qual-", "spike-")) or "/tank/fn/" in description


def quiet_check(window=QUIET_WINDOW, threshold=QUIET_CPU):
    """Every other transient or fn-named running unit, with its CPU fraction
    of one core over WINDOW seconds.  Busy = at or above QUIET_CPU."""
    mine = own_unit()
    first = {}
    for unit in unit_rows():
        if unit == mine:
            continue
        transient, cpu, description = unit_show(unit)
        if fn_candidate(unit, transient, description):
            first[unit] = (cpu, description)
    t0 = time.monotonic()
    time.sleep(window)
    elapsed = time.monotonic() - t0
    busy, idle = [], []
    for unit, (cpu0, description) in sorted(first.items()):
        transient, cpu1, _ = unit_show(unit)
        if cpu0 is None or cpu1 is None:
            frac = None
        else:
            frac = round((cpu1 - cpu0) / 1e9 / elapsed, 3)
        row = {"unit": unit, "cpu_cores": frac, "description": description[:160]}
        (busy if frac is None or frac >= threshold else idle).append(row)
    return {"own_unit": mine, "window_s": window, "threshold_cores": threshold, "busy": busy, "idle": idle}


def cpu_times():
    fields = Path("/proc/stat").read_text().splitlines()[0].split()[1:]
    values = [int(v) for v in fields]
    idle = values[3] + values[4]
    return sum(values), idle


class LoadSampler:
    def __init__(self, interval=5.0):
        self.interval, self.rows, self.stop = interval, [], threading.Event()
        self.thread = threading.Thread(target=self.loop, daemon=True)

    def loop(self):
        total0, idle0 = cpu_times()
        while not self.stop.wait(self.interval):
            total1, idle1 = cpu_times()
            busy = 1.0 - (idle1 - idle0) / max(1, total1 - total0)
            total0, idle0 = total1, idle1
            load1 = float(Path("/proc/loadavg").read_text().split()[0])
            self.rows.append((round(busy, 3), load1))

    def summary(self):
        if not self.rows:
            return {"samples": 0}
        busy = sorted(r[0] for r in self.rows)
        load = sorted(r[1] for r in self.rows)
        return {"samples": len(self.rows), "interval_s": self.interval, "cpus": os.cpu_count(),
                "box_cpu_busy_median": busy[len(busy) // 2], "box_cpu_busy_max": busy[-1],
                "loadavg1_median": load[len(load) // 2], "loadavg1_max": load[-1]}


def write_config(work, port, store):
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, work / "c.sock"), encoding="ascii")
    return config


def init_store(image, config, env, args):
    r = subprocess.run([str(image), "--fn", "operator", str(config), "init"] + args,
                       env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if r.returncode:
        raise SystemExit("init rc=%d: %r" % (r.returncode, r.stdout[-400:]))
    return r.stdout.decode("ascii", "replace")


def child_cpu():
    u = resource.getrusage(resource.RUSAGE_CHILDREN)
    return u.ru_utime + u.ru_stime


def measure_probe(image, work, env, n, out):
    config = write_config(work, 1, work / "store")
    init_store(image, config, env, ["--profile", "scale", "--max-transactions", "1048576",
                                    "--max-article-octets", "2048", "fn.letters", "fn.test"])
    c0, t0 = child_cpu(), time.perf_counter()
    r = subprocess.run([str(image), "--fn", "store", str(work / "store"), "probe", str(n)],
                       env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    wall, cpu = time.perf_counter() - t0, child_cpu() - c0
    tail = r.stdout.decode("ascii", "replace").strip().splitlines()[-1:] or [""]
    out["probe_rc"] = r.returncode
    out["probe_n"] = n
    out["probe_wall_s"] = round(wall, 3)
    out["probe_cpu_s"] = round(cpu, 3)
    try:
        reported = json.loads(tail[0])
    except ValueError:
        out["probe_output"] = tail[0][:400]
        return
    out["probe_reported"] = reported
    if reported.get("status") == "passed":
        out["probe_commit_ms"] = round(1000.0 * reported["commit_seconds"] / n, 3)
        out["probe_reopen_s"] = reported["reopen_seconds"]


ALLOC_LISP = r"""
(in-package "ACL2")
(dolist (f '(fnn-crypto-startup fnn-tls-reset fnn-hsig-reset fnn-hsig-initialize))
  (when (fboundp f) (funcall f)))
(let* ((root (sb-ext:posix-getenv "TG_ROOT"))
       (n (parse-integer (sb-ext:posix-getenv "TG_N")))
       (b0 (sb-ext:get-bytes-consed))
       (condition nil))
  (handler-case (fnn-command-probe root n)
    (serious-condition (e) (setq condition (type-of e))))
  (format t "~&TG-ALLOC n=~d bytes-consed=~d condition=~a~%" n
          (- (sb-ext:get-bytes-consed) b0) condition))
(sb-ext:exit :code 0 :abort t)
"""


def runtime_argv(image):
    """The launcher's sbcl, its runtime options and core, from its exec line."""
    text = Path(image).read_text()
    line = next(l for l in text.splitlines() if l.startswith("exec "))
    words = shlex.split(line.replace("${SBCL_USER_ARGS}", ""))[1:]
    return words[:words.index("--end-runtime-options") + 1]


def measure_alloc(image, work, env, n, out):
    config = write_config(work, 1, work / "store")
    init_store(image, config, env, ["--profile", "scale", "--max-transactions", "1048576",
                                    "--max-article-octets", "2048", "fn.letters", "fn.test"])
    lisp = work / "alloc.lisp"
    lisp.write_text(ALLOC_LISP)
    text = Path(image).read_text()
    home = re.search(r"SBCL_HOME='([^']*)'", text)
    aenv = dict(env, TG_ROOT=str(work / "store"), TG_N=str(n))
    if home:
        aenv["SBCL_HOME"] = home.group(1)
    argv = runtime_argv(image) + ["--no-userinit", "--disable-debugger", "--load", str(lisp)]
    r = subprocess.run(argv, env=aenv, cwd=str(work), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    text = r.stdout.decode("ascii", "replace")
    m = re.search(r"TG-ALLOC n=(\d+) bytes-consed=(\d+) condition=(\S+)", text)
    if not m:
        out["alloc_output"] = text[-400:]
        return
    out["alloc_condition"] = m.group(3)
    # The in-process probe ends by writing its JSON to a stream the bare core
    # leaves unbound (a TYPE-ERROR after the commits and the reopen); any
    # other condition means the loop did not finish, so no figure.
    if m.group(3) in ("NIL", "TYPE-ERROR"):
        out["probe_bytes_consed_per_commit"] = int(m.group(2)) // n


def owner_cpu(pid):
    fields = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")


def measure_served(image, work, env, posts, octets, out):
    import msgid_measure as m
    import rep_measure as r
    port = m.free_port()
    config = write_config(work, port, work / "store")
    init_store(image, config, env, ["--profile", "scale", "--max-transactions", "1048576",
                                    "--max-article-octets", "4096", "fn.letters", "fn.test"])
    proc, _, err = r.start_owner(Path(image), config, env, work / "owner.stderr")
    try:
        c = m.Conn(port)
        c0, t0 = owner_cpu(proc.pid), time.perf_counter()
        times = [r.post(c, i, octets) for i in range(posts)]
        out["post_load_s"] = round(time.perf_counter() - t0, 3)
        out["post_owner_cpu_ms"] = round(1000.0 * (owner_cpu(proc.pid) - c0) / posts, 3)
        c.close()
        s = m.summary(times)
        out["post_n"], out["post_octets"] = posts, len(r.article(0, octets))
        out["post_median_ms"], out["post_p95_ms"] = round(s["median_ms"], 3), round(s["p95_ms"], 3)
        c = m.Conn(port)
        reads = []
        for i in range(posts):
            dt, reply, _ = r.timed_multiline(c, "ARTICLE %s" % m.msgid(i))
            if not reply.startswith(b"220"):
                raise SystemExit("ARTICLE %d: %r" % (i, reply))
            reads.append(dt)
        c.close()
        s = m.summary(reads)
        out["article_n"] = posts
        out["article_median_ms"], out["article_p95_ms"] = round(s["median_ms"], 3), round(s["p95_ms"], 3)
    finally:
        r.stop_owner(proc, err)
    proc, open_s, err = r.start_owner(Path(image), config, env, work / "owner-reopen.stderr")
    try:
        c = m.Conn(port)
        _, reply = c.timed("STAT %s" % m.msgid(posts - 1))
        c.close()
    finally:
        r.stop_owner(proc, err)
    out["reopen_s"] = round(open_s, 3)
    out["reopen_last_stat"] = reply.decode("ascii", "replace").strip()


CHECKPOINT_LINE = re.compile(rb"CHECKPOINT auto sequence=(\d+) suffix=(\d+) octets=(\d+) ms=(\d+)")


def measure_checkpoint(image, work, env, out, deadline=180.0):
    """Development profile (T = K = 128, A = 32,768): POST articles of A less
    1 KiB (the injected fields: Path, Injection-Date, Injection-Info must fit
    under A too) until the owner publishes at K/2."""
    import msgid_measure as m
    import rep_measure as r
    port = m.free_port()
    config = write_config(work, port, work / "store")
    init_store(image, config, env, ["--profile", "development", "fn.letters", "fn.test"])
    octets = 32768 - 1024
    stderr_path = work / "owner.stderr"
    proc, _, err = r.start_owner(Path(image), config, env, stderr_path)
    line, posted = None, 0
    try:
        c = m.Conn(port)
        started = time.perf_counter()
        for i in range(64):
            r.post(c, i, octets)
            posted += 1
            line = CHECKPOINT_LINE.search(stderr_path.read_bytes())
            if line:
                break
        c.close()
        loaded = time.perf_counter()
        # The owner publishes between accepts: open connections until it does.
        while line is None and time.perf_counter() - started < deadline:
            m.Conn(port).close()
            time.sleep(0.25)
            line = CHECKPOINT_LINE.search(stderr_path.read_bytes())
        seen = time.perf_counter()
    finally:
        r.stop_owner(proc, err)
    out["checkpoint_article_octets"] = len(r.article(0, octets))
    out["checkpoint_posts"] = posted
    if line is None:
        out["checkpoint_published"] = False
        return
    out["checkpoint_published"] = True
    out["checkpoint_sequence"], out["checkpoint_suffix"] = int(line.group(1)), int(line.group(2))
    out["checkpoint_octets"], out["checkpoint_publish_ms"] = int(line.group(3)), int(line.group(4))
    out["checkpoint_seen_after_load_s"] = round(seen - loaded, 3)


def box(a):
    sys.path.insert(0, str(ROOT / "tools"))
    sys.path.insert(0, str(ROOT))
    import msgid_measure as m
    image = Path(a.image)
    out = {"schema": 1, "revision": a.revision, "label": a.label, "image": str(image),
           "core_sha256": m.digest(str(image) + ".core"), "launcher_sha256": m.digest(image),
           "client_sha256": {f: m.digest(ROOT / f) for f in CLIENT_FILES if (ROOT / f).is_file()},
           "filesystem": "tmpfs", "host": os.uname().nodename,
           "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    deadline = time.monotonic() + a.wait_quiet
    while True:
        quiet = quiet_check(threshold=a.quiet_cpu)
        if not quiet["busy"] or time.monotonic() >= deadline:
            break
        print("not quiet: %s" % ", ".join(u["unit"] for u in quiet["busy"]), flush=True)
        time.sleep(60)
    out["quiet_before"] = quiet
    out["quiet"] = not quiet["busy"]
    if quiet["busy"] and not a.under_load:
        out["refused"] = "box not quiet: " + ", ".join(
            "%s (%s cores)" % (u["unit"], u["cpu_cores"]) for u in quiet["busy"])
        Path(a.json).write_text(json.dumps(out, indent=2) + "\n")
        print(out["refused"], file=sys.stderr)
        return 3
    if quiet["busy"]:
        print("under load: wall-clock metrics will not be compared", flush=True)
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env["LD_LIBRARY_PATH"] = OPENSSL + "/lib" + (":" + env["LD_LIBRARY_PATH"] if env.get("LD_LIBRARY_PATH") else "")
    base = Path(a.work)
    if base.exists():
        shutil.rmtree(base)
    sampler = LoadSampler()
    sampler.thread.start()
    try:
        for name, fn in (("probe", lambda w: measure_probe(image, w, env, a.probe_n, out)),
                         ("alloc", lambda w: measure_alloc(image, w, env, a.probe_n, out)),
                         ("served", lambda w: measure_served(image, w, env, a.posts, a.octets, out)),
                         ("checkpoint", lambda w: measure_checkpoint(image, w, env, out))):
            w = base / name
            w.mkdir(parents=True)
            t0 = time.perf_counter()
            fn(w)
            out.setdefault("phase_seconds", {})[name] = round(time.perf_counter() - t0, 3)
            shutil.rmtree(w)
            print("phase %s done" % name, flush=True)
    finally:
        sampler.stop.set()
        sampler.thread.join()
        shutil.rmtree(base, ignore_errors=True)
    out["box_load"] = sampler.summary()
    out["quiet_after"] = quiet_check(window=5.0, threshold=a.quiet_cpu)
    out["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    Path(a.json).write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: out.get(k) for k in METRICS}))
    return 0


# ---------------------------------------------------------------------------
# The laptop half.

def ssh(cmd, **kw):
    return subprocess.run(["ssh", "-n", HOST, cmd], **kw)


def run(a):
    rev = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--verify", a.revision + "^{commit}"],
                         stdout=subprocess.PIPE, text=True, check=True).stdout.strip()
    label = a.label
    if not re.fullmatch(r"[A-Za-z0-9._-]+", label):
        raise SystemExit("bad --label")
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    remote = "%s/run-%s-%s" % (BOX_ROOT, rev[:12], stamp)
    unit = "throughput-gate-%s-%s" % (rev[:12], stamp)
    if ssh("test -x %s" % shlex.quote(a.image)).returncode:
        raise SystemExit("no image %s on %s" % (a.image, HOST))
    ssh("mkdir -p %s/client/tools %s/client/tests" % (remote, remote), check=True)
    subprocess.run(["rsync", "-a", "--relative"] + ["./" + f for f in CLIENT_FILES]
                   + ["%s:%s/client/" % (HOST, remote)], cwd=str(ROOT), check=True)
    work = "/dev/shm/throughput-gate/%s" % stamp
    box_cmd = ("python3 %s/client/tools/throughput_gate.py box --image %s --revision %s --label %s "
               "--work %s --json %s/result.json --wait-quiet %d%s > %s/box.log 2>&1; echo $? > %s/status"
               % (remote, shlex.quote(a.image), rev, label, work, remote, a.wait_quiet,
                  " --under-load" if a.under_load else "", remote, remote))
    ssh("systemd-run --user --quiet --collect --unit=%s --slice=swarm.slice -p MemoryMax=24G "
        "-p MemorySwapMax=0 sh -c %s" % (unit, shlex.quote(box_cmd)), check=True)
    print("started %s on %s; %s" % (unit, HOST, remote), flush=True)
    waited = subprocess.run([str(ROOT / "tools" / "wait_for.sh"), "--host", HOST, "--deadline",
                             str(a.deadline), "--interval", "20", "--file", remote + "/status"],
                            stdout=subprocess.DEVNULL).returncode
    if waited:
        print("no status within %ss (wait_for %d); still running in %s" % (a.deadline, waited, remote))
        return 124
    status = ssh("cat %s/status; tail -n 5 %s/box.log" % (remote, remote), stdout=subprocess.PIPE,
                 text=True).stdout
    print(status)
    RUNS.mkdir(parents=True, exist_ok=True)
    dest = RUNS / ("%s-%s-%s.json" % (rev[:12], label, stamp))
    fetched = subprocess.run(["scp", "-q", "%s:%s/result.json" % (HOST, remote), str(dest)]).returncode
    if fetched == 0:
        print("wrote %s" % dest.relative_to(ROOT))
    return int(status.split()[0]) if status.split() else 1


# ---------------------------------------------------------------------------
# The check.

def load_json(path, default=None):
    if not path.is_file():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def git(*args):
    return subprocess.run(["git", "-C", str(ROOT)] + list(args), stdout=subprocess.PIPE,
                          stderr=subprocess.DEVNULL, text=True)


def limit(base, floor):
    return max(base * (1 + TOLERANCE), base + floor)


def compared(run_doc, baseline):
    names = list(baseline.get("metrics", {}))
    if run_doc.get("quiet") is False:
        names = [n for n in names if n in LOAD_INSENSITIVE]
    return names


def compare(run_doc, baseline):
    """The failing metrics of RUN_DOC: (metric, value, base, limit)."""
    failures = []
    for metric in compared(run_doc, baseline):
        row = baseline["metrics"][metric]
        value = run_doc.get(metric)
        if value is None:
            failures.append((metric, None, row["value"], None))
            continue
        bound = limit(row["value"], row.get("floor", METRICS.get(metric, 0)))
        if value > bound:
            failures.append((metric, value, row["value"], bound))
    return failures


def newest_run(head):
    """The run whose revision is HEAD or HEAD's nearest measured ancestor; the
    newest file of that revision."""
    runs = []
    for path in sorted(RUNS.glob("*.json")):
        doc = load_json(path)
        if not isinstance(doc, dict) or doc.get("refused") or not doc.get("revision"):
            continue
        if doc.get("quiet_before", {}).get("threshold_cores") != QUIET_CPU:
            continue
        runs.append((path, doc))
    best = None
    for path, doc in runs:
        rev = doc["revision"]
        if git("merge-base", "--is-ancestor", rev, head).returncode != 0:
            continue
        distance = int(git("rev-list", "--count", "%s..%s" % (rev, head)).stdout.strip() or 10 ** 9)
        key = (-distance, doc.get("quiet") is not False, doc.get("finished_utc", ""))
        if best is None or key > best[0]:
            best = (key, path, doc)
    return best


def check(a):
    baseline = load_json(BASELINE)
    if baseline is None:
        print("throughput_gate: no %s" % BASELINE.relative_to(ROOT))
        return 1
    causes = load_json(CAUSES, {"causes": []}).get("causes", [])
    head = git("rev-parse", "HEAD").stdout.strip()
    if not head:
        print("throughput_gate: not a git checkout; NOT MEASURED")
        return 0
    found = newest_run(head)
    if found is None:
        print("throughput_gate: NOT MEASURED: no run under planning/evidence/throughput/ "
              "is HEAD or its ancestor")
        return 0
    (negative, _, _), path, doc = found
    distance = -negative
    rev = doc["revision"]
    changed = git("diff", "--name-only", rev, head, "--", "host", "books").stdout.split()
    scope = "at HEAD" if distance == 0 else "%d commits before HEAD" % distance
    failures = compare(doc, baseline)
    named = [c for c in causes if len(c.get("revision", "")) >= 7 and c.get("reason")
             and (rev.startswith(c["revision"]) or c["revision"].startswith(rev[:12]))]
    for metric, value, base, bound in failures:
        if value is None:
            print("throughput_gate: MISSING %s in %s" % (metric, path.name))
        else:
            print("throughput_gate: REGRESSION %s %.3f > %.3f (baseline %.3f) in %s"
                  % (metric, value, bound, base, path.name))
    for metric in compared(doc, baseline):
        row, value = baseline["metrics"][metric], doc.get(metric)
        floor = row.get("floor", METRICS.get(metric, 0))
        if value is not None and value * (1 + TOLERANCE) < row["value"] and row["value"] - value > floor:
            print("throughput_gate: IMPROVED %s %.3f against %.3f: lower the baseline "
                  "(tools/throughput_gate.py baseline)" % (metric, value, row["value"]))
    if changed:
        print("throughput_gate: STALE: %s measures %s (%s); %d host/books files changed since"
              % (path.name, rev[:12], scope, len(changed)))
    load = doc.get("box_load", {})
    names = compared(doc, baseline)
    busy = doc.get("quiet_before", {}).get("busy", [])
    print("throughput_gate: %s measures %s (%s), %d of %d metrics compared%s, box cpu busy median %s"
          % (path.name, rev[:12], scope, len(names), len(baseline.get("metrics", {})),
             "" if doc.get("quiet") is not False else
             " (under load: %s busy; wall-clock figures not compared)" % ", ".join(u["unit"] for u in busy),
             load.get("box_cpu_busy_median")))
    if failures and named:
        print("throughput_gate: named cause for %s: %s" % (rev[:12], named[0].get("reason")))
        return 0
    if failures:
        print("throughput_gate: FAIL: name the cause in planning/throughput-causes.json "
              "({\"revision\": \"%s\", \"reason\": ...}) or fix it" % rev[:12])
        return 1
    return 0


def write_baseline(a):
    release, dev = load_json(Path(a.release)), load_json(Path(a.dev))
    old = load_json(BASELINE, {"metrics": {}})
    metrics, raised = {}, []
    for metric, floor in METRICS.items():
        values = [d.get(metric) for d in (release, dev)]
        if any(v is None for v in values):
            raise SystemExit("%s missing from a run" % metric)
        value = min(values)
        prior = old.get("metrics", {}).get(metric, {}).get("value")
        if prior is not None and value > prior and not a.allow_regression:
            raised.append(metric)
        metrics[metric] = {"value": value, "floor": floor, "release": values[0], "dev": values[1]}
    if raised:
        raise SystemExit("would raise %s; rerun with --allow-regression and name the cause" % ", ".join(raised))
    for metric, row in metrics.items():
        if row["dev"] > limit(row["value"], row["floor"]):
            print("dev %s: %s %s over the release's %s (limit %.3f): name it in %s"
                  % (dev["revision"][:12], metric, row["dev"], row["value"],
                     limit(row["value"], row["floor"]), CAUSES.relative_to(ROOT)))
    doc = {
        "about": ("Throughput per operation of a native developer image on hbox, tmpfs, one "
                  "unit (tools/throughput_gate.py); quiet says whether each source run had "
                  "the box to itself. A run fails a metric above "
                  "max(value * (1 + tolerance), value + floor). value is the smaller of the "
                  "qualified release's and dev's figure (a ratchet: an improvement lowers it "
                  "at the next write); both are kept beside it, and a dev figure over the "
                  "release's limit needs a row in planning/throughput-causes.json."),
        "tolerance": TOLERANCE,
        "release": {"revision": release["revision"], "run": Path(a.release).name,
                    "core_sha256": release["core_sha256"], "quiet": release.get("quiet")},
        "dev": {"revision": dev["revision"], "run": Path(a.dev).name, "core_sha256": dev["core_sha256"],
                "quiet": dev.get("quiet")},
        "metrics": metrics,
    }
    BASELINE.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    print("wrote %s" % BASELINE.relative_to(ROOT))
    return 0


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd")
    b = sub.add_parser("box")
    b.add_argument("--image", required=True)
    b.add_argument("--revision", required=True)
    b.add_argument("--label", required=True)
    b.add_argument("--work", required=True)
    b.add_argument("--json", required=True)
    b.add_argument("--probe-n", type=int, default=1000)
    b.add_argument("--posts", type=int, default=100)
    b.add_argument("--octets", type=int, default=2048)
    b.add_argument("--wait-quiet", type=int, default=0, help="seconds to wait for a quiet box before refusing")
    b.add_argument("--under-load", action="store_true",
                   help="measure on a busy box anyway; the check then compares only " + ", ".join(LOAD_INSENSITIVE))
    b.add_argument("--quiet-cpu", type=float, default=QUIET_CPU,
                   help="busy threshold in cores; a run above the default is a smoke run the check ignores")
    r = sub.add_parser("run")
    r.add_argument("--image", required=True, help="the developer launcher on hbox")
    r.add_argument("--revision", required=True, help="the commit the image was built from")
    r.add_argument("--label", required=True)
    r.add_argument("--wait-quiet", type=int, default=1800)
    r.add_argument("--under-load", action="store_true")
    r.add_argument("--deadline", type=int, default=3300)
    sub.add_parser("check")
    w = sub.add_parser("baseline")
    w.add_argument("--release", required=True)
    w.add_argument("--dev", required=True)
    w.add_argument("--allow-regression", action="store_true")
    a = p.parse_args(argv)
    if a.cmd == "box":
        return box(a)
    if a.cmd == "run":
        return run(a)
    if a.cmd == "baseline":
        return write_baseline(a)
    return check(a)


if __name__ == "__main__":
    sys.exit(main())
