#!/usr/bin/env python3
"""post-identity-index (2026-09-26): a POST's owner CPU and bytes consed.

    python3 postmeasure.py load IMAGE WORK N
        init (default profile, group fn.test) and N POSTs of 2,048 octets
    python3 postmeasure.py post IMAGE SRC WORK LABEL K [cpu]
        copy the store SRC to WORK/store, open it with IMAGE, one warm-up
        POST, then K POSTs of 2,048 octets between two heap readings: bytes
        consed per POST (the heap hook) and owner CPU per POST
        (/proc/PID/stat utime+stime over the K); with `cpu`, an sb-sprof
        :cpu window over the same K.  Writes WORK/LABEL.json.

Run from a tree whose tools/ holds msgid_measure.py and rep_measure.py (the
perf-ledger helpers), each command in its own systemd-run --user --scope
with MemoryMax.  IMAGE is a developer launcher: the perf-ledger's profiling
twin is not needed.  The launcher is copied to WORK/launcher with
`--load heap.lisp --load sprof.lisp` (this directory's) put before its
`--eval '(acl2::sbcl-restart)'`, so the same core runs with the perf-ledger's
heap hook (FN_HEAP_DIR) and a CPU window (FN_SPROF_DIR).  The box state is
recorded beside every figure.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path.cwd()
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "tools"))
import msgid_measure as m  # noqa: E402
import rep_measure as r  # noqa: E402

TICK = os.sysconf("SC_CLK_TCK")
RESTART = "--eval '(acl2::sbcl-restart)'"


def cpu_s(pid):
    f = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(f[11]) + int(f[12])) / TICK


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def box():
    try:
        units = subprocess.run(["systemctl", "--user", "list-units", "--state=running", "--no-legend",
                                "--plain"], stdout=subprocess.PIPE, text=True, timeout=30).stdout
    except Exception as ex:  # noqa: BLE001
        units = repr(ex)
    return {"loadavg": Path("/proc/loadavg").read_text().strip(),
            "running_user_units": [u.split()[0] for u in units.splitlines() if u.strip()]}


def wrap(image, work):
    text = Path(image).read_text()
    if RESTART not in text:
        raise SystemExit("launcher has no %s" % RESTART)
    loads = "--load '%s' --load '%s' " % (HERE / "heap.lisp", HERE / "sprof.lisp")
    out = work / "launcher"
    out.write_text(text.replace(RESTART, loads + RESTART))
    out.chmod(0o755)
    return out


def write_config(work, store):
    port = m.free_port()
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, work / "control.sock"), encoding="ascii")
    return config, port


def env_for(work, sprof=None):
    e = dict(os.environ)
    e["ACL2_CUSTOMIZATION"] = "NONE"
    e.pop("ACL2_SYSTEM_BOOKS", None)
    e["FN_HEAP_DIR"] = str(work / "heap")
    (work / "heap").mkdir(parents=True, exist_ok=True)
    if sprof is not None:
        shutil.rmtree(sprof, ignore_errors=True)
        sprof.mkdir(parents=True)
        e["FN_SPROF_DIR"] = str(sprof)
    return e


def phase_load(image, work, n):
    work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    config, port = write_config(work, store)
    e = env_for(work)
    init = [str(image), "--fn", "operator", str(config), "init", "--profile", "default", "fn.test"]
    ir = subprocess.run(init, env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = {"init_rc": ir.returncode, "init_tail": ir.stdout.decode("ascii", "replace")[-300:]}
    proc, out["first_open_s"], err = r.start_owner(image, config, e, work / "load.stderr")
    try:
        c = m.Conn(port)
        t = time.perf_counter()
        load = [r.post(c, i, 2048) for i in range(n)]
        out["load_s"] = time.perf_counter() - t
        c.close()
        q = max(1, n // 4)
        out["post_first_quarter"] = m.summary(load[:q])
        out["post_last_quarter"] = m.summary(load[-q:])
    finally:
        r.stop_owner(proc, err)
    out["n"] = n
    return out


def phase_post(image, src, work, k, cpu):
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    store = work / "store"
    shutil.copytree(src, store, symlinks=True)
    config, port = write_config(work, store)
    launcher = wrap(image, work)
    d = work / "sprof" if cpu else None
    e = env_for(work, d)
    t = time.perf_counter()
    proc, secs, err = r.start_owner(launcher, config, e, work / "post.stderr")
    out = {"open_s": secs}
    heap = r.Heap(str(work / "heap"), proc)
    try:
        c = m.Conn(port)
        r.post(c, 899999, 2048)
        h0 = heap.snap("p0")
        c0 = cpu_s(proc.pid)
        if cpu:
            (d / "start").write_text("1")
            time.sleep(0.2)
        t0 = time.perf_counter()
        times = [r.post(c, 900000 + i, 2048) for i in range(k)]
        wall = time.perf_counter() - t0
        if cpu:
            (d / "stop").write_text("1")
        c1 = cpu_s(proc.pid)
        h1 = heap.snap("p1")
        out["post"] = m.summary(times)
        out["window_wall_s"] = wall
        out["owner_cpu_ms_per_post"] = 1000.0 * (c1 - c0) / k
        out["bytes_consed_per_post"] = (h1["bytes_consed"] - h0["bytes_consed"]) / float(k)
        c.close()
        if cpu:
            started = time.perf_counter()
            while not (d / "done").exists() and time.perf_counter() - started < 900:
                time.sleep(0.1)
            out["sprof_error"] = (d / "error.txt").read_text() if (d / "error.txt").exists() else None
    finally:
        r.stop_owner(proc, err)
    out["k"] = k
    out["store_src"] = str(src)
    return out


def main():
    phase, image = sys.argv[1], Path(sys.argv[2])
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    b0 = box()
    if phase == "load":
        work = Path(sys.argv[3])
        out = phase_load(image, work, int(sys.argv[4]))
        name = work / "load.json"
    elif phase == "post":
        src, work, label, k = Path(sys.argv[3]), Path(sys.argv[4]), sys.argv[5], int(sys.argv[6])
        out = phase_post(image, src, work, k, len(sys.argv) > 7 and sys.argv[7] == "cpu")
        out["label"] = label
        name = work.parent / ("%s.json" % label)
    else:
        raise SystemExit("unknown phase " + phase)
    out.update({"phase": phase, "started_utc": started,
                "ended_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "box_before": b0, "box_after": box(),
                "image": str(image), "core_sha256": digest(str(image) + ".core")})
    name.write_text(json.dumps(out, indent=1))
    print(phase, "done", json.dumps({k: v for k, v in out.items()
                                     if k not in ("box_before", "box_after")})[:1500])


if __name__ == "__main__":
    main()
