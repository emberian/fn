#!/usr/bin/env python3
"""over-number-index (2026-09-26): OVER and read-by-number timings on hbox.

    python3 measure.py load  TREE IMAGE WORK N        init + N POSTs of 2,048 octets
    python3 measure.py reads TREE IMAGE STORE WORK LABEL
                                                     copy STORE to WORK, open it,
                                                     time the reads, write WORK/LABEL.json

TREE is a tree whose tools/ holds msgid_measure.py and rep_measure.py (the
perf-ledger helpers).  IMAGE is a developer launcher.  Stores live on
/dev/shm; run each command in its own `systemd-run --user --scope -p
MemoryMax=24G`.  Owner CPU is /proc/PID/stat utime+stime over each batch.
The reads are the perf-ledger `reads` phase's (planning/evidence/
perf-ledger-2026-09-26/perf.py) without the profiler: GROUP x5, STAT,
ARTICLE by number, ARTICLE by Message-ID x32, OVER 1 x32, OVER 40 rows x20,
OVER 1-2000 x5; the box state beside every figure.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

TICK = os.sysconf("SC_CLK_TCK")


def cpu_s(pid):
    f = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(f[11]) + int(f[12])) / TICK


def box():
    try:
        units = subprocess.run(["systemctl", "--user", "list-units", "--state=running", "--no-legend",
                                "--plain"], stdout=subprocess.PIPE, text=True, timeout=30).stdout
    except Exception as ex:  # noqa: BLE001
        units = repr(ex)
    return {"utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "loadavg": Path("/proc/loadavg").read_text().strip(),
            "running_user_units": [u.split()[0] for u in units.splitlines() if u.strip()]}


def write_config(m, work, store):
    port = m.free_port()
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, work / "control.sock"), encoding="ascii")
    return config, port


def env():
    e = dict(os.environ)
    e["ACL2_CUSTOMIZATION"] = "NONE"
    e.pop("ACL2_SYSTEM_BOOKS", None)
    return e


def batch(m, pid, fn, k):
    c0 = cpu_s(pid)
    t = [fn(i) for i in range(k)]
    out = m.summary(t)
    out["owner_cpu_ms_per_op"] = 1000 * (cpu_s(pid) - c0) / k
    return out


def load(m, r, image, work, n):
    work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    config, port = write_config(m, work, store)
    ir = subprocess.run([str(image), "--fn", "operator", str(config), "init", "--profile", "default",
                         "fn.test"], env=env(), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = {"init_rc": ir.returncode, "box_before": box()}
    proc, out["first_open_s"], err = r.start_owner(image, config, env(), work / "load.stderr")
    try:
        c = m.Conn(port)
        t = time.perf_counter()
        for i in range(n):
            r.post(c, i, 2048)
        out["load_s"] = time.perf_counter() - t
        c.close()
    finally:
        r.stop_owner(proc, err)
    out["n"], out["box_after"] = n, box()
    return out


def reads(m, r, image, source, work, label):
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    store = work / "store"
    shutil.copytree(source, store)
    config, port = write_config(m, work, store)
    out = {"label": label, "image": str(image), "source": str(source), "box_before": box()}
    proc, out["open_s"], err = r.start_owner(image, config, env(), work / (label + ".stderr"), timeout=3600)
    try:
        c = m.Conn(port)
        g = []
        for _ in range(5):
            t0 = time.perf_counter()
            reply = c.line("GROUP fn.test")
            g.append(time.perf_counter() - t0)
        out["group"] = m.summary(g)
        out["group_reply"] = reply.decode("ascii", "replace").strip()
        low, high = int(reply.split()[2]), int(reply.split()[3])
        nums = [low + (i * (high - low - 40)) // 31 for i in range(32)]
        out["stat"] = batch(m, proc.pid, lambda i: c.timed("STAT %d" % nums[i % 32])[0], 32)
        out["article_by_number"] = batch(m, proc.pid, lambda i: r.timed_multiline(c, "ARTICLE %d" % nums[i % 32])[0], 32)
        ids = [m.msgid(n - low) for n in nums]
        out["article_by_msgid"] = batch(m, proc.pid, lambda i: r.timed_multiline(c, "ARTICLE %s" % ids[i % 32])[0], 32)
        out["over_1"] = batch(m, proc.pid, lambda i: r.timed_multiline(c, "OVER %d" % nums[i % 32])[0], 32)
        out["over_40"] = batch(m, proc.pid, lambda i: r.timed_multiline(c, "OVER %d-%d" % (nums[i % 20], nums[i % 20] + 39))[0], 20)
        rows = {}

        def over2000(_i):
            dt, reply, octets = r.timed_multiline(c, "OVER %d-%d" % (low, low + 1999))
            rows["reply"], rows["octets"] = reply.decode("ascii", "replace").strip(), octets
            return dt
        out["over_2000"] = batch(m, proc.pid, over2000, 5)
        out["over_2000_reply"] = rows
        # The served bytes: SHA-256 of one OVER 1-2000 reply and 32 ARTICLEs by number.
        h = hashlib.sha256()
        c.stream.write(("OVER %d-%d\r\n" % (low, low + 1999)).encode("ascii"))
        while True:
            line = c.readline()
            h.update(line)
            if line == b".\r\n" or not line:
                break
        for n in nums:
            c.stream.write(("ARTICLE %d\r\n" % n).encode("ascii"))
            line = c.readline()
            h.update(line)
            while line[:1] == b"2":
                line = c.readline()
                h.update(line)
                if line == b".\r\n" or not line:
                    break
        out["served_bytes_sha256"] = h.hexdigest()
        c.close()
    finally:
        r.stop_owner(proc, err)
    out["box_after"] = box()
    return out


def main():
    cmd, tree, image = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
    sys.path.insert(0, str(tree / "tools"))
    sys.path.insert(0, str(tree))
    import msgid_measure as m  # noqa: E402
    import rep_measure as r  # noqa: E402
    if cmd == "load":
        work = Path(sys.argv[4])
        out = load(m, r, image, work, int(sys.argv[5]))
        (work / "load.json").write_text(json.dumps(out, indent=1))
    else:
        work = Path(sys.argv[5])
        out = reads(m, r, image, Path(sys.argv[4]), work, sys.argv[6])
        Path(str(work) + "-" + sys.argv[6] + ".json").write_text(json.dumps(out, indent=1))
    print(json.dumps({k: v for k, v in out.items() if not k.startswith("box")}, indent=1))


main()
