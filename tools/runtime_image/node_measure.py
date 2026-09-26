#!/usr/bin/env python3
"""Resident size, start time, smallest working heap and a served transcript
of one native image (lane runtime-image, 2026-09-26).  Runs ON hbox (or any
Linux box with /proc), from a tree that has tools/rep_measure.py and
tools/msgid_measure.py.  A measurement only: it decides nothing a node does.

    node_measure.py run IMAGE WORK --posts N [--heap MB] [--transcript FILE]
        fresh scale-profile store (A = 4,096, as the throughput gate's); the owner under SBCL_USER_ARGS
        --dynamic-space-size MB; seconds to LISTENING; VmRSS/VmHWM at start,
        after one POST, after N POSTs of 2,048 octets; then a fixed command
        list whose reply octets (every line, verbatim) go to FILE.
    node_measure.py floor IMAGE WORK [--lo MB --hi MB]
        the smallest --dynamic-space-size (MB) at which a fresh store starts,
        takes one POST (240) and serves it back (220); bisection to 8 MB.
    node_measure.py core IMAGE
        the runtime's own figure: "dynamic space too small for core: N KiB".
    node_measure.py checkpoint IMAGE WORK [--heap MB]
        (lane image-floor) a fresh development-profile store: POSTs of 2,048
        octets until the owner logs `CHECKPOINT auto'; VmRSS/VmHWM after the
        publication; then stop, start again on that store (the reopen):
        seconds to LISTENING and VmRSS after it.
    node_measure.py reopen-floor IMAGE WORK [--lo MB --hi MB]
        (lane image-floor) the smallest heap at which the owner reopens the
        store a `run' left in WORK and serves its first article.
`run' also stops the owner after the POSTs and starts it again on the same
store: reopen seconds and VmRSS after the reopen, and per-POST median/p95 ms.
Output: one JSON line on stdout.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import msgid_measure as m  # noqa: E402
import rep_measure as r    # noqa: E402

OCTETS = 2048


def env_for(heap):
    env = dict(os.environ)
    if heap:
        env["SBCL_USER_ARGS"] = "--dynamic-space-size %dMB" % heap
    return env


DEVELOPMENT = ["--profile", "development"]
SCALE = ["--profile", "scale", "--max-transactions", "1048576", "--max-article-octets", "4096"]


def fresh(image, work, env, profile=DEVELOPMENT):
    work.mkdir(parents=True, exist_ok=True)
    for p in ("store", "c.sock"):
        subprocess.run(["rm", "-rf", str(work / p)], check=True)
    port = m.free_port()
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (work / "store", port, work / "c.sock"),
                      encoding="ascii")
    res = subprocess.run([str(image), "--fn", "operator", str(config), "init"] + profile
                         + ["fn.letters", "fn.test"], env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if res.returncode:
        raise RuntimeError("init rc=%d %r" % (res.returncode, res.stdout[-300:]))
    return config, port


def rss(pid):
    if os.path.exists("/proc/%d/status" % pid):
        return {"rss_kib": r.status_kib(pid, "VmRSS"), "hwm_kib": r.status_kib(pid, "VmHWM")}
    # OpenBSD (no /proc): ps(1)'s resident set in KiB; no high-water mark.
    out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], stdout=subprocess.PIPE,
                         check=True).stdout
    return {"rss_kib": int(out.split()[0]), "hwm_kib": None}


def multiline(c, out):
    while True:
        line = c.readline()
        if not line:
            raise RuntimeError("closed in a multi-line reply")
        out.append(line)
        if line == b".\r\n":
            return


def transcript(port, posts):
    out = []
    c = m.Conn(port)
    out.append(c.greeting)
    cmds = ["CAPABILITIES", "MODE READER", "LIST", "LIST ACTIVE fn.*", "LIST NEWSGROUPS",
            "LIST OVERVIEW.FMT", "GROUP fn.test", "LISTGROUP fn.test", "OVER 1-%d" % posts,
            "HDR Subject 1-%d" % posts, "STAT 1", "NEXT", "LAST", "HEAD 1", "BODY 2"]
    cmds += ["ARTICLE %s" % m.msgid(i) for i in range(posts)]
    cmds += ["ARTICLE <absent@example.invalid>", "STAT %s" % m.msgid(posts - 1),
             "GROUP fn.absent", "XYZZY", "HELP"]
    for cmd in cmds:
        out.append(b"C: " + cmd.encode("ascii") + b"\r\n")
        line = c.line(cmd)
        out.append(line)
        head = line[:3]
        if head in (b"215", b"220", b"221", b"222", b"224", b"225", b"101", b"100", b"230",
                    b"231") or (cmd.startswith("LISTGROUP") and head == b"211"):
            multiline(c, out)
    out.append(b"C: QUIT\r\n")
    out.append(c.line("QUIT"))
    return b"".join(out)


def run(a):
    image, work = Path(a.image), Path(a.work)
    env = env_for(a.heap)
    config, port = fresh(image, work, env, SCALE)
    doc = {"image": str(image), "heap_mb": a.heap, "posts": a.posts, "profile": "scale"}
    proc, start_s, err = r.start_owner(image, config, env, work / "owner.stderr", timeout=600)
    try:
        doc["start_s"] = round(start_s, 3)
        time.sleep(1.0)
        doc["start"] = rss(proc.pid)
        c = m.Conn(port)
        r.post(c, 0, OCTETS)
        doc["after_1"] = rss(proc.pid)
        t0 = time.perf_counter()
        times = []
        for i in range(1, a.posts):
            t1 = time.perf_counter()
            r.post(c, i, OCTETS)
            times.append(time.perf_counter() - t1)
            if i + 1 in (100, 1000, 10000):
                doc["after_%d" % (i + 1)] = rss(proc.pid)
        doc["post_s"] = round(time.perf_counter() - t0, 3)
        doc["post_ms"] = latency(times)
        c.close()
        if a.transcript:
            data = transcript(port, min(a.posts, 20))
            Path(a.transcript).write_bytes(data)
            doc["transcript_octets"] = len(data)
        doc["end"] = rss(proc.pid)
    finally:
        r.stop_owner(proc, err)
    doc["owner_rc"] = proc.returncode
    proc, doc["reopen_s"], err = r.start_owner(image, config, env, work / "owner.stderr",
                                               timeout=600)
    try:
        doc["reopen_s"] = round(doc["reopen_s"], 3)
        time.sleep(1.0)
        doc["after_reopen"] = rss(proc.pid)
    finally:
        r.stop_owner(proc, err)
    return doc


def latency(times):
    if not times:
        return None
    t = sorted(times)
    return {"median": round(1000 * t[len(t) // 2], 3),
            "p95": round(1000 * t[min(len(t) - 1, int(len(t) * 0.95))], 3)}


def checkpoint(a):
    """POST until the owner publishes a checkpoint; then the reopen."""
    image, work = Path(a.image), Path(a.work)
    env = env_for(a.heap)
    config, port = fresh(image, work, env)
    log = work / "owner.stderr"
    if log.exists():
        log.unlink()
    doc = {"image": str(image), "heap_mb": a.heap, "profile": "development"}
    proc, start_s, err = r.start_owner(image, config, env, log, timeout=600)
    try:
        doc["start_s"] = round(start_s, 3)
        c = m.Conn(port)
        line = None
        for i in range(a.max_posts):
            r.post(c, i, OCTETS)
            err.flush()
            line = next((l for l in log.read_text(errors="replace").splitlines()
                         if "CHECKPOINT auto " in l), None)
            if line:
                doc["posts"] = i + 1
                break
        c.close()
        if not line:
            raise RuntimeError("no CHECKPOINT auto after %d posts" % a.max_posts)
        doc["checkpoint_line"] = line.strip()
        time.sleep(1.0)
        doc["after_publication"] = rss(proc.pid)
    finally:
        r.stop_owner(proc, err)
    proc, reopen_s, err = r.start_owner(image, config, env, log, timeout=600)
    try:
        doc["reopen_s"] = round(reopen_s, 3)
        time.sleep(1.0)
        doc["after_reopen"] = rss(proc.pid)
    finally:
        r.stop_owner(proc, err)
    return doc


def trial(image, work, heap):
    env = env_for(heap)
    try:
        config, port = fresh(image, work, env)
    except RuntimeError as e:
        return False, "init: %s" % str(e)[:200]
    try:
        proc, _, err = r.start_owner(image, config, env, work / "owner.stderr", timeout=120)
    except BaseException as e:  # the owner died before LISTENING
        return False, "start: %s" % str(e)[:200]
    try:
        c = m.Conn(port)
        r.post(c, 0, OCTETS)
        c.close()
        c = m.Conn(port)
        _, reply, _ = r.timed_multiline(c, "ARTICLE %s" % m.msgid(0))
        c.close()
        ok = reply.startswith(b"220")
        return ok, reply[:40].decode("ascii", "replace").strip()
    except BaseException as e:
        return False, "session: %s" % str(e)[:200]
    finally:
        try:
            r.stop_owner(proc, err)
        except BaseException:
            pass


def floor(a):
    image, work = Path(a.image), Path(a.work)
    lo, hi = a.lo, a.hi
    rows = []
    ok, why = trial(image, work, hi)
    rows.append([hi, ok, why])
    if not ok:
        return {"image": str(image), "floor_mb": None, "trials": rows}
    while hi - lo > 8:
        mid = (lo + hi) // 2
        ok, why = trial(image, work, mid)
        rows.append([mid, ok, why])
        if ok:
            hi = mid
        else:
            lo = mid
    return {"image": str(image), "floor_mb": hi, "failed_at_mb": lo, "trials": rows}


def reopen_floor(a):
    """The smallest heap at which the owner reopens the store `run' left in
    WORK (its fn.toml) and serves its first article back; bisection to 8 MB."""
    image, work = Path(a.image), Path(a.work)
    config = work / "fn.toml"
    port = int(re.search(r"port = (\d+)", config.read_text()).group(1))

    def attempt(heap):
        env = env_for(heap)
        try:
            proc, secs, err = r.start_owner(image, config, env, work / "reopen.stderr",
                                            timeout=600)
        except BaseException as e:
            return False, "start: %s" % str(e)[:120]
        try:
            c = m.Conn(port)
            _, reply, _ = r.timed_multiline(c, "ARTICLE %s" % m.msgid(0))
            c.close()
            return reply.startswith(b"220"), "%.3f s %s" % (secs, reply[:12])
        except BaseException as e:
            return False, "session: %s" % str(e)[:120]
        finally:
            try:
                r.stop_owner(proc, err)
            except BaseException:
                pass

    lo, hi = a.lo, a.hi
    rows = []
    ok, why = attempt(hi)
    rows.append([hi, ok, why])
    if not ok:
        return {"image": str(image), "reopen_floor_mb": None, "trials": rows}
    while hi - lo > 8:
        mid = (lo + hi) // 2
        ok, why = attempt(mid)
        rows.append([mid, ok, why])
        if ok:
            hi = mid
        else:
            lo = mid
    return {"image": str(image), "reopen_floor_mb": hi, "failed_at_mb": lo, "trials": rows}


def core(a):
    text = Path(a.image).read_text()
    line = next(l for l in text.splitlines() if l.startswith("exec "))
    words = shlex.split(line.replace("${SBCL_USER_ARGS}", "--dynamic-space-size 8MB"))[1:]
    home = re.search(r"SBCL_HOME='([^']*)'", text)
    env = dict(os.environ)
    if home:
        env["SBCL_HOME"] = home.group(1)
    res = subprocess.run(words, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, timeout=60)
    out = res.stdout.decode("ascii", "replace")
    got = re.search(r"(\d+)KiB required", out)
    core_path = words[words.index("--core") + 1]
    return {"image": a.image, "core_required_kib": int(got.group(1)) if got else None,
            "core_file_octets": os.path.getsize(core_path), "said": out.strip()[-200:]}


def counts(path):
    table = {}
    for line in Path(path).read_text().splitlines():
        k, v = line.rsplit(" ", 1)
        table[k] = int(v)
    return table


def delta(after, before):
    return {k: v - before.get(k, 0) for k, v in sorted(after.items()) if v - before.get(k, 0)}


def probe(a):
    """The world-access and *1* counts of the POST and ARTICLE paths."""
    image, work = Path(a.image), Path(a.work)
    env = env_for(1024)
    config, port = fresh(image, work, env, SCALE)
    text = image.read_text()
    line = next(l for l in text.splitlines() if l.startswith("exec "))
    words = shlex.split(line.replace("${SBCL_USER_ARGS}", ""))[1:]
    runtime = words[:words.index("--end-runtime-options") + 1]
    home = re.search(r"SBCL_HOME='([^']*)'", text)
    if home:
        env["SBCL_HOME"] = home.group(1)
    out = work / "probe-counts.txt"
    env["RI_PROBE_OUT"] = str(out)
    lisp = Path(__file__).resolve().parent / "world-probe.lisp"
    argv = runtime + ["--no-userinit", "--load", str(lisp), "--eval", "(acl2::sbcl-restart)",
                      "--disable-debugger", "--end-toplevel-options",
                      "--fn", "operator", str(config), "run"]
    err = open(work / "probe.stderr", "ab")
    proc = subprocess.Popen(argv, env=env, stdout=subprocess.PIPE, stderr=err)
    doc = {"image": str(image), "posts": a.posts}
    try:
        r.wait_for_announcement(proc, b"LISTENING ", timeout=600)
        time.sleep(2.5)
        base = counts(out)
        c = m.Conn(port)
        for i in range(a.posts):
            r.post(c, i, OCTETS)
        c.close()
        time.sleep(2.5)
        posted = counts(out)
        c = m.Conn(port)
        for i in range(a.posts):
            _, reply, _ = r.timed_multiline(c, "ARTICLE %s" % m.msgid(i))
            if not reply.startswith(b"220"):
                raise RuntimeError("ARTICLE %d: %r" % (i, reply))
        c.close()
        time.sleep(2.5)
        read = counts(out)
        doc["start"] = base
        doc["post"] = delta(posted, base)
        doc["article"] = delta(read, posted)
    finally:
        r.stop_owner(proc, err)
    return doc


def main():
    import argparse
    p = argparse.ArgumentParser()
    s = p.add_subparsers(dest="cmd", required=True)
    q = s.add_parser("run")
    q.add_argument("image"); q.add_argument("work")
    q.add_argument("--posts", type=int, default=100)
    q.add_argument("--heap", type=int, default=1024)
    q.add_argument("--transcript")
    q = s.add_parser("floor")
    q.add_argument("image"); q.add_argument("work")
    q.add_argument("--lo", type=int, default=32)
    q.add_argument("--hi", type=int, default=1024)
    q = s.add_parser("probe")
    q.add_argument("image"); q.add_argument("work")
    q.add_argument("--posts", type=int, default=100)
    q = s.add_parser("core")
    q.add_argument("image")
    q = s.add_parser("reopen-floor")
    q.add_argument("image"); q.add_argument("work")
    q.add_argument("--lo", type=int, default=128)
    q.add_argument("--hi", type=int, default=1024)
    q = s.add_parser("checkpoint")
    q.add_argument("image"); q.add_argument("work")
    q.add_argument("--heap", type=int, default=1024)
    q.add_argument("--max-posts", type=int, default=200)
    a = p.parse_args()
    doc = {"run": run, "floor": floor, "core": core, "probe": probe,
           "checkpoint": checkpoint, "reopen-floor": reopen_floor}[a.cmd](a)
    print(json.dumps(doc, sort_keys=True))


if __name__ == "__main__":
    main()
