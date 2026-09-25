#!/usr/bin/env python3
"""Representation measurement on a native image (the megaspike, D27/D28).

One scratch store, one `operator run` of the named image on a kernel port.
N articles of about L octets are posted through one NNTP reader connection
(POST wall per article, first and last quarter); the owner's VmRSS is read
after the load and, when the image carries the rep-heap census hook and
`--census` is given, the live dynamic space after a full GC.  Then, on a
fresh reader connection, `STAT <id>`, `ARTICLE <id>` (the whole multi-line
reply) and `OVER n` (after `GROUP`) are timed for K identifiers spread over
the store.  Then the owner is stopped and started again on the same store:
the time to its LISTENING line is the owner's load time at N (full-history
recovery), and its VmRSS after that is read.  Every timing is a command
written and its reply read on an open socket; it includes the loopback
round trip and the owner's whole read.

    python3 tools/rep_measure.py --image build/fn-host-developer \\
        --work /tank/fn/scratch/spike-representation/n120-2k --articles 120 \\
        --octets 2048 --samples 16 --json out.json
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
import msgid_measure as m  # noqa: E402
from tests.native_process import wait_for_announcement  # noqa: E402

LINE = ("x" * 76 + "\r\n").encode("ascii")


def article(i, octets):
    if octets == 0:
        return m.article(i)
    head = ("From: t17@example.invalid\r\nNewsgroups: fn.test\r\nSubject: t17 %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n"
            % (i, m.msgid(i))).encode("ascii")
    body = ("body %d\r\n" % i).encode("ascii")
    while len(head) + len(body) + len(LINE) <= octets:
        body += LINE
    return head + body


def read_multiline(conn):
    """Read a multi-line reply body up to the terminator line; return octets."""
    total = 0
    while True:
        line = conn.readline()
        if not line:
            raise SystemExit("connection closed in a multi-line reply")
        total += len(line)
        if line == b".\r\n":
            return total


def timed_multiline(conn, text):
    started = time.perf_counter()
    reply = conn.line(text)
    octets = read_multiline(conn) if reply[:1] == b"2" else 0
    return time.perf_counter() - started, reply, octets


def start_owner(image, config, env, stderr_path):
    stderr = open(stderr_path, "ab")
    started = time.perf_counter()
    proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"],
                            env=env, stdout=subprocess.PIPE, stderr=stderr)
    wait_for_announcement(proc, b"LISTENING ", timeout=3600)
    return proc, time.perf_counter() - started, stderr


def stop_owner(proc, stderr):
    proc.terminate()
    try:
        proc.wait(timeout=600)
    except subprocess.TimeoutExpired:
        proc.kill()
    stderr.close()


def census(cdir, proc, tag):
    (cdir / "go.tmp").write_text(tag + "\n")
    os.rename(cdir / "go.tmp", cdir / "go")
    started = time.perf_counter()
    while not (cdir / ("done-" + tag)).exists():
        time.sleep(0.2)
        if proc.poll() is not None:
            raise SystemExit("owner died during the census")
    seconds = time.perf_counter() - started
    text = None
    for path in sorted(cdir.glob("*" + tag + "*")):
        if path.name.startswith("done-"):
            continue
        text = path.read_text(errors="replace")
    after = None
    if text:
        for line in text.splitlines():
            if line.startswith("dynamic-usage-after-gc"):
                after = int(line.split()[1])
    return {"seconds": seconds, "dynamic_usage_after_gc": after}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--image", required=True)
    p.add_argument("--work", required=True)
    p.add_argument("--articles", type=int, required=True)
    p.add_argument("--octets", type=int, default=0, help="target article size; 0 = the 155-octet article")
    p.add_argument("--samples", type=int, default=16)
    p.add_argument("--json", required=True)
    p.add_argument("--census", default=None, help="the rep-heap census.lisp to load (images with the hook)")
    p.add_argument("--profile", default="default")
    p.add_argument("--max-transactions", type=int, default=None)
    a = p.parse_args()
    image = Path(a.image).resolve()
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    cdir = None
    if a.census:
        cdir = work / "census"
        cdir.mkdir()
        env["FN_CENSUS_DIR"] = str(cdir)
        env["FN_CENSUS_LOAD"] = a.census
    port = m.free_port()
    store, control, config = work / "store", work / "control.sock", work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, control), encoding="ascii")
    init = [str(image), "--fn", "operator", str(config), "init", "--profile", a.profile]
    if a.max_transactions:
        init += ["--max-transactions", str(a.max_transactions)]
    if a.octets:
        init += ["--max-article-octets", str(max(65536, a.octets * 2))]
    init += ["fn.test"]
    r = subprocess.run(init, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if r.returncode != 0:
        raise SystemExit("init failed: %r" % r.stdout[-400:])
    out = {"image": str(image), "launcher_sha256": m.digest(image),
           "core_sha256": m.digest(str(image) + ".core"), "articles": a.articles,
           "octets": a.octets, "article0_octets": len(article(0, a.octets)),
           "samples": a.samples, "port": port, "init": " ".join(init[4:])}
    proc, out["first_open_seconds"], stderr = start_owner(image, config, env, work / "owner.stderr")
    try:
        c = m.Conn(port)
        load = []
        started_all = time.perf_counter()
        for i in range(a.articles):
            t0 = time.perf_counter()
            r = c.line("POST")
            if not r.startswith(b"340"):
                raise SystemExit("POST %d: %r" % (i, r))
            c.stream.write(article(i, a.octets) + b".\r\n")
            r = c.readline()
            if not r.startswith(b"240"):
                raise SystemExit("POST %d body: %r" % (i, r))
            load.append(time.perf_counter() - t0)
        c.close()
        out["load_seconds"] = time.perf_counter() - started_all
        q = max(1, a.articles // 4)
        out["post_all"] = m.summary(load)
        out["post_first_quarter"] = m.summary(load[:q])
        out["post_last_quarter"] = m.summary(load[-q:])
        out["rss_after_load_kib"] = m.rss_kib(proc.pid)
        if cdir:
            out["census_after_load"] = census(cdir, proc, "load")
            out["rss_after_census_kib"] = m.rss_kib(proc.pid)
        step = max(1, a.articles // a.samples)
        present = [m.msgid(i) for i in range(0, a.articles, step)][:a.samples]
        numbers = [i + 1 for i in range(0, a.articles, step)][:a.samples]
        c = m.Conn(port)
        c.line("STAT %s" % present[0])
        stat, art, art_octets = [], [], 0
        for msgid in present:
            dt, r = c.timed("STAT %s" % msgid)
            assert r.startswith(b"223"), r
            stat.append(dt)
        for msgid in present:
            dt, r, octets = timed_multiline(c, "ARTICLE %s" % msgid)
            assert r.startswith(b"220"), r
            art.append(dt)
            art_octets += octets
        r = c.line("GROUP fn.test")
        out["group_reply"] = r.decode("ascii", "replace").strip()
        over = []
        for n in numbers:
            dt, r, octets = timed_multiline(c, "OVER %d" % n)
            assert r.startswith(b"224"), r
            over.append(dt)
        c.close()
        out["stat_present"] = m.summary(stat)
        out["article_present"] = m.summary(art)
        out["article_octets_read"] = art_octets
        out["over_present"] = m.summary(over)
        out["rss_after_reads_kib"] = m.rss_kib(proc.pid)
    finally:
        stop_owner(proc, stderr)
    # The owner's load time at N: a fresh process on the same store.
    proc, out["reopen_seconds"], stderr = start_owner(image, config, env, work / "owner-reopen.stderr")
    try:
        out["rss_after_reopen_kib"] = m.rss_kib(proc.pid)
        c = m.Conn(port)
        dt, r = c.timed("STAT %s" % m.msgid(a.articles - 1))
        out["reopen_last_stat"] = r.decode("ascii", "replace").strip()
        c.close()
        if cdir:
            out["census_after_reopen"] = census(cdir, proc, "reopen")
    finally:
        stop_owner(proc, stderr)
    Path(a.json).write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items() if not isinstance(v, dict)}))
    for k, v in out.items():
        if isinstance(v, dict) and "median_ms" in v:
            print(k, "median %.3f ms  p95 %.3f ms  max %.3f ms" % (v["median_ms"], v["p95_ms"], v["max_ms"]))


if __name__ == "__main__":
    main()
