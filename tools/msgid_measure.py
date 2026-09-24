#!/usr/bin/env python3
"""Served Message-ID lookup cost on a native image (T17).

One scratch store, one `operator run` of the named image on a kernel port.
N articles are posted through one NNTP reader connection (POST, one article
per command).  Then, on a fresh reader connection, `STAT <id>` is timed for
K present identifiers spread over the store and K absent ones.  Then one peer
record is added live whose source address is 127.0.0.1, so every later
loopback connection is a peer connection, and `IHAVE <present-id>` (435) and
`CHECK <present-id>` (438) are timed on one peer connection.  Every timing is
one command line written and its one status line read on an open socket: it
includes the loopback round trip and the owner's whole read, not process
startup.  The owner's VmRSS is sampled after each phase.

    python3 tools/msgid_measure.py --image build/fn-host-developer \
        --work /tank/fn/scratch/t17/n1000 --articles 1000 --json out.json
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from tests.native_process import wait_for_announcement  # noqa: E402


def digest(path):
    value = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            value.update(chunk)
    return value.hexdigest()


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def msgid(i):
    return "<t17-%06d@example.invalid>" % i


def article(i):
    return ("From: t17@example.invalid\r\n"
            "Newsgroups: fn.test\r\n"
            "Subject: t17 %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\n"
            "Message-ID: %s\r\n\r\nbody %d\r\n" % (i, msgid(i), i)).encode("ascii")


class Conn:
    # TCP_NODELAY on the client: without it a small command write can wait
    # for the delayed ACK of the previous reply (Nagle), and the wall time
    # then carries a timer instead of the server's work.
    nodelay = False

    def __init__(self, port):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=600)
        if Conn.nodelay:
            self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.stream = self.sock.makefile("rwb", buffering=0)
        self.greeting = self.stream.readline()

    def line(self, text):
        self.stream.write(text.encode("ascii") + b"\r\n")
        return self.stream.readline()

    def timed(self, text):
        started = time.perf_counter()
        reply = self.line(text)
        return time.perf_counter() - started, reply

    def close(self):
        try:
            self.line("QUIT")
        except OSError:
            pass
        self.sock.close()


def rss_kib(pid):
    try:
        for row in Path("/proc/%d/status" % pid).read_text().splitlines():
            if row.startswith("VmRSS:"):
                return int(row.split()[1])
    except OSError:
        return None
    return None


def summary(seconds):
    ms = sorted(s * 1000.0 for s in seconds)
    return {"n": len(ms), "min_ms": ms[0], "median_ms": statistics.median(ms),
            "p95_ms": ms[max(0, int(round(0.95 * len(ms))) - 1)], "max_ms": ms[-1]}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--image", required=True)
    p.add_argument("--work", required=True)
    p.add_argument("--articles", type=int, required=True)
    p.add_argument("--samples", type=int, default=50)
    p.add_argument("--json", required=True)
    p.add_argument("--nodelay", action="store_true",
                   help="set TCP_NODELAY on every client socket")
    a = p.parse_args()
    Conn.nodelay = a.nodelay
    image = Path(a.image).resolve()
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    port = free_port()
    store, control, config = work / "store", work / "control.sock", work / "fn.toml"
    subprocess.run([str(image), "--fn", "store", str(store), "init", "fn.test"],
                   env=env, check=True, stdout=subprocess.PIPE)
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\n'
                      'port = %d\n[control]\npath = "%s"\n' % (store, port, control),
                      encoding="ascii")
    stderr = open(work / "owner.stderr", "wb")
    proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"],
                            env=env, stdout=subprocess.PIPE, stderr=stderr)
    out = {"image": str(image), "launcher_sha256": digest(image),
           "core_sha256": digest(str(image) + ".core"), "articles": a.articles,
           "samples": a.samples, "port": port, "nodelay": a.nodelay}
    try:
        wait_for_announcement(proc, b"LISTENING ")
        # Load.
        c = Conn(port)
        load = []
        started_all = time.perf_counter()
        for i in range(a.articles):
            t0 = time.perf_counter()
            r = c.line("POST")
            if not r.startswith(b"340"):
                raise SystemExit("POST %d: %r" % (i, r))
            body = article(i)
            c.stream.write(body + b".\r\n")
            r = c.stream.readline()
            if not r.startswith(b"240"):
                raise SystemExit("POST %d body: %r" % (i, r))
            load.append(time.perf_counter() - t0)
        c.close()
        out["load_seconds"] = time.perf_counter() - started_all
        q = max(1, a.articles // 4)
        out["post_first_quarter"] = summary(load[:q])
        out["post_last_quarter"] = summary(load[-q:])
        out["rss_after_load_kib"] = rss_kib(proc.pid)
        step = max(1, a.articles // a.samples)
        present = [msgid(i) for i in range(0, a.articles, step)][:a.samples]
        absent = ["<t17-absent-%d@example.invalid>" % i for i in range(a.samples)]
        # Reader STAT.
        c = Conn(port)
        c.line("STAT %s" % present[0])  # warm
        hit, miss = [], []
        for m in present:
            dt, r = c.timed("STAT %s" % m)
            assert r.startswith(b"223"), r
            hit.append(dt)
        for m in absent:
            dt, r = c.timed("STAT %s" % m)
            assert r.startswith(b"430"), r
            miss.append(dt)
        c.close()
        out["stat_present"] = summary(hit)
        out["stat_absent"] = summary(miss)
        out["rss_after_stat_kib"] = rss_kib(proc.pid)
        # Live peer record: every later loopback connection is a peer.
        dead = free_port()
        subprocess.run([str(image), "--fn", "operator", str(config), "peer", "add",
                        "t17peer", "t17peer.example.invalid", "127.0.0.1",
                        str(dead), "fn.*", "fn.*", "127.0.0.1", "true"],
                       env=env, check=True, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=600)
        c = Conn(port)
        caps = c.line("MODE STREAM")
        out["peer_mode_stream"] = caps.decode("ascii", "replace").strip()
        ihave, check, check_absent = [], [], []
        for m in present:
            dt, r = c.timed("IHAVE %s" % m)
            assert r.startswith(b"435"), r
            ihave.append(dt)
        for m in present:
            dt, r = c.timed("CHECK %s" % m)
            assert r.startswith(b"438"), r
            check.append(dt)
        for m in absent:
            dt, r = c.timed("CHECK %s" % m)
            assert r[:3] in (b"238", b"431"), r
            check_absent.append(dt)
        c.close()
        out["ihave_duplicate"] = summary(ihave)
        out["check_duplicate"] = summary(check)
        out["check_absent"] = summary(check_absent)
        out["rss_after_peer_kib"] = rss_kib(proc.pid)
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=60)
        except subprocess.TimeoutExpired:
            proc.kill()
        stderr.close()
    Path(a.json).write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items() if not isinstance(v, dict)}))
    for k, v in out.items():
        if isinstance(v, dict):
            print(k, "median %.3f ms  p95 %.3f ms  max %.3f ms" % (
                v["median_ms"], v["p95_ms"], v["max_ms"]))


if __name__ == "__main__":
    main()
