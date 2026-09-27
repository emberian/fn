#!/usr/bin/env python3
"""What a served connection costs, before and after the I/O loops (lane
connection-multiplexing, 2026-09-26; PKT-605).  Runs ON the box (hbox, the
OpenBSD VM) against one image; a measurement only, it decides nothing a node
does.  Same procedure for every image, so two runs on the same box state are a
comparison:

  1. a fresh development-profile store (`operator CONFIG init`), the capacity
     row raised to hold the run (`policy set exposure-connections N`), the
     node started (`operator CONFIG run`, RLIMIT_NOFILE 16384) and POSTS
     articles of 2 KiB posted;
  2. the node's RSS and thread count at rest;
  3. IDLE connections opened one after another, each to its greeting: the
     sequential setup rate; held open; RSS and threads again, and the RSS
     each one cost;
  4. with those held, ACTIVE readers at once: each connects (the greeting's
     latency), GROUP, then OVERS x `OVER 1-POSTS` (each OVER's latency, to
     the terminating dot line); p50/p95/max;
  5. the concurrent setup rate: 8 clients opening CONNECT connections each
     (connect, greeting, QUIT);
  6. everything closed; RSS once more.

    mux_measure.py IMAGE WORK [--idle 1000] [--active 200] [--overs 20]
                             [--posts 50] [--connect 250]
Output: one JSON document on stdout.  RSS by ps(1) (Linux and OpenBSD).
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import resource
import socket
import ssl
import statistics
import subprocess
import sys
import threading
import time

GROUP = "fn.test"
LINE = b"x" * 76 + b"\r\n"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def run(image, *args, env=None, check=True):
    res = subprocess.run([str(image), "--fn"] + [str(a) for a in args], env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if check and res.returncode:
        raise RuntimeError("%s rc=%d %r" % (args[:3], res.returncode, res.stdout[-400:]))
    return res


def rss_kib(pid):
    out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)],
                         stdout=subprocess.PIPE, text=True).stdout.strip()
    return int(out) if out.isdigit() else None


def threads(pid):
    status = Path("/proc/%d/status" % pid)
    if status.exists():
        for row in status.read_text().splitlines():
            if row.startswith("Threads:"):
                return int(row.split()[1])
    out = subprocess.run(["ps", "-H", "-o", "pid=", "-p", str(pid)],
                         stdout=subprocess.PIPE, text=True).stdout.split()
    return len(out) or None


def raise_nofile():
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    want = 16384 if hard == resource.RLIM_INFINITY else min(16384, hard)
    resource.setrlimit(resource.RLIMIT_NOFILE, (max(soft, want), hard))


TLS = None  # an ssl.SSLContext when --tls: the reader connections use implicit TLS


class Conn:
    def __init__(self, port, timeout=120, tls=None):
        sock = socket.create_connection(("127.0.0.1", port), timeout=timeout)
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.sock = tls.wrap_socket(sock, server_hostname="localhost") if tls else sock
        self.stream = self.sock.makefile("rwb", buffering=0)
        self.greeting = self.stream.readline()

    def line(self, text):
        self.stream.write(text.encode("ascii") + b"\r\n")
        return self.stream.readline()

    def dotted(self):
        count = 0
        while True:
            row = self.stream.readline()
            if not row:
                raise RuntimeError("closed inside a multi-line reply")
            if row == b".\r\n":
                return count
            count += 1

    def close(self):
        try:
            self.sock.close()
        except OSError:
            pass


def article(i):
    head = ("From: mux@example.invalid\r\nNewsgroups: %s\r\nSubject: mux %d\r\n"
            "Date: Sat, 26 Sep 2026 12:00:00 +0000\r\n"
            "Message-ID: <mux-%06d@example.invalid>\r\n\r\n" % (GROUP, i, i)).encode("ascii")
    return head + LINE * 26


def pct(values, q):
    if not values:
        return None
    ordered = sorted(values)
    return round(1000 * ordered[min(len(ordered) - 1, int(q * len(ordered)))], 3)


def summary(values):
    return {"n": len(values), "p50_ms": pct(values, 0.50), "p95_ms": pct(values, 0.95),
            "max_ms": round(1000 * max(values), 3) if values else None}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("image")
    p.add_argument("work")
    p.add_argument("--idle", type=int, default=1000)
    p.add_argument("--active", type=int, default=200)
    p.add_argument("--overs", type=int, default=20)
    p.add_argument("--posts", type=int, default=50)
    p.add_argument("--connect", type=int, default=250)
    p.add_argument("--tls", action="store_true",
                   help="readers over implicit TLS (a fresh self-signed RSA-2048 pair)")
    a = p.parse_args()
    raise_nofile()
    image, work = Path(a.image), Path(a.work)
    work.mkdir(parents=True, exist_ok=True)
    for name in ("store", "c.sock", "fn.log"):
        subprocess.run(["rm", "-rf", str(work / name)], check=True)
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    port = free_port()
    config = work / "fn.toml"
    listener = ""
    rport = port
    tls = None
    if a.tls:
        cert, key = work / "cert.pem", work / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
                        "-out", str(cert), "-sha256", "-days", "1", "-nodes", "-subj",
                        "/CN=localhost"], check=True, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)
        rport = free_port()
        listener = 'tls_cert = "%s"\ntls_key = "%s"\ntls_port = %d\n' % (cert, key, rport)
        tls = ssl.create_default_context(cafile=str(cert))
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n%s'
                      '[control]\npath = "%s"\n[log]\npath = "%s"\n'
                      '[auth]\nprotected_only = false\n'
                      % (work / "store", port, listener, work / "c.sock", work / "fn.log"),
                      encoding="ascii")
    run(image, "operator", config, "init", "--profile", "development", "fn.letters",
        GROUP, env=env)
    capacity = a.idle + a.active + 64
    run(image, "operator", config, "policy", "set", "exposure-connections", capacity, env=env)
    doc = {"image": str(image), "tls": a.tls, "idle": a.idle, "active": a.active, "overs": a.overs,
           "posts": a.posts, "capacity": capacity}
    stderr = open(work / "owner.stderr", "wb")
    proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], env=env,
                            stdout=subprocess.PIPE, stderr=stderr, preexec_fn=raise_nofile)
    try:
        deadline = time.monotonic() + 600
        while time.monotonic() < deadline:
            row = proc.stdout.readline()
            if not row:
                raise RuntimeError("the node exited before LISTENING rc=%r" % proc.poll())
            if row.startswith(b"LISTENING "):
                break
        c = Conn(port)
        for i in range(a.posts):
            if not c.line("POST").startswith(b"340"):
                raise RuntimeError("POST refused")
            c.stream.write(article(i) + b".\r\n")
            reply = c.stream.readline()
            if not reply.startswith(b"240"):
                raise RuntimeError("POST %d: %r" % (i, reply))
        c.close()
        time.sleep(2)
        doc["rest"] = {"rss_kib": rss_kib(proc.pid), "threads": threads(proc.pid)}

        held = []
        started = time.perf_counter()
        for _ in range(a.idle):
            conn = Conn(rport, tls=tls)
            if not conn.greeting.startswith(b"20"):
                raise RuntimeError("idle connection %d: %r" % (len(held), conn.greeting))
            held.append(conn)
        seconds = time.perf_counter() - started
        doc["setup_sequential_per_s"] = round(a.idle / seconds, 1)
        time.sleep(3)
        after = rss_kib(proc.pid)
        doc["idle_held"] = {"rss_kib": after, "threads": threads(proc.pid),
                            "rss_per_connection_kib":
                                round((after - doc["rest"]["rss_kib"]) / a.idle, 2)}

        greet, overs, errors = [], [], []
        lock = threading.Lock()
        barrier = threading.Barrier(a.active)

        def reader():
            try:
                barrier.wait(timeout=120)
                t0 = time.perf_counter()
                conn = Conn(rport, tls=tls)
                g = time.perf_counter() - t0
                mine = []
                if not conn.line("GROUP %s" % GROUP).startswith(b"211"):
                    raise RuntimeError("GROUP refused")
                for _ in range(a.overs):
                    t1 = time.perf_counter()
                    if not conn.line("OVER 1-%d" % a.posts).startswith(b"224"):
                        raise RuntimeError("OVER refused")
                    conn.dotted()
                    mine.append(time.perf_counter() - t1)
                conn.line("QUIT")
                conn.close()
                with lock:
                    greet.append(g)
                    overs.extend(mine)
            except Exception as exc:  # noqa: BLE001 - a measurement records it
                with lock:
                    errors.append(repr(exc))

        workers = [threading.Thread(target=reader) for _ in range(a.active)]
        t0 = time.perf_counter()
        for w in workers:
            w.start()
        for w in workers:
            w.join()
        doc["active"] = {"seconds": round(time.perf_counter() - t0, 3),
                         "greeting": summary(greet), "over": summary(overs),
                         "errors": errors[:5], "error_count": len(errors),
                         "rss_kib": rss_kib(proc.pid)}

        opened = []

        def connector():
            for _ in range(a.connect):
                try:
                    conn = Conn(rport, tls=tls)
                    conn.line("QUIT")
                    conn.close()
                    with lock:
                        opened.append(1)
                except Exception as exc:  # noqa: BLE001
                    with lock:
                        errors.append(repr(exc))

        clients = [threading.Thread(target=connector) for _ in range(8)]
        t0 = time.perf_counter()
        for w in clients:
            w.start()
        for w in clients:
            w.join()
        doc["setup_concurrent_per_s"] = round(len(opened) / (time.perf_counter() - t0), 1)
        doc["hwm_rss_kib"] = rss_kib(proc.pid)
        for conn in held:
            conn.close()
        time.sleep(5)
        doc["closed"] = {"rss_kib": rss_kib(proc.pid), "threads": threads(proc.pid)}
        doc["errors_total"] = len(errors)
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=120)
        except subprocess.TimeoutExpired:
            proc.kill()
        stderr.close()
    doc["owner_rc"] = proc.returncode
    json.dump(doc, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
