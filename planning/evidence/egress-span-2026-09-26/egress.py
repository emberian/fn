#!/usr/bin/env python3
"""egress-span (2026-09-26): where an ARTICLE's wall goes (PKT-555), and
the reply's owner CPU and bytes consed before/after the buffer range.

    python3 egress.py IMAGE WORK OUT.json   (run from an image's tree root)

IMAGE is a developer image, or its profiling twin (build/fn-host-developer-prof
with FN_PROF_LOAD naming hooks.lisp and FN_HEAP_DIR set, the perf-ledger
setup) for bytes consed per operation.  One store, the default profile with
--max-article-octets 4194304 (the ledger's big phase), on WORK (tmpfs).
POST 2 KiB, 32 KiB, 3 MiB; then each ARTICLE size read by three clients on
their own connections:

  harness   tools/msgid_measure.Conn + rep_measure.read_multiline: an
            unbuffered socket file (makefile buffering=0), readline per
            line (the ledger's figures)
  buffered  a 1 MiB-buffered socket file, readline per line
  raw       recv(1 MiB) until the reply ends CRLF.CRLF

Per operation: wall, owner process CPU (/proc/PID/stat), client CPU
(time.process_time), the owner's write syscalls and octets written
(/proc/PID/io syscw, wchar), and the serving thread ("fn owner client")
sampled every 1 ms from /proc/PID/task/TID/{stat,syscall}: running, or
blocked and in which syscall.  This script is the owner's ancestor, so
yama ptrace_scope 1 lets it read the syscall file.
"""
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import threading
import time

ROOT = Path.cwd()
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
import msgid_measure as m  # noqa: E402
import rep_measure as r  # noqa: E402

TICK = os.sysconf("SC_CLK_TCK")
SYSCALLS = {"7": "poll", "1": "write", "0": "read", "44": "sendto", "45": "recvfrom",
            "202": "futex", "230": "clock_nanosleep", "35": "nanosleep", "271": "ppoll",
            "23": "select", "232": "epoll_wait", "281": "epoll_pwait"}


def cpu_s(pid):
    f = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(f[11]) + int(f[12])) / TICK


def io(pid):
    out = {}
    for row in Path("/proc/%d/io" % pid).read_text().splitlines():
        k, v = row.split(":")
        out[k] = int(v)
    return out


def client_tids(pid):
    tids = []
    for t in Path("/proc/%d/task" % pid).iterdir():
        try:
            if (t / "comm").read_text().strip() == "fn owner client":
                tids.append(int(t.name))
        except OSError:
            pass
    return set(tids)


class Sampler(threading.Thread):
    """The serving thread's state every 1 ms: R, or the syscall it waits in."""

    def __init__(self, pid, tid):
        super().__init__(daemon=True)
        self.base = "/proc/%d/task/%d/" % (pid, tid)
        self.stop_ev = threading.Event()
        self.hist = {}

    def run(self):
        while not self.stop_ev.is_set():
            try:
                st = open(self.base + "stat").read().rsplit(")", 1)[1].split()[0]
                if st == "R":
                    key = "running"
                else:
                    sc = open(self.base + "syscall").read().split()[0]
                    key = "%s:%s" % (st, SYSCALLS.get(sc, sc))
            except OSError:
                key = "gone"
            self.hist[key] = self.hist.get(key, 0) + 1
            time.sleep(0.001)


def open_conn(port, proc, kind):
    before = client_tids(proc.pid)
    if kind == "harness":
        c = m.Conn(port)
        sock = c.sock
    else:
        sock = socket.create_connection(("127.0.0.1", port), timeout=600)
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        c = sock
    deadline = time.time() + 10
    new = set()
    while not new and time.time() < deadline:
        new = client_tids(proc.pid) - before
        time.sleep(0.01)
    tid = min(new) if new else None
    if kind == "buffered":
        f = sock.makefile("rb", buffering=1 << 20)
        f.readline()
        c = (sock, f)
    elif kind == "raw":
        greet = b""
        while not greet.endswith(b"\r\n"):
            greet += sock.recv(4096)
    return c, tid


def request(c, kind, text):
    if kind == "harness":
        return r.timed_multiline(c, text)[2]
    if kind == "buffered":
        sock, f = c
        sock.sendall(text.encode("ascii") + b"\r\n")
        status = f.readline()
        total = 0
        if status[:1] != b"2":
            raise SystemExit("reply %r" % status)
        while True:
            line = f.readline()
            if not line:
                raise SystemExit("closed")
            total += len(line)
            if line == b".\r\n":
                return total
    sock = c
    sock.sendall(text.encode("ascii") + b"\r\n")
    got = bytearray()
    while True:
        chunk = sock.recv(1 << 20)
        if not chunk:
            raise SystemExit("closed")
        got += chunk
        if got.endswith(b"\r\n.\r\n"):
            if not got.startswith(b"2"):
                raise SystemExit("reply %r" % bytes(got[:80]))
            return len(got) - (got.index(b"\r\n") + 2)


def measure(proc, heap, port, kind, number, k, label):
    c, tid = open_conn(port, proc, kind)
    if kind == "harness":
        c.line("GROUP fn.test")
    elif kind == "buffered":
        c[0].sendall(b"GROUP fn.test\r\n")
        c[1].readline()
    else:
        c.sendall(b"GROUP fn.test\r\n")
        g = b""
        while not g.endswith(b"\r\n"):
            g += c.recv(4096)
    walls, sizes = [], []
    snap0 = heap.snap(label + "0")
    c0, io0, p0 = cpu_s(proc.pid), io(proc.pid), time.process_time()
    sampler = Sampler(proc.pid, tid) if tid else None
    if sampler:
        sampler.start()
    for _ in range(k):
        t0 = time.perf_counter()
        sizes.append(request(c, kind, "ARTICLE %d" % number))
        walls.append(time.perf_counter() - t0)
    if sampler:
        sampler.stop_ev.set()
        sampler.join()
    c1, io1, p1 = cpu_s(proc.pid), io(proc.pid), time.process_time()
    snap1 = heap.snap(label + "1")
    out = {"client": kind, "n": k, "timing": m.summary(walls), "octets": sizes[0],
           "owner_cpu_ms_per_op": 1000 * (c1 - c0) / k,
           "client_cpu_ms_per_op": 1000 * (p1 - p0) / k,
           "owner_write_syscalls_per_op": (io1["syscw"] - io0["syscw"]) / k,
           "owner_octets_written_per_op": (io1["wchar"] - io0["wchar"]) / k,
           "serving_thread_1ms_samples": sampler.hist if sampler else None}
    if snap0 and snap1:
        out["bytes_consed_per_op"] = (snap1["bytes_consed"] - snap0["bytes_consed"]) / float(k)
    if kind == "harness":
        c.close()
    elif kind == "buffered":
        c[0].close()
    else:
        c.close()
    return out


def post(c, i, octets):
    """rep_measure.post with sendall: the harness's unbuffered stream.write
    may send a 3 MiB article partially and then wait on a reply forever."""
    t0 = time.perf_counter()
    reply = c.line("POST")
    if not reply.startswith(b"340"):
        raise SystemExit("POST %d: %r" % (i, reply))
    c.sock.sendall(r.article(i, octets) + b".\r\n")
    reply = c.readline()
    if not reply.startswith(b"240"):
        raise SystemExit("POST %d body: %r" % (i, reply))
    return time.perf_counter() - t0


def box():
    return {"loadavg": Path("/proc/loadavg").read_text().strip()}


def main():
    image, work, out_path = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    kinds = (sys.argv[4] if len(sys.argv) > 4 else "harness,buffered,raw").split(",")
    work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    port = m.free_port()
    config = work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, work / "control.sock"), encoding="ascii")
    e = dict(os.environ)
    e["ACL2_CUSTOMIZATION"] = "NONE"
    e.pop("ACL2_SYSTEM_BOOKS", None)
    heap_dir = e.get("FN_HEAP_DIR")
    if heap_dir:
        Path(heap_dir).mkdir(parents=True, exist_ok=True)
    out = {"image": str(image), "core_sha256": m.digest(str(image) + ".core"),
           "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "box_before": box()}
    ir = subprocess.run([str(image), "--fn", "operator", str(config), "init",
                         "--max-article-octets", "4194304", "fn.test"],
                        env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if ir.returncode != 0:
        raise SystemExit(ir.stdout.decode("ascii", "replace")[-400:])
    proc, out["open_s"], err = r.start_owner(image, config, e, work / "owner.stderr")
    heap = r.Heap(heap_dir, proc)
    try:
        c = m.Conn(port)
        c.line("GROUP fn.test")
        numbers = {}
        for i, (name, octets) in enumerate((("2k", 2048), ("32k", 32768), ("3m", 3 * 1024 * 1024))):
            numbers[name] = i + 1
            c0 = cpu_s(proc.pid)
            out["post_" + name] = {"wall_ms": 1000 * post(c, i, octets),
                                   "owner_cpu_ms": 1000 * (cpu_s(proc.pid) - c0)}
        c.close()
        for name in ("2k", "32k", "3m"):
            k = 3 if name == "3m" else 10
            for kind in kinds:
                out["article_%s_%s" % (name, kind)] = measure(
                    proc, heap, port, kind, numbers[name], k, "a%s%s" % (name, kind))
    finally:
        r.stop_owner(proc, err)
    out["box_after"] = box()
    out["ended_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    out_path.write_text(json.dumps(out, indent=1))
    for key, v in out.items():
        if key.startswith("article_"):
            print(key, "median %.1f ms" % v["timing"]["median_ms"], "owner %.0f ms" % v["owner_cpu_ms_per_op"],
                  "client %.0f ms" % v["client_cpu_ms_per_op"], "writes %.0f" % v["owner_write_syscalls_per_op"],
                  "consed %s" % v.get("bytes_consed_per_op"), v["serving_thread_1ms_samples"])
        elif key.startswith("post_"):
            print(key, v)


if __name__ == "__main__":
    main()
