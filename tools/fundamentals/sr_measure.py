#!/usr/bin/env python3
"""catalog-slice-7 step 9: served read costs on a COPY of a fixture store.

Measured on one `operator run` of IMAGE over a copy of FIXTURE/store:
  open       seconds from spawn to the LISTENING line
  greeting   K fresh connections, connect to the 200 line
  article_n  GROUP fn.test, then ARTICLE n for K numbers spread over 1..N
  over2000   OVER 1-2000 (after GROUP), R times; OVER 1-40 R times
  cpu        the owner process's utime+stime delta per batch / ops (ms/op)
Every timing is a command written and its whole reply read on an open
loopback socket.  Allocation per read needs the heap hook image; not here.
"""
import argparse, json, os, shutil, socket, statistics, subprocess, sys, time
from pathlib import Path

def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0)); return s.getsockname()[1]

BULK = True
class Conn:
    def __init__(self, port):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=900)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.f = self.sock.makefile("rwb", buffering=0)
        self.greeting = self.readline()
    def readline(self):
        if hasattr(socket, "TCP_QUICKACK"):
            self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_QUICKACK, 1)
        return self.f.readline()
    def line(self, t):
        self.f.write(t.encode() + b"\r\n"); return self.readline()
    def multi(self, t):
        if BULK:
            return self.multi_bulk(t)
        return self.multi_line(t)
    def multi_bulk(self, t):
        """The reply read in bulk (recv of up to 1 MiB) until its terminator;
        the per-line client (multi_line) spends ~2 us per octet in Python's
        unbuffered readline, which dominated the served numbers it reported."""
        t0 = time.perf_counter(); self.f.write(t.encode() + b"\r\n"); buf = b""
        while b"\r\n" not in buf:
            buf += self.sock.recv(1 << 20)
        first = buf[:buf.index(b"\r\n") + 2]
        if first[:3] in (b"220", b"221", b"222", b"224", b"225", b"211") and not t.startswith("GROUP"):
            while not (buf.endswith(b"\r\n.\r\n") and len(buf) > len(first)):
                buf += self.sock.recv(1 << 20)
            body = buf[len(first):]
            return time.perf_counter() - t0, first, body.count(b"\r\n") - 1, len(body)
        return time.perf_counter() - t0, first, 0, 0
    def multi_line(self, t):
        t0 = time.perf_counter(); first = self.line(t); n = 0; octets = 0
        if first[:3] in (b"220", b"221", b"222", b"224", b"225", b"211") and not t.startswith("GROUP"):
            while True:
                l = self.readline(); octets += len(l)
                if l in (b".\r\n", b""): break
                n += 1
        return time.perf_counter() - t0, first, n, octets

def cpu_ms(pid):
    f = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(f[11]) + int(f[12])) * 1000.0 / os.sysconf("SC_CLK_TCK")

def summ(xs):
    ms = sorted(x * 1000 for x in xs)
    return {"n": len(ms), "median_ms": round(statistics.median(ms), 2),
            "p95_ms": round(ms[max(0, int(round(0.95 * len(ms))) - 1)], 2), "max_ms": round(ms[-1], 2)}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--image", required=True); p.add_argument("--fixture", required=True)
    p.add_argument("--work", required=True); p.add_argument("--articles", type=int, default=10000)
    p.add_argument("--samples", type=int, default=40); p.add_argument("--repeats", type=int, default=5)
    p.add_argument("--json", required=True)
    p.add_argument("--keep-store", default=None, help="copy the loaded store here (a fixture for later runs)")
    p.add_argument("--prof", default=None, help="article|over2000: sample that batch with sb-sprof (prof image)")
    p.add_argument("--heap", action="store_true", help="bytes consed per batch (heap hook)")
    p.add_argument("--client", choices=("line", "bulk"), default="bulk")
    a = p.parse_args()
    global BULK; BULK = a.client == "bulk"
    work = Path(a.work); work.mkdir(parents=True, exist_ok=False)
    store = work / "store"
    env = dict(os.environ); env["ACL2_CUSTOMIZATION"] = "NONE"; env.pop("ACL2_SYSTEM_BOOKS", None)
    img = str(Path(a.image).resolve())
    fresh = a.fixture == "fresh"
    port = free_port(); cfg = work / "fn.toml"
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
                   % (store, port, work / "control.sock"))
    if fresh:
        subprocess.run([img, "--fn", "operator", str(cfg), "init", "--profile", "default", "--max-transactions", "16384", "--max-history-octets", str(256 << 20), "fn.test"],
                       env=env, check=True, stdout=subprocess.PIPE)
    else:
        shutil.copytree(Path(a.fixture) / "store", store, symlinks=True)
        if not (store / "keys").exists():
            subprocess.run([img, "--fn", "store", str(store), "node-secret", "create"], env=env,
                           check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    hook = "/tank/fn/scratch/served-readers/hook"
    if a.prof or a.heap:
        env["FN_PROF_LOAD"] = hook + "/io-only.lisp"; env["FN_HEAP_DIR"] = str(work / "heap"); (work / "heap").mkdir()
    if a.prof:
        env["FN_SPROF_DIR"] = str(work / "sprof"); (work / "sprof").mkdir()
    def heap(tag):
        if not (a.prof or a.heap): return None
        d = work / "heap"; (d / "go").write_text(tag)
        while not (d / ("done-" + tag)).exists(): time.sleep(0.02)
        return int((d / ("heap-" + tag + ".txt")).read_text().split()[1])
    def prof(which, phase):
        if a.prof != which: return
        d = work / "sprof"; (d / phase).write_text("x")
        if phase == "stop":
            while not (d / "done").exists(): time.sleep(0.05)
    err = open(work / "owner.stderr", "wb")
    t0 = time.perf_counter()
    proc = subprocess.Popen([img, "--fn", "operator", str(cfg), "run"], env=env,
                            stdout=subprocess.PIPE, stderr=err)
    out = {"image": img, "fixture": a.fixture, "articles": a.articles, "client": a.client}
    try:
        while True:
            l = proc.stdout.readline()
            if not l: raise SystemExit("owner exited before LISTENING")
            if l.startswith(b"LISTENING "): break
        out["open_s"] = round(time.perf_counter() - t0, 2)
        pid = proc.pid
        if fresh:
            body = ("x" * 76 + "\r\n") * 24
            c = Conn(port); t1 = time.perf_counter()
            for i in range(a.articles):
                r = c.line("POST"); assert r.startswith(b"340"), (i, r)
                art = ("From: cs7@example.invalid\r\nNewsgroups: fn.test\r\nSubject: cs7 %d\r\n"
                       "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: <cs7-%06d@example.invalid>\r\n\r\n%s"
                       % (i, i, body))
                c.f.write(art.encode() + b".\r\n"); r = c.readline(); assert r.startswith(b"240"), (i, r)
            c.line("QUIT"); c.sock.close(); out["load_s"] = round(time.perf_counter() - t1, 1)
        # settle: wait until the owner process is idle (a checkpoint publication
        # after the load or the open runs on its own thread and would be
        # charged to the reads): 2 s windows under 40 ms of CPU, at most 600 s.
        t_settle = time.perf_counter()
        while time.perf_counter() - t_settle < 600:
            c_a = cpu_ms(pid); time.sleep(2); c_b = cpu_ms(pid)
            if c_b - c_a < 40: break
        out["settle_s"] = round(time.perf_counter() - t_settle, 1)
        # greeting
        g = []; c0 = cpu_ms(pid)
        for _ in range(a.samples):
            s0 = time.perf_counter(); c = Conn(port); g.append(time.perf_counter() - s0)
            assert c.greeting.startswith(b"20"), c.greeting; c.sock.close()
        out["greeting"] = summ(g); out["greeting"]["owner_cpu_ms_per_op"] = round((cpu_ms(pid) - c0) / a.samples, 2)
        # ARTICLE by number
        c = Conn(port); r = c.line("GROUP fn.test"); out["group_reply"] = r.decode().strip()
        nums = [1 + (i * a.articles) // a.samples for i in range(a.samples)]
        c.multi("ARTICLE %d" % nums[0])
        xs = []; h0 = heap("a0"); prof("article", "start"); c0 = cpu_ms(pid)
        for n in nums:
            dt, first, _, _ = c.multi("ARTICLE %d" % n); assert first.startswith(b"220"), first; xs.append(dt)
        c1 = cpu_ms(pid); prof("article", "stop"); h1 = heap("a1")
        out["article_by_number"] = summ(xs); out["article_by_number"]["owner_cpu_ms_per_op"] = round((c1 - c0) / len(nums), 2)
        if h0 is not None: out["article_by_number"]["consed_bytes_per_op"] = (h1 - h0) // len(nums)
        for label, rng in (("over_2000", "1-2000"), ("over_40", "%d-%d" % (a.articles // 2, a.articles // 2 + 39))):
            xs = []; rows = None; h0 = heap(label + "0"); prof(label.replace("_", ""), "start"); c0 = cpu_ms(pid)
            for _ in range(a.repeats):
                dt, first, n, octets = c.multi("OVER %s" % rng); assert first.startswith(b"224"), first
                xs.append(dt); rows = n
            c1 = cpu_ms(pid); prof(label.replace("_", ""), "stop"); h1 = heap(label + "1")
            out[label] = summ(xs); out[label]["rows"] = rows
            out[label]["owner_cpu_ms_per_op"] = round((c1 - c0) / a.repeats, 2)
            if h0 is not None: out[label]["consed_bytes_per_op"] = (h1 - h0) // a.repeats
        c.line("QUIT"); c.sock.close()
        out["rss_kib"] = int([l for l in Path("/proc/%d/status" % pid).read_text().splitlines() if l.startswith("VmRSS")][0].split()[1])
        if a.keep_store:
            c = Conn(port); c.sock.close()
    finally:
        proc.terminate()
        try: proc.wait(timeout=60)
        except subprocess.TimeoutExpired: proc.kill()
    if a.keep_store and fresh:
        shutil.copytree(store, Path(a.keep_store) / "store", symlinks=True)
    Path(a.json).write_text(json.dumps(out, indent=1)); print(json.dumps(out))

if __name__ == "__main__":
    main()
