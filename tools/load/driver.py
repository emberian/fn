#!/usr/bin/env python3
"""tools/load: run named cells of the load matrix against a node image or fn-core.

    python3 -m tools.load.driver run --cell W13 --image IMG --out DIR [--arms A,B] [--repeat 2]
    python3 -m tools.load.driver run --cell W2@10k --image IMG --out DIR
    python3 -m tools.load.driver list
    python3 -m tools.load.driver box --box hbox --image IMG --cell W13 --label L   (laptop: ship, start detached)
    python3 -m tools.load.driver fetch LABEL                                      (laptop: pull a finished run)
    python3 -m tools.load.result judge RESULT.json [--file-items]
    python3 -m tools.load.result report RESULT.json [--out report.md]

`run` is for the box: one process, one node at a time, DIR/result.json rewritten
after every phase, one `FN_LOAD_RESULT {json}` line per finished cell on stdout
and in DIR/cells.jsonl.  Targets: --image (any fn-host image; its own launcher)
and --fn-core (E's core through its launcher; in-process hooks go in through
XL_HOOK=FILE).  With both, the order is rep -> target -> arm, so W13 runs
A B A B on each target in turn within a rep.

Probes the image does not expose are recorded NOT-MEASURED with the reason, never
estimated.  Everything is loopback on one box.
"""
from __future__ import annotations

import argparse
import collections
import contextlib
import datetime as dt
import hashlib
import itertools
import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))

from tools.load import cells as cells_mod          # noqa: E402
from tools.load import result as res_mod            # noqa: E402
from tools.load import workloads as wl              # noqa: E402

BOX_BASE = "/tank/fn/scratch/load-harness"
# One-off hook files live in the evidence dir (not tools/load): O2's FN_TRACE spans replace them.
HOOKS = ROOT / "planning" / "evidence" / "load" / "hooks"
HOOK = HOOKS / "w13-idle-gc.lisp"
CENSUS_HOOK = HOOKS / "w15-census.lisp"
FIXTURES = "/tank/fn/scratch/fixtures-0b4d3b183"
PROF_HOOK = Path("/tank/fn/scratch/extract-prof/prof2.lisp")      # E's deterministic encapsulate hook (same path on hbox and persvati)
CLK = os.sysconf("SC_CLK_TCK") if hasattr(os, "sysconf") else 100


class CellError(Exception):
    pass


# ---------------------------------------------------------------- /proc readers

def read_kv(path, keys=None):
    out = {}
    try:
        for line in Path(path).read_text().splitlines():
            k, _, v = line.partition(":")
            if keys is None or k in keys:
                parts = v.split()
                if parts and parts[0].isdigit():
                    out[k] = int(parts[0])
    except OSError:
        pass
    return out


def proc_snapshot(pid):
    """VmRSS/VmHWM/RssAnon/RssFile (status), Pss (smaps_rollup), CPU s, io octets, threads."""
    st = read_kv("/proc/%d/status" % pid, {"VmRSS", "VmHWM", "RssAnon", "RssFile", "Threads"})
    if "VmRSS" not in st:
        return None
    sm = read_kv("/proc/%d/smaps_rollup" % pid, {"Rss", "Pss", "Anonymous"})
    io = read_kv("/proc/%d/io" % pid, {"read_bytes", "write_bytes", "rchar", "wchar"})
    cpu = None
    with contextlib.suppress(OSError, IndexError, ValueError):
        fields = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
        cpu = (int(fields[11]) + int(fields[12])) / CLK
    return {"vmrss": st.get("VmRSS"), "hwm": st.get("VmHWM"), "anon": st.get("RssAnon", sm.get("Anonymous")),
            "file": st.get("RssFile"), "pss": sm.get("Pss"), "smaps_rss": sm.get("Rss"),
            "threads": st.get("Threads"), "cpu_s": cpu, "io": io}


def loadavg():
    return [float(x) for x in Path("/proc/loadavg").read_text().split()[:3]]


def cpu_ticks():
    """{core: (busy, total)} jiffies per core from /proc/stat."""
    out = {}
    for ln in Path("/proc/stat").read_text().splitlines():
        if ln.startswith("cpu") and ln[3:4].isdigit():
            f = ln.split()
            v = [int(x) for x in f[1:9]]
            idle = v[3] + v[4]
            out[int(f[0][3:])] = (sum(v) - idle, sum(v))
    return out


def busy_cores(cores, seconds=2.0):
    """Cores' worth of busy time on CORES over a short window (the quiet rule of ruling 17, per core, not loadavg)."""
    a = cpu_ticks()
    time.sleep(seconds)
    b = cpu_ticks()
    tot = 0.0
    for c in cores:
        if c in a and c in b and b[c][1] > a[c][1]:
            tot += (b[c][0] - a[c][0]) / (b[c][1] - a[c][1])
    return round(tot, 2)


def arc_size():
    return read_kv("/proc/spl/kstat/zfs/arcstats", {"size"}).get("size") if Path("/proc/spl/kstat/zfs/arcstats").exists() else None


def fs_type(path):
    with contextlib.suppress(Exception):
        return subprocess.run(["stat", "-f", "-c", "%T", str(path)], capture_output=True, text=True, timeout=10).stdout.strip()
    return None


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 22), b""):
            h.update(block)
    return h.hexdigest()


class Sampler(threading.Thread):
    """Samples the owner's memory every `interval` s; per-phase peaks are read and reset by the driver."""

    def __init__(self, node, interval):
        super().__init__(daemon=True)
        self.node, self.interval, self.stop_ev = node, interval, threading.Event()
        self.lock, self.series = threading.Lock(), []
        self.peak = {"vmrss": 0, "anon": 0, "hwm": 0}

    def run(self):
        while not self.stop_ev.wait(self.interval):
            pid = self.node.pid
            s = proc_snapshot(pid) if pid else None
            if not s:
                continue
            with self.lock:
                self.series.append((round(time.time(), 2), s["vmrss"], s["anon"], s["hwm"]))
                for k in self.peak:
                    self.peak[k] = max(self.peak[k], s.get(k) or 0)

    def take_peak(self):
        with self.lock:
            p, self.peak = dict(self.peak), {"vmrss": 0, "anon": 0, "hwm": 0}
        return p


# ---------------------------------------------------------------- target and node

class Target:
    """An image or an fn-core: the launcher path and how a hook gets into it."""

    def __init__(self, kind, path):
        self.kind, self.path = kind, Path(path).resolve()
        core = Path(str(self.path) + ".core")
        self.core = core if core.is_file() else (self.path if self.kind == "fn-core" else None)
        self._sha = None
        tree = self.path.parent
        self.tree_sha = next(((tree / n).read_text().strip() for n in ("TREE_SHA", "../TREE_SHA")
                              if (tree / n).is_file()), None)

    @property
    def core_sha256(self):
        if self._sha is None and self.core is not None:
            self._sha = sha256_file(self.core)
        return self._sha

    def launcher(self, workdir, hooks, env):
        """(launcher path, env) with the hook files loaded before the node starts."""
        if not hooks:
            return self.path, env
        if len(hooks) == 1:
            hook = hooks[0]
        else:
            hook = Path(workdir) / "hooks.lisp"
            hook.write_text("".join('(load "%s")\n' % h for h in hooks))
        if self.kind == "fn-core":
            env = dict(env, XL_HOOK=str(hook))
            return self.path, env
        wrap = Path(workdir) / "hooked"
        shutil.rmtree(wrap, ignore_errors=True)
        wrap.mkdir(parents=True)
        for sib in self.path.parent.glob("fn-host*"):
            if sib.name != self.path.name:
                (wrap / sib.name).symlink_to(sib)
        text = self.path.read_text()
        pat = re.compile(r"""--eval (['"])\(acl2::sbcl-restart\)\1""")
        if not pat.search(text):
            raise CellError("launcher %s has no --eval (acl2::sbcl-restart) to put the hook before" % self.path)
        text = pat.sub(lambda mo: '--eval "(load \\"%s\\")" --eval "(acl2::sbcl-restart)"' % hook, text)
        out = wrap / self.path.name
        out.write_text(text)
        out.chmod(0o755)
        return out, env


class Node:
    def __init__(self, target, work, flags, groups, sbcl_args, hooks, gc_log, extra_env, interval, heap_mode="decided", max_connections=None):
        self.target, self.work, self.flags, self.groups = target, Path(work), flags, groups
        self.heap_mode, self.decided = heap_mode, None
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE", SBCL_USER_ARGS=sbcl_args)
        for k in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "FN_PROF_OUT", "FN_PROF_HOOK", "XL_HOOK"):
            self.env.pop(k, None)
        self.env.update(extra_env)
        self.max_connections = max_connections
        if hooks:
            self.env["FN_LOAD_GC_LOG"] = str(gc_log)
        self.launcher, self.env = target.launcher(self.work, hooks, self.env)
        self.gc_log = Path(gc_log)
        self.proc, self.pid, self.port = None, None, None
        self.config = self.work / "fn.toml"
        self.store = self.work / "store"
        self.err_n = 0
        self.sampler = Sampler(self, interval)
        self.last_exit = None

    def write_config(self):
        import socket
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            self.port = s.getsockname()[1]
        server = ""        # fn.toml has no [server] table (books/native-config.lisp: key-allowedp); the cap is policy, see apply_policy
        self.config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n%s'
                               % (self.store, self.port, self.work / "c.sock", server))

    def argv(self, *words):
        return [str(self.launcher), "--fn", "operator", str(self.config), *words]

    def init(self):
        self.write_config()
        p = subprocess.run(self.argv("init", *self.flags, *self.groups), env=self.env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=900)
        if p.returncode != 0:
            raise CellError("operator init exit %d: %s" % (p.returncode, p.stdout[-400:].decode("utf-8", "replace")))

    def decide_heap(self):
        """The heap and control stack the image's own probe decides for this store (MEM-002):
        `IMAGE --fn heap -- operator CONFIG run`, as tests/native_harness.decided_launch does."""
        p = subprocess.run([str(self.launcher), "--fn", "heap", "--", "operator", str(self.config), "run"], env=self.env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        out = p.stdout.decode("utf-8", "replace")
        heap, stack = re.search(r"heap=(\d+) MB", out), re.search(r"stack=(\d+) KB", out)
        if p.returncode != 0 or not (heap and stack):
            if self.target.kind == "fn-core":      # the core's launcher has no heap probe: its declared launch stands
                self.decided = self.env["SBCL_USER_ARGS"]
                self.heap_probe_failed = out[-200:]
                return self.decided
            raise CellError("heap probe exit %d: %s" % (p.returncode, out[-300:]))
        self.decided = "--dynamic-space-size %sMB --control-stack-size %sKB" % (heap.group(1), stack.group(1))
        self.env["SBCL_USER_ARGS"] = self.decided
        return self.decided

    def start(self, timeout=1800):
        import select
        if self.heap_mode == "decided":
            self.decide_heap()
        self.err_n += 1
        errp = self.work / ("owner.%d.err" % self.err_n)
        err = open(errp, "wb")
        t0 = time.monotonic()
        self.proc = subprocess.Popen(self.argv("run"), env=self.env, stdout=subprocess.PIPE, stderr=err)
        self.pid = self.proc.pid
        deadline = t0 + timeout
        while True:
            if not select.select([self.proc.stdout], [], [], max(0.1, deadline - time.monotonic()))[0]:
                raise CellError("no LISTENING in %d s" % timeout)
            line = self.proc.stdout.readline()
            if not line:
                self.proc.wait()
                raise CellError("owner exited %s before LISTENING: %s" % (self.proc.returncode,
                                errp.read_text("utf-8", "replace")[-400:]))
            if line.startswith(b"LISTENING"):
                break
        threading.Thread(target=lambda: [None for _ in iter(lambda: self.proc.stdout.read(4096), b"")], daemon=True).start()
        self.open_s = time.monotonic() - t0
        snap = proc_snapshot(self.pid)
        self.open_cpu_s = snap["cpu_s"] if snap else None
        return self.open_s

    def stop(self, grace=300):
        if not self.proc:
            return None
        if self.proc.poll() is None:
            self.proc.terminate()
        try:
            rc = self.proc.wait(grace)
        except subprocess.TimeoutExpired:
            self.proc.kill()      # our own child, by the PID we started
            rc = self.proc.wait(60)
        self.last_exit, self.proc, self.pid = rc, None, None
        return rc

    def policy_set(self, key, value):
        """`operator CONFIG policy set KEY VALUE` against the live owner: (exit code, output tail)."""
        p = subprocess.run(self.argv("policy", "set", key, str(value)), env=self.env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=120)
        return p.returncode, p.stdout.decode("utf-8", "replace").strip()[-300:]

    def verb(self, *argv):
        """An offline `store ROOT ...` verb, timed (the owner must be stopped)."""
        t0 = time.monotonic()
        p = subprocess.run([str(self.launcher), "--fn", "store", str(self.store), *argv], env=self.env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=3600)
        return p.returncode, time.monotonic() - t0, p.stdout.decode("utf-8", "replace")[-300:]


# ---------------------------------------------------------------- clients

def _clients():
    import msgid_measure as m
    import rep_measure as r
    return m, r


def refusal_name(reply):
    words = re.sub(r"[^a-z0-9 ]", "", reply.decode("latin-1").strip().lower()).split()
    return "-".join(words[:5]) or "empty"


class Counters:
    def __init__(self):
        self.lock = threading.Lock()
        self.refusals = collections.Counter()
        self.admitted = 0
        self.refused = 0
        self._ids = itertools.count()
        self.known = []

    def next_id(self):
        with self.lock:
            return next(self._ids)

    def ok(self, i):
        with self.lock:
            self.admitted += 1
            self.known.append(i)

    def refuse(self, reply):
        with self.lock:
            self.refused += 1
            self.refusals[refusal_name(reply)] += 1


def post_one(conn, ctr, octets, retries=40):
    """One POST that counts its refusals by name and retries a refused POST command; seconds or None."""
    m, r = _clients()
    i = ctr.next_id()
    for _ in range(retries):
        t0 = time.perf_counter()
        first = conn.line("POST")
        if not first.startswith(b"340"):
            ctr.refuse(first)
            time.sleep(0.25)
            continue
        conn.stream.write(r.article(i, octets) + b".\r\n")
        final = conn.readline()
        dt_ = time.perf_counter() - t0
        if final.startswith(b"240"):
            ctr.ok(i)
            return dt_
        ctr.refuse(final)
        return None
    return None


def store_files(root):
    """relative path -> (octets, mtime_ns) for every file under the store."""
    out = {}
    for dp, _, fns in os.walk(root):
        for fn in fns:
            fp = Path(dp) / fn
            with contextlib.suppress(OSError):
                st = fp.stat()
                out[str(fp.relative_to(root))] = (st.st_size, st.st_mtime_ns)
    return out


def components(files):
    """Octets per component: files grouped by path with digit runs and hex names folded to '#'."""
    out = collections.Counter()
    for k, (size, _) in files.items():
        out[re.sub(r"[0-9a-f]{8,}|\d+", "#", k)] += size
    return dict(out)


def site_probe(directory, n=200):
    """4 KiB write + fdatasync loop in the store's filesystem: p50/p99 ms.  Reported with every cell, so a ZFS site's
    sync cost is never read as the node's (T-SYNC)."""
    path = Path(directory) / "site-probe.bin"
    buf = b"\x5a" * 4096
    ts = []
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT, 0o600)
        try:
            for _ in range(n):
                t0 = time.perf_counter()
                os.write(fd, buf)
                os.fdatasync(fd)
                ts.append(time.perf_counter() - t0)
        finally:
            os.close(fd)
            os.unlink(path)
    except OSError as e:
        return {"error": repr(e)}
    st = res_mod.lat_stats(ts)
    return {"fs": fs_type(directory), "write4k_fdatasync": st, "n": n}


def mid(x):
    """A message-id: the string itself (discovered from OVER) or the id of our own article i."""
    return x if isinstance(x, str) else _clients()[0].msgid(x)


def discover_ids(port, group="fn.test", want=300):
    """Message-ids of the newest `want` articles of the first group that answers (a fixture's articles are not ours)."""
    m, _ = _clients()
    c = m.Conn(port, buffered=True)
    try:
        g = c.line("GROUP %s" % group).split()
        if not g or g[0] != b"211":
            lst = c.line("LIST ACTIVE")
            names = []
            if lst[:1] == b"2":
                while True:
                    ln = c.readline()
                    if ln == b".\r\n" or not ln:
                        break
                    names.append(ln.split()[0].decode())
            group = next((n for n in names if n.startswith("fn.")), names[0] if names else group)
            g = c.line("GROUP %s" % group).split()
        hi = int(g[3])
        lo = max(int(g[2]), hi - want + 1)
        if c.line("OVER %d-%d" % (lo, hi))[:3] != b"224":
            return [], group
        ids = []
        while True:
            ln = c.readline()
            if ln == b".\r\n" or not ln:
                break
            f = ln.decode("latin-1").rstrip("\r\n").split("\t")
            if len(f) >= 5 and f[4].startswith("<"):
                ids.append(f[4])
        return ids, group
    finally:
        c.close()


def read_dot(conn):
    n = 0
    while True:
        line = conn.readline()
        if not line:
            raise CellError("connection closed inside a multi-line reply")
        n += len(line)
        if line == b".\r\n":
            return n


def timed_cmd(conn, text):
    t0 = time.perf_counter()
    reply = conn.line(text)
    octets = read_dot(conn) if reply[:1] == b"2" else 0
    return time.perf_counter() - t0, reply, octets


# ---------------------------------------------------------------- phases

class Run:
    """One cell run on one node: phases in order, result rewritten after each."""

    def __init__(self, node, spec, ctr, args):
        self.node, self.spec, self.ctr, self.args = node, spec, ctr, args
        self.errors = []

    def conn(self):
        """A connection, or None when the node refused it (a non-200 greeting, counted by name)."""
        m, _ = _clients()
        c = m.Conn(self.node.port, buffered=True)
        if c.greeting[:3] != b"200":
            with self.ctr.lock:
                self.ctr.refusals["conn-" + refusal_name(c.greeting)] += 1
            with contextlib.suppress(Exception):
                c.sock.close()
            return None
        return c

    # post -------------------------------------------------------------
    def phase_post(self, ph):
        conns = ph.get("connections", 1)
        octets = ph["octets"]
        count = ph.get("count")
        stop_at = time.monotonic() + ph["duration_s"] if "duration_s" in ph else None
        lat = [[] for _ in range(conns)]
        remaining = itertools.count()
        lock = threading.Lock()
        errs = []

        def worker(k):
            try:
                c = self.conn()
                if c is None:
                    return
                while True:
                    if count is not None:
                        with lock:
                            if next(remaining) >= count:
                                break
                    elif time.monotonic() >= stop_at:
                        break
                    d = post_one(c, self.ctr, octets)
                    if d is not None:
                        lat[k].append(d)
                c.close()
            except Exception as e:      # noqa: BLE001 - recorded, not hidden
                errs.append(repr(e))
        bg_stop, bg_n, bg_errs = threading.Event(), itertools.count(), []

        def background():
            try:
                c = self.conn()
                if c is None:
                    return
                known = list(self.ctr.known) or list(range(self.args_known_floor()))
                j = 0
                while known and not bg_stop.is_set():
                    timed_cmd(c, "ARTICLE %s" % mid(known[(j * 7919) % len(known)]))
                    next(bg_n)
                    j += 1
                c.close()
            except Exception as e:      # noqa: BLE001
                bg_errs.append(repr(e))
        t0 = time.monotonic()
        bg = [threading.Thread(target=background) for _ in range(ph.get("background_readers", 0))]
        ths = [threading.Thread(target=worker, args=(k,)) for k in range(conns)]
        for t in bg + ths:
            t.start()
        for t in ths:
            t.join()
        bg_stop.set()
        for t in bg:
            t.join()
        secs = time.monotonic() - t0
        allv = [d for v in lat for d in v]
        errs += bg_errs
        out = {"background_readers": ph.get("background_readers", 0), "cmd": {"POST": res_mod.lat_stats(allv)}, "rate": {"post_per_s": round(len(allv) / secs, 3) if secs else None},
               "connections": conns, "octets": octets}
        if errs:
            out["errors"] = errs
            self.errors += errs
        return out

    # read -------------------------------------------------------------
    def phase_read(self, ph):
        readers, cmd = ph["readers"], ph.get("cmd", "ARTICLE")
        count = ph.get("count")
        stop = threading.Event()
        known = list(self.ctr.known) or list(range(self.args_known_floor()))
        if not known:
            raise CellError("no articles to read: the store is empty and nothing was POSTed")
        lat = [[] for _ in range(readers)]
        bad = collections.Counter()
        done = itertools.count()
        errs = []
        lock = threading.Lock()

        def reader(k):
            try:
                c = self.conn()
                if c is None:
                    return
                win = None
                if cmd == "OVER40":
                    g = c.line("GROUP fn.test").split()
                    hi = int(g[3]) if len(g) >= 4 else 0
                    win = (max(1, hi - 39), hi)
                j = k
                while not stop.is_set():
                    if count is not None:
                        with lock:
                            if next(done) >= count:
                                break
                    if cmd == "OVER40":
                        d, rep, _ = timed_cmd(c, "OVER %d-%d" % win)
                        good = rep.startswith(b"224")
                    else:
                        d, rep, _ = timed_cmd(c, "ARTICLE %s" % mid(known[(j * 7919) % len(known)]))
                        good = rep.startswith(b"220")
                    j += readers if readers > 1 else 1
                    if good:
                        lat[k].append(d)
                    else:
                        bad[refusal_name(rep)] += 1
                c.close()
            except Exception as e:      # noqa: BLE001
                errs.append(repr(e))
        poster = ph.get("poster")
        plat, ptimes = [], []

        def poster_loop():
            try:
                c = self.conn()
                if c is None:
                    return
                gap = 1.0 / poster["rate_per_s"]
                t0 = time.perf_counter()
                k = 0
                while not stop.is_set():
                    intended = t0 + k * gap          # open loop: latency from the intended send time
                    now = time.perf_counter()
                    if intended > now:
                        time.sleep(intended - now)
                    d = post_one(c, self.ctr, poster["octets"])
                    if d is not None:
                        plat.append(time.perf_counter() - intended)
                    k += 1
                c.close()
            except Exception as e:      # noqa: BLE001
                errs.append(repr(e))
        t0 = time.monotonic()
        ths = [threading.Thread(target=reader, args=(k,)) for k in range(readers)]
        pth = threading.Thread(target=poster_loop) if poster else None
        for t in ths + ([pth] if pth else []):
            t.start()
        if "duration_s" in ph:
            time.sleep(ph["duration_s"])
            stop.set()
        for t in ths:
            t.join()
        stop.set()
        if pth:
            pth.join()
        secs = time.monotonic() - t0
        allv = [d for v in lat for d in v]
        op = "OVER40" if cmd == "OVER40" else "ARTICLE"
        out = {"cmd": {op: res_mod.lat_stats(allv)}, "rate": {op.lower() + "_per_s": round(len(allv) / secs, 2) if secs else None},
               "readers": readers}
        if plat:
            out["cmd"]["POST"] = res_mod.lat_stats(plat)
        if bad:
            out["bad_replies"] = dict(bad)
        if errs:
            out["errors"] = errs
            self.errors += errs
        return out

    def args_known_floor(self):
        return self.spec.get("_preloaded", 0)

    def phase_commands(self, ph):
        """Per-command latency and owner CPU per command on one connection: the standing T-CMD row."""
        m, _ = _clients()
        reps = ph.get("reps", 300)
        known = list(self.ctr.known) or list(range(self.args_known_floor()))
        if not known:
            raise CellError("no articles for the command row")
        c = self.conn()
        g = c.line("GROUP fn.test").split()
        hi = int(g[3]) if len(g) >= 4 else 0
        lo = max(1, hi - 39)
        pick = lambda k: mid(known[(k * 7919) % len(known)])
        plan = {"GROUP": lambda k: ("GROUP fn.test", False), "OVER40": lambda k: ("OVER %d-%d" % (lo, hi), True),
                "STAT": lambda k: ("STAT %s" % pick(k), False), "HEAD": lambda k: ("HEAD %s" % pick(k), True),
                "LIST": lambda k: ("LIST", True)}
        out, cpu_ms, bad = {}, {}, {}
        for name, mk in plan.items():
            ts, c0 = [], (proc_snapshot(self.node.pid) or {}).get("cpu_s")
            for k in range(reps):
                text, multi = mk(k)
                t0 = time.perf_counter()
                rep = c.line(text)
                if multi and rep[:1] == b"2":
                    read_dot(c)
                ts.append(time.perf_counter() - t0)
                if rep[:1] != b"2":
                    bad[name] = refusal_name(rep)
            c1 = (proc_snapshot(self.node.pid) or {}).get("cpu_s")
            out[name] = res_mod.lat_stats(ts)
            if c0 is not None and c1 is not None:
                cpu_ms[name] = round((c1 - c0) * 1000.0 / reps, 3)
        c.close()
        ts = []
        c0 = (proc_snapshot(self.node.pid) or {}).get("cpu_s")
        for _ in range(reps):
            t0 = time.perf_counter()
            cc = m.Conn(self.node.port, buffered=True)
            ts.append(time.perf_counter() - t0)
            cc.sock.close()
        c1 = (proc_snapshot(self.node.pid) or {}).get("cpu_s")
        out["greeting"] = res_mod.lat_stats(ts)
        if c0 is not None and c1 is not None:
            cpu_ms["greeting"] = round((c1 - c0) * 1000.0 / reps, 3)
        return {"cmd": out, "cpu_ms_per_op_by_cmd": cpu_ms, "bad_replies": bad or None}

    # hold / idle --------------------------------------------------------
    def phase_hold(self, ph):
        m, _ = _clients()
        held = []
        admitted = 0
        for k in ph["steps"]:
            for _ in range(k):
                held.append(m.Conn(self.node.port))
            time.sleep(ph.get("step_settle_s", 2))
        admitted = sum(1 for c in held if c.greeting[:3] == b"200")
        refused = collections.Counter(refusal_name(c.greeting) for c in held if c.greeting[:3] != b"200")
        if ph.get("close", True):
            for c in held:
                with contextlib.suppress(Exception):
                    c.close()
        return {"connections": len(held), "admitted_connections": admitted, "connection_refusals": dict(refused)}

    def phase_idle(self, ph):
        time.sleep(ph["seconds"])
        return {}

    # article sizes ------------------------------------------------------
    def phase_article_sizes(self, ph):
        m, r = _clients()
        sizes_ms, per_size, refused = {}, {}, {}
        c = self.conn()
        for kib in ph["sizes_kib"]:
            ids = []
            for _ in range(ph["reps"]):
                i = self.ctr.next_id()
                first = c.line("POST")
                if not first.startswith(b"340"):
                    self.ctr.refuse(first)
                    refused[str(kib)] = refusal_name(first)
                    break
                c.stream.write(r.article(i, kib * 1024) + b".\r\n")
                final = c.readline()
                if final.startswith(b"240"):
                    self.ctr.ok(i)
                    ids.append(i)
                else:
                    self.ctr.refuse(final)
                    refused[str(kib)] = refusal_name(final)
                    break
            if len(ids) < ph["reps"]:
                continue
            ts = []
            for i in ids:
                d, rep, octets = timed_cmd(c, "ARTICLE %s" % m.msgid(i))
                if rep.startswith(b"220"):
                    ts.append(d)
            if ts:
                per_size[str(kib)] = res_mod.lat_stats(ts)
                sizes_ms[str(kib)] = round(sorted(ts)[len(ts) // 2] * 1000, 3)
        c.close()
        return {"sizes_ms": sizes_ms, "per_size": per_size, "refused_sizes": refused,
                "cmd": {"ARTICLE": res_mod.lat_stats([v / 1000 for v in sizes_ms.values()])}}

    # reopen / checkpoint / verify ----------------------------------------
    def phase_reopen(self, ph):
        self.node.stop()
        s = self.node.start()
        return {"open_s": round(s, 3)}

    def phase_checkpoint(self, ph):
        self.node.stop()
        rc, secs, tail = self.node.verb("checkpoint")
        if rc != 0:
            raise CellError("store checkpoint exit %d: %s" % (rc, tail))
        return {"checkpoint_s": round(secs, 3), "checkpoint_report": tail.strip()[-200:]}

    def phase_verify(self, ph):
        m, r = _clients()
        c = self.conn()
        mism, first_bad = 0, None
        ids = sorted(self.ctr.known)[:ph["count"]]
        for i in ids:
            c.line("ARTICLE %s" % m.msgid(i))
            body = b""
            while True:
                line = c.readline()
                if line == b".\r\n":
                    break
                body += line
            want = r.article(i, self.spec["phases"][0]["octets"])
            if body != want:
                mism += 1
                first_bad = first_bad or {"id": i, "got_octets": len(body), "want_octets": len(want)}
        c.close()
        return {"verified": len(ids), "mismatches": mism, "first_mismatch": first_bad}

    def phase_census(self, ph):
        """SBCL's accounting of the dynamic space (the one-off w15-census.lisp hook), raw and after a full GC."""
        d = Path(self.node.work) / "census"
        for f in ("done", "go", "census.txt", "census.err"):
            with contextlib.suppress(OSError):
                (d / f).unlink()
        (d / "go").write_text("")
        t0 = time.monotonic()
        while not (d / "done").exists():
            if time.monotonic() - t0 > 900:
                raise CellError("census hook did not finish in 900 s (is the hook loaded?)")
            time.sleep(0.5)
        keep = Path(self.args.out) / ("census-%s.txt" % re.sub(r"[^A-Za-z0-9]+", "_", self.cell_id))
        shutil.copy(d / "census.txt", keep) if (d / "census.txt").exists() else None
        err = (d / "census.err").read_text() if (d / "census.err").exists() else None
        return {"census_file": keep.name, "census": cells_mod.parse_census((d / "census.txt").read_text("utf-8", "replace"))
                if (d / "census.txt").exists() else None, "census_error": err, "census_s": round(time.monotonic() - t0, 1)}

    def phase_publish(self, ph):
        """Stop the owner, publish a checkpoint offline: wall, CPU, octets in files it touched, component sizes."""
        import resource
        self.node.stop()
        before = store_files(self.node.store)
        r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        rc, secs, tail = self.node.verb("checkpoint")
        r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        if rc != 0:
            raise CellError("store checkpoint exit %d: %s" % (rc, tail))
        after = store_files(self.node.store)
        touched = sum(v[0] for k, v in after.items() if before.get(k) != v)
        return {"publish_wall_s": round(secs, 3),
                "publish_cpu_s": round((r1.ru_utime + r1.ru_stime) - (r0.ru_utime + r0.ru_stime), 3),
                "publish_touched_octets": touched, "store_octets_before": sum(v[0] for v in before.values()),
                "store_octets_after": sum(v[0] for v in after.values()),
                "sizes_before": components(before), "sizes_after": components(after), "checkpoint_report": tail.strip()[-200:]}

    def phase_fresh_start(self, ph):
        """L-FRESH (absorbed from tools/load_fresh_start.py): per limit, a fresh store, the node started the way an
        installed node starts (packaging/fn: the image's heap probe, which may refuse the profile on this machine)
        inside `systemd-run --user --scope -p MemoryMax=LIMIT -p MemorySwapMax=0`, then one POST and one ARTICLE."""
        from tests import native_harness as h
        image = self.node.target.path
        results = []
        for limit in ph["limits_mb"]:
            d = Path(self.node.work) / ("fresh-%d" % limit)
            shutil.rmtree(d, ignore_errors=True)
            d.mkdir(parents=True)
            node = Node(self.node.target, d, self.node.flags, self.node.groups, self.node.env["SBCL_USER_ARGS"], [],
                        d / "gc.log", {}, 1.0, "declared")
            node.init()
            env = h.environment({"FN_NATIVE_HOST": None})
            scope = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=%dM" % limit, "-p", "MemorySwapMax=0"]
            core = Path(str(image) + ".core")
            boot = (core.stat().st_size + 1048575) // 1048576 + 128 if core.exists() else 256
            probe = subprocess.run(scope + [str(image), "--fn", "heap", "--", "operator", str(node.config), "run"],
                                   env=dict(env, SBCL_USER_ARGS="--dynamic-space-size %d" % boot), capture_output=True, timeout=300)
            r = {"limit_mb": limit, "heap_probe": {"exit": probe.returncode, "stdout": probe.stdout.decode("utf-8", "replace").strip(),
                                                  "stderr_tail": probe.stderr[-400:].decode("utf-8", "replace")}}
            errp, outp = d / "run.stderr", d / "run.stdout"
            argv = scope + [str(h.installed_launcher(image)), "operator", str(node.config), "run"]
            r["argv"] = argv
            with open(errp, "wb") as err, open(outp, "wb") as so:
                proc = subprocess.Popen(argv, env=env, stdout=so, stderr=err, cwd=str(ROOT))
            t0, listening = time.monotonic(), False
            while time.monotonic() - t0 < 120:
                if b"LISTENING " in outp.read_bytes():
                    listening = True
                    break
                if proc.poll() is not None:
                    break
                time.sleep(0.2)
            r["seconds_to_listening_or_exit"] = round(time.monotonic() - t0, 2)
            r["listening"] = listening
            try:
                if listening:
                    r["at_listening_kib"] = (proc_snapshot(proc.pid) or {}).get("vmrss")
                    node.pid = proc.pid
                    c = None
                    try:
                        m, rm = _clients()
                        c = m.Conn(node.port, buffered=True)
                        ctr = Counters()
                        d_post = post_one(c, ctr, 2048)
                        d_art, rep, octets = timed_cmd(c, "ARTICLE %s" % m.msgid(0))
                        r["served"] = d_post is not None and rep.startswith(b"220")
                        r["post_ms"], r["article_ms"] = (d_post or 0) * 1000, d_art * 1000
                    except Exception as e:      # noqa: BLE001 - the failure is the result
                        r["client_error"] = repr(e)
                        r["served"] = False
                    finally:
                        if c is not None:
                            with contextlib.suppress(Exception):
                                c.close()
                    snap = proc_snapshot(proc.pid) or {}
                    r["after_kib"] = {k: snap.get(k) for k in ("vmrss", "hwm", "anon", "file")}
            finally:
                if proc.poll() is None:
                    proc.terminate()                    # SIGTERM to the PID this driver started
                    try:
                        proc.wait(timeout=90)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait()
                        r["needed_sigkill"] = True
                r["exit_code"] = proc.returncode
            r["stdout_tail"] = outp.read_bytes()[-2000:].decode("utf-8", "replace")
            r["stderr_tail"] = errp.read_bytes()[-2000:].decode("utf-8", "replace")
            r["verdict"] = "serves" if r.get("served") else ("refused-or-exited" if not listening else "listening-but-no-service")
            if not r.get("served"):
                line = next((l for l in (r["stderr_tail"] + "\n" + r["heap_probe"]["stderr_tail"] + "\n" + r["heap_probe"]["stdout"]).splitlines()
                             if "refused" in l), r["verdict"])
                self.ctr.refusals["fresh-%d-%s" % (limit, refusal_name(line.encode()))] += 1
            results.append(r)
        return {"results": results}

    def phase_prof(self, ph):
        """T-CALLS / T-ALLOC / T-SYNC through E's deterministic hook (prof2.lisp, one window per process): per operation, a
        restarted owner, `start`, K commands, `stop`; the hook reports host-to-ACL2 calls (outermost fnn-call), the owner's own
        fnn-durable-barrier / fnn-log-fdatasync count and wall, bytes consed and GC time, all process-wide.  The hook costs
        about 40% of wall: these rows are counts and bytes, not latency, and are labelled hooked."""
        m, r = _clients()
        K = ph.get("reps", 100)
        pdir = Path(self.node.work) / "prof"
        ids = {}
        c = self.conn()
        for kib in ph["article_kib"]:
            ids[kib] = []
            for _ in range(3):
                i = self.ctr.next_id()
                c.line("POST")
                c.stream.write(r.article(i, kib * 1024) + b".\r\n")
                if c.readline().startswith(b"240"):
                    ids[kib].append(i)
                    self.ctr.ok(i)
        c.close()
        ops = [("POST_2k", None)] + [("GROUP", None)] + [("ARTICLE_%dk" % k, k) for k in ph["article_kib"]]
        res = {}
        for name, kib in ops:
            self.node.stop()
            shutil.rmtree(pdir, ignore_errors=True)
            pdir.mkdir(parents=True)
            self.node.env["XL_PROF_DIR"] = str(pdir)
            self.node.start()
            time.sleep(2)
            c = self.conn()
            cpu0 = (proc_snapshot(self.node.pid) or {}).get("cpu_s")
            (pdir / "start").write_text("")
            time.sleep(0.5)
            t0 = time.perf_counter()
            for k in range(K):
                if name == "POST_2k":
                    post_one(c, self.ctr, 2048)
                elif name == "GROUP":
                    c.line("GROUP fn.test")
                else:
                    timed_cmd(c, "ARTICLE %s" % mid(ids[kib][k % len(ids[kib])]))
            wall = time.perf_counter() - t0
            (pdir / "stop").write_text("")
            t1 = time.monotonic()
            while not (pdir / "done").exists():
                if time.monotonic() - t1 > 120:
                    raise CellError("prof hook did not finish (is prof2.lisp loaded?)")
                time.sleep(0.2)
            cpu1 = (proc_snapshot(self.node.pid) or {}).get("cpu_s")
            c.close()
            keep = Path(self.args.out) / ("prof-%s-%s.txt" % (re.sub(r"[^A-Za-z0-9]+", "_", self.cell_id), name))
            shutil.copy(pdir / "timing.txt", keep)
            res[name] = cells_mod.parse_prof((pdir / "timing.txt").read_text(), K)
            res[name]["hooked_wall_ms_per_cmd"] = round(wall * 1000 / K, 3)
            if cpu0 is not None and cpu1 is not None:
                res[name]["hooked_cpu_ms_per_cmd"] = round((cpu1 - cpu0) * 1000 / K, 3)
        return {"prof": res, "reps": K, "hooked": True}

    def phase_conn_capacity(self, ph):
        """Per preset: the decided default cap (no key in fn.toml), then the largest `[server] max_connections` the image
        admits (doubling, then 3 bisection steps), the RSS per held connection and the refusal line past the cap."""
        m, _ = _clients()
        data = self.args.data
        image_node = self.node
        out = {}

        def trial(preset, mc):
            d = Path(image_node.work) / ("cc-%s-%s" % (preset, mc or "default"))
            shutil.rmtree(d, ignore_errors=True)
            d.mkdir(parents=True)
            node = Node(image_node.target, d, wl.init_flags(data, preset), ["fn.test"], image_node.env["SBCL_USER_ARGS"], [],
                        d / "gc.log", {}, 1.0, "decided", mc)
            node.init()
            t = {"max_connections": mc, "preset": preset}
            try:
                try:
                    node.start(180)
                except CellError as e:
                    t.update(started=False, refusal=str(e)[-300:])
                    return t
                if mc:
                    t["policy_set"] = node.policy_set("exposure-connections", mc)
                time.sleep(1)
                base = (proc_snapshot(node.pid) or {}).get("vmrss")
                want = (mc or 32) + 1
                held, greetings = [], collections.Counter()
                for _ in range(want):
                    c = m.Conn(node.port)
                    held.append(c)
                    greetings[c.greeting[:3].decode("latin-1")] += 1
                admitted = greetings.get("200", 0)
                last = held[-1].greeting.decode("latin-1").strip()
                after = (proc_snapshot(node.pid) or {}).get("vmrss")
                t.update(started=True, admitted=admitted, past_cap_greeting=last if admitted < want else None,
                         vmrss_base_kib=base, vmrss_held_kib=after,
                         kib_per_conn=round((after - base) / admitted, 2) if admitted and base and after else None,
                         heap=node.decided)
                for c in held:
                    with contextlib.suppress(Exception):
                        c.sock.close()
            finally:
                node.stop(60)
            return t
        for preset in ph["presets"]:
            trials = [trial(preset, None)]
            good, bad, mc = None, None, 64
            while mc <= ph.get("max_try", 4096):
                t = trial(preset, mc)
                trials.append(t)
                if t.get("started") and t.get("admitted") == mc:
                    good = mc
                    mc *= 2
                else:
                    bad = mc
                    break
            for _ in range(3):
                if good is None or bad is None or bad - good <= 1:
                    break
                mid_ = (good + bad) // 2
                t = trial(preset, mid_)
                trials.append(t)
                if t.get("started") and t.get("admitted") == mid_:
                    good = mid_
                else:
                    bad = mid_
            out[preset] = {"default_cap": trials[0].get("admitted"), "largest_ok": good, "first_refused": bad, "trials": trials}
            for t in trials:
                if t.get("refusal"):
                    self.ctr.refusals["conn-capacity-%s-%s" % (preset, refusal_name(t["refusal"].encode()))] += 1
        return {"capacity": out}

    def phase_unimplemented(self, ph):
        return {"status": "not-implemented", "reason": ph["reason"]}


# ---------------------------------------------------------------- stores

def preload(node, run, n, octets, budget_s):
    """POST n articles (in order, 2 connections) so a store of n exists; seconds taken."""
    t0 = time.monotonic()
    ph = {"count": n, "octets": octets, "connections": 2}
    out = run.phase_post(ph)
    if run.ctr.admitted < n:
        raise CellError("preload admitted %d of %d POSTs (refusals %s): the preset cannot hold this store"
                        % (run.ctr.admitted, n, dict(run.ctr.refusals)))
    if time.monotonic() - t0 > budget_s:
        raise CellError("preload of %d exceeded its %d s budget" % (n, budget_s))
    return out


def prepare_store(node, run, spec, cache_dir, key):
    """Fresh init, or a cached preloaded store copied in; returns {'preloaded': n, ...}."""
    st = spec.get("store")
    if not st or not st.get("preload"):
        node.init()
        node.start()
        return {}
    n, octets = st["preload"], st.get("octets", 2048)
    fixture = Path(run.args.fixtures) / st["fixture"].format(N=n) / "store" if st.get("fixture") else None
    if fixture is not None and fixture.is_dir():
        shutil.copytree(fixture, node.store, symlinks=True)
        node.write_config()
        lock = node.store / "writer.lock"
        lock.touch()
        lock.chmod(0o600)
        node.start()
        ids, group = discover_ids(node.port)
        if not ids:
            raise CellError("fixture %s: no article ids discoverable through OVER" % fixture)
        run.ctr.known = ids
        run.ctr._ids = itertools.count(10 ** 6)       # our own POSTs never collide with the fixture's ids
        run.spec["_group"] = group
        return {"preloaded": n, "source": "fixture %s" % fixture, "group": group}
    cached = Path(cache_dir) / ("%s-%d-%d" % (key, n, octets))
    if cached.is_dir() and (cached / "store").is_dir():
        shutil.copytree(cached / "store", node.store, symlinks=True)
        node.write_config()
        lock = node.store / "writer.lock"
        lock.touch()
        lock.chmod(0o600)
        node.start()
        run.ctr._ids = itertools.count(n)
        run.ctr.known = list(range(n))
        return {"preloaded": n, "source": "cache %s" % cached.name}
    node.init()
    node.start()
    t0 = time.monotonic()
    preload(node, run, n, octets, st.get("budget_s", 3600))
    secs = time.monotonic() - t0
    node.stop()
    with contextlib.suppress(OSError):
        cached.mkdir(parents=True, exist_ok=True)
        shutil.copytree(node.store, cached / "store", symlinks=True)
    node.start()
    run.ctr.refusals.clear()
    run.ctr.admitted = run.ctr.refused = 0
    return {"preloaded": n, "preload_s": round(secs, 1), "source": "POSTs"}


# ---------------------------------------------------------------- one cell

def run_cell(cell, target, arm, rep, args, data, res, write, sub=False):
    spec = cell.spec
    label = "%s-%s-%s-r%d" % (re.sub(r"[^A-Za-z0-9]+", "_", cell.id), target.kind, arm or "x", rep)
    work = Path(args.work) / label
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    use_hook = bool(arm) or args.gc_hook
    hooks = [HOOK] if use_hook else []
    env_extra = {"FN_LOAD_IDLE_GC": "off"} if arm == "A" else {}
    if spec.get("prof"):
        hooks.append(PROF_HOOK)
        env_extra["XL_PROF_DIR"] = str(work / "prof")
    if spec.get("census"):
        hooks.append(CENSUS_HOOK)
        (work / "census").mkdir()
        env_extra["FN_LOAD_CENSUS_DIR"] = str(work / "census")
    node = Node(target, work, wl.init_flags(data, spec["preset"]), spec["groups"], args.sbcl_user_args or data["sbcl_user_args"],
                hooks, work / "gc.log", env_extra, spec.get("sampler_s", 1.0),
                spec.get("heap", "decided"), None)
    ctr = Counters()
    run = Run(node, spec, ctr, args)
    run.cell_id = cell.id
    cr = {"trace": None, "cell": cell.id, "workload": cell.workload, "target": target.kind, "arm": arm, "rep": rep,
          "preset": spec["preset"], "flags": node.flags, "git": args.rev, "status": "running",
          "image": {"path": str(target.path), "core_sha256": target.core_sha256, "tree_sha": target.tree_sha},
          "hook": ("+".join(h.name for h in hooks) + (" idle-gc-off" if arm == "A" else "")) if hooks else None,
          "policy": spec.get("policy"),
          "launch": "%s --fn operator %s run (SBCL_USER_ARGS=%r)" % (node.launcher, node.config, node.env["SBCL_USER_ARGS"]),
          "started_utc": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "phases": [],
          "box": {"name": args.box, "cores": len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count(),
                  "loadavg_start": loadavg(), "arc_bytes_start": arc_size(),
                  "pinned": sorted(os.sched_getaffinity(0)) if args.cores else None,
                  "busy_cores_set": ("%d-%d" % (min(os.sched_getaffinity(0)), max(os.sched_getaffinity(0)))) if args.cores else None,
                  "busy_cores_start": busy_cores(sorted(os.sched_getaffinity(0))) if args.cores else None, "fs": fs_type(work)},
          "loopback_only": True}
    if sub:
        cr["sub"] = True
    res["cells"].append(cr)
    write()
    t_cell = time.monotonic()
    gc_seen = [0, 0.0]

    def gc_delta():
        n, last = 0, 0
        with contextlib.suppress(OSError):
            for line in node.gc_log.read_text().splitlines():
                p = line.split()
                if len(p) == 4 and p[0] == "GC":
                    n, last = n + 1, int(p[2])
        d = {"count": n - gc_seen[0], "ms": round((last - gc_seen[1]) / 1000.0, 1)}
        gc_seen[0], gc_seen[1] = n, last
        return d
    try:
        cr["heap"] = {"mode": node.heap_mode}
        cr["site"] = site_probe(work)
        write()
        if spec.get("own_nodes"):        # the phases start their own nodes (fresh-start)
            cr["store"] = {}
        else:
            info = prepare_store(node, run, spec, args.cache, (target.core_sha256 or "x")[:12] + "-" + spec["preset"])
            cr["store"] = info
            cr["heap"]["sbcl_user_args"] = node.env["SBCL_USER_ARGS"]
            if spec.get("policy"):
                cr["policy"] = {k: node.policy_set(k, v) for k, v in spec["policy"].items()}
            spec["_preloaded"] = info.get("preloaded", 0)
            node.sampler.start()
            time.sleep(spec.get("settle_s", 3))
            cr["open_s"] = round(node.open_s, 3)
            snap = proc_snapshot(node.pid)
            cr["phases"].append({"name": "open", "kind": "open", "seconds": round(node.open_s, 3), "open_s": round(node.open_s, 3),
                                 "open_cpu_s": getattr(node, "open_cpu_s", None),
                                 "mem": {k: snap[k] for k in ("vmrss", "hwm", "anon", "file")}, "gc": gc_delta() if use_hook else None})
        write()
        for ph in spec["phases"]:
            before = proc_snapshot(node.pid) if node.pid else None
            cnt0 = (ctr.admitted, ctr.refused, dict(ctr.refusals))
            node.sampler.take_peak()
            t0 = time.monotonic()
            out = getattr(run, "phase_" + ph["kind"])(ph)
            secs = time.monotonic() - t0
            after = proc_snapshot(node.pid) if node.pid else None
            peak = node.sampler.take_peak()
            rec = {"name": ph["name"], "kind": ph["kind"], "seconds": round(secs, 3), "measure": bool(ph.get("measure")),
                   "status": out.pop("status", "ok")}
            rec.update(out)
            rec["counts"] = {"admitted": ctr.admitted - cnt0[0], "refused": ctr.refused - cnt0[1]}
            if after:
                rec["mem"] = {k: after[k] for k in ("vmrss", "hwm", "anon", "file", "pss", "threads")}
                rec["mem"]["peak_vmrss"], rec["mem"]["peak_anon"] = peak["vmrss"], peak["anon"]
                rec["io"] = {"read_bytes": (after["io"].get("read_bytes", 0) - ((before or {}).get("io") or {}).get("read_bytes", 0)),
                             "write_bytes": (after["io"].get("write_bytes", 0) - ((before or {}).get("io") or {}).get("write_bytes", 0))} if before and before["cpu_s"] is not None and ph["kind"] != "reopen" else None
                rec["cpu_s"] = round(after["cpu_s"] - before["cpu_s"], 2) if before and after.get("cpu_s") is not None and ph["kind"] != "reopen" else None
            ops = sum((st or {}).get("n", 0) for st in (rec.get("cmd") or {}).values())
            if ops and rec.get("cpu_s") is not None:
                rec["ops"], rec["cpu_ms_per_op"] = ops, round(rec["cpu_s"] * 1000.0 / ops, 3)
            rec["gc"] = gc_delta() if use_hook else None
            rec["load"] = loadavg()
            rec["arc_bytes"] = arc_size()
            cr["phases"].append(rec)
            cr["refusals"] = dict(ctr.refusals)
            cr["admitted"] = {"admitted": ctr.admitted, "refused": ctr.refused}
            write()
        if args.cores:
            cr["box"]["busy_cores_end"] = busy_cores(sorted(os.sched_getaffinity(0)))
        cr["status"] = "complete" if not run.errors else "complete-with-errors"
    except Exception as e:      # noqa: BLE001 - the cell's own failure is a result
        cr["status"] = "error"
        cr["error"] = "%s: %s" % (type(e).__name__, e)
        import traceback
        cr["traceback"] = traceback.format_exc()[-900:]
    finally:
        node.sampler.stop_ev.set()
        with contextlib.suppress(Exception):
            cr["exit_code"] = node.stop()
        cr["refusals"] = dict(ctr.refusals)
        cr["admitted"] = {"admitted": ctr.admitted, "refused": ctr.refused}
        cr["seconds"] = round(time.monotonic() - t_cell, 1)
        cr["box"]["loadavg_end"] = loadavg()
        cr["box"]["arc_bytes_end"] = arc_size()
        cr["noisy"] = (cr["box"]["loadavg_start"][0] > 2 * cr["box"]["cores"]) if cr["box"]["cores"] else False
        cr["metrics"], cr["not_measured"] = cells_mod.derive(cell.workload, cr["phases"])
        st = (cr.get("site") or {}).get("write4k_fdatasync") or {}
        if st.get("p50_ms") is not None:
            cr["metrics"]["site.fdatasync_p50_ms"], cr["metrics"]["site.fdatasync_p99_ms"] = st["p50_ms"], st.get("p99_ms")
            if st.get("p99_ms") is None:
                cr["not_measured"]["site.fdatasync_p99_ms"] = "fewer than 200 probe samples"
        cr["bars"] = [] if sub else res_mod.judge_cell(cr, args.bars)
        with contextlib.suppress(OSError):
            (work / "samples.json").write_text(json.dumps(node.sampler.series))
        write()
        if not args.keep:
            shutil.rmtree(work / "store", ignore_errors=True)
    return cr


def run_sweep(cell_id, cell, target, arm, rep, args, data, res, write):
    """One cell over several store sizes: a sub-cell per size, then the merged cell that the bars judge."""
    subs = []
    for key in cell.spec["sweep"]:
        sc = wl.resolve("%s@%s" % (cell_id, key), data)
        cr = run_cell(sc, target, arm, rep, args, data, res, write, sub=True)
        subs.append((key, data["stores"][key], cr))
        print(res_mod.print_line(cr, []), flush=True)
    merged = cells_mod.merge_sweep(cell_id, cell.workload, subs)
    merged["bars"] = res_mod.judge_cell(merged, args.bars)
    res["cells"].append(merged)
    write()
    return merged


def cmd_run(args):
    data = wl.load()
    args.bars = res_mod.load_bars()
    args.data = data
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    args.work = args.work or ("/dev/shm/fn-load-%s" % args.label)
    Path(args.work).mkdir(parents=True, exist_ok=True)
    args.cache = args.cache or ("%s/stores" % BOX_BASE)
    args.fixtures = args.fixtures or FIXTURES
    targets = [Target("image", p) for p in args.image] + [Target("fn-core", p) for p in args.fn_core]
    if not targets:
        raise SystemExit("run needs --image and/or --fn-core")
    if args.cores:
        cores = set()
        for part in args.cores.split(","):
            a, _, b = part.partition("-")
            cores |= set(range(int(a), int(b or a) + 1))
        os.sched_setaffinity(0, cores)
    for t in targets:
        if t.tree_sha is None and args.rev:
            t.tree_sha = args.rev           # an fn-core has no TREE_SHA: --rev names the dev sha it was extracted at
    args.rev = args.rev or next((t.tree_sha for t in targets if t.tree_sha), None) or _git_rev()
    res = {"schema": 1, "label": args.label, "rev": args.rev, "cells": [], "evidence": args.evidence}
    status = out / "status"

    def write():
        tmp = out / "result.json.tmp"
        tmp.write_text(json.dumps(res, indent=1, sort_keys=True))
        os.replace(tmp, out / "result.json")
    status.write_text("running\n")
    arms_default = [None]
    rc = 0
    try:
        for cell_id in args.cell.split(","):
            cell = wl.resolve(cell_id, data)
            if args.sweep and cell.spec.get("sweep"):
                data["workloads"][cell.workload]["sweep"] = args.sweep.split(",")
                cell = wl.resolve(cell_id, data)
            arms = args.arms.split(",") if args.arms else ([cell.arm] if cell.arm else arms_default)
            for rep in range(1, args.repeat + 1):
                for target in targets:
                    for arm in arms:
                        if cell.spec.get("sweep") and "@" not in cell_id:
                            cr = run_sweep(cell_id, cell, target, arm, rep, args, data, res, write)
                        else:
                            cr = run_cell(wl.resolve(cell_id, data), target, arm, rep, args, data, res, write)
                        line = res_mod.print_line(cr, cr["bars"])
                        print(line, flush=True)
                        with open(out / "cells.jsonl", "a") as f:
                            f.write(line + "\n")
                        rc = rc or (1 if cr["status"] == "error" else 0)
    finally:
        status.write_text("done rc=%d\n" % rc)
    return rc


def _git_rev():
    with contextlib.suppress(Exception):
        return subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True, timeout=10).stdout.strip() or None
    return None


# ---------------------------------------------------------------- laptop side: box / fetch / list

def ssh(host, script, timeout=120):
    return subprocess.run(["ssh", "-o", "ConnectTimeout=15", host, script], capture_output=True, text=True, timeout=timeout)


def cmd_box(args):
    host = {"hbox": "hbox", "persvati": "persvati"}[args.box]
    base = BOX_BASE
    ship = "%s/ship/%s" % (base, args.label)
    runs = "%s/runs/%s" % (base, args.label)
    ssh(host, "mkdir -p %s/tests %s/books %s/packaging %s/host/native %s/planning/evidence/load/hooks %s" % (ship, ship, ship, ship, ship, runs))
    for src, dst in (("planning/evidence/load/hooks/", "planning/evidence/load/hooks/"), ("packaging/fn", "packaging/"), ("host/native/io.lisp", "host/native/"), ("tools/", "tools/"), ("tests/__init__.py", "tests/"), ("tests/native_harness.py", "tests/"),
                     ("books/outcome-class.lisp", "books/")):
        p = subprocess.run(["rsync", "-a", "--exclude", "__pycache__", str(ROOT / src) + ("/" if src.endswith("/") else ""), "%s:%s/%s" % (host, ship, dst)],
                           capture_output=True, text=True)
        if p.returncode:
            raise SystemExit("rsync %s failed: %s" % (src, p.stderr))
    inner = ["python3", "-m", "tools.load.driver", "run", "--cell", args.cell, "--label", args.label, "--out", runs,
             "--box", args.box, "--repeat", str(args.repeat)]
    for img in args.image:
        inner += ["--image", img]
    for core in args.fn_core:
        inner += ["--fn-core", core]
    for flag, val in (("--arms", args.arms), ("--rev", args.rev), ("--sbcl-user-args", args.sbcl_user_args),
                      ("--work", args.work), ("--cores", args.cores), ("--sweep", getattr(args, "sweep", None))):
        if val:
            inner += [flag, val]
    if args.gc_hook:
        inner.append("--gc-hook")
    if args.box == "hbox":
        wrap = "SWARM_MEM_MAX=%s swarm-build" % args.mem
    else:
        cores = args.cores or "0-11"          # N's plan: timing cells 12-23 (shared with E4), everything else 0-11
        lock = ("flock %s " % shlex.quote(args.flock)) if args.flock else ""
        wrap = "systemd-run --user --scope -p MemoryMax=%s %staskset -c %s" % (args.mem, lock, cores)
        if not args.cores:
            inner += ["--cores", cores]
    script = ("cd %s && %s timeout %d %s > %s/run.log 2>&1 < /dev/null" % (ship, wrap, args.timeout, " ".join(shlex.quote(a) for a in inner), runs))
    launch = "cd %s && setsid nohup sh -c %s > /dev/null 2>&1 < /dev/null & echo $! > %s/pid; cat %s/pid" % (ship, shlex.quote(script), runs, runs)
    p = ssh(host, launch)
    print("started %s on %s, pid file %s/pid: %s" % (args.label, args.box, runs, p.stdout.strip() or p.stderr.strip()))
    return 0


def cmd_fetch(args):
    host = args.box
    runs = "%s/runs/%s" % (BOX_BASE, args.label)
    st = ssh(host, "cat %s/status 2>&1; tail -n 3 %s/run.log" % (runs, runs)).stdout
    print(st.strip())
    if not st.startswith("done") and not args.force:
        print("not done; nothing fetched")
        return 2
    dest = ROOT / "planning" / "evidence" / "load" / ("%s-%s" % (time.strftime("%Y-%m-%d"), args.label))
    dest.mkdir(parents=True, exist_ok=True)
    # Raw output (result.json, cells.jsonl, logs, censuses) stays on the box; only report.md
    # (and anon-by-type.md when present) enters the tree, with the box path written into it.
    # --raw also copies the raw files next to the report (gitignored; never commit them).
    raw = Path(tempfile.mkdtemp(prefix="fn-load-fetch-"))
    p = subprocess.run(["rsync", "-a", "--exclude", "samples.json", "%s:%s/" % (host, runs), str(raw) + "/"], capture_output=True, text=True)
    resf = raw / "result.json"
    if resf.exists():
        note = "\n\nRaw output: %s:%s/ (result.json, cells.jsonl, run.log, census/prof files). Not committed.\n" % (host, runs)
        (dest / "report.md").write_text(res_mod.report(res_mod.read_result(resf), res_mod.load_bars()) + note)
    for extra in ("anon-by-type.md",):
        if (raw / extra).exists():
            shutil.copy(raw / extra, dest / extra)
    if args.raw:
        subprocess.run(["rsync", "-a", str(raw) + "/", str(dest) + "/"])
    shutil.rmtree(raw, ignore_errors=True)
    print("fetched report to %s; raw stays at %s:%s %s" % (dest, host, runs, p.stderr.strip()))
    return 0


def cmd_list(_args):
    data = wl.load()
    for cid, name in sorted(data["cells"].items()):
        print("%-8s %-18s %s" % (cid, name, data["workloads"][name]["about"][:100]))
    return 0


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    def common(q):
        q.add_argument("--cell", required=True, help="comma-separated cell ids (WORKLOAD[@STORE][/variant])")
        q.add_argument("--image", action="append", default=[])
        q.add_argument("--fn-core", action="append", default=[])
        q.add_argument("--arms", default=None, help="idle-GC arms, e.g. A,B (A: idle collection off)")
        q.add_argument("--repeat", type=int, default=1)
        q.add_argument("--gc-hook", action="store_true")
        q.add_argument("--rev", default=None)
        q.add_argument("--sbcl-user-args", default=None)
        q.add_argument("--label", required=True)
        q.add_argument("--box", default="local")
        q.add_argument("--work", default=None, help="work dir (default /dev/shm/fn-load-LABEL: tmpfs); a path on ZFS for the disk rows")
        q.add_argument("--sweep", default=None, help="a sweep cell's store sizes, e.g. 1k,10k,25k,50k")
        q.add_argument("--flock", default=None, help="persvati: hold this lock for the whole run, e.g. /tank/fn/scratch/timing-12-23.lock (one cell per hold)")
        q.add_argument("--cores", default=None, help="pin the run to these cores, e.g. 0-7 (a time cell needs its own cores)")
    r = sub.add_parser("run")
    common(r)
    r.add_argument("--out", required=True)
    r.add_argument("--cache", default=None, help="preloaded-store cache dir")
    r.add_argument("--keep", action="store_true")
    r.add_argument("--fixtures", default=None, help="fixture root (default %s)" % FIXTURES)
    r.add_argument("--evidence", default=None)
    b = sub.add_parser("box")
    common(b)
    b.add_argument("--mem", default="16G")
    b.add_argument("--timeout", type=int, default=7200)
    f = sub.add_parser("fetch")
    f.add_argument("label")
    f.add_argument("--force", action="store_true")
    f.add_argument("--raw", action="store_true", help="also copy the raw files into the (gitignored) evidence dir")
    f.add_argument("--box", default="hbox")
    sub.add_parser("list")
    a = p.parse_args(argv)
    return {"run": cmd_run, "box": cmd_box, "fetch": cmd_fetch, "list": cmd_list}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
