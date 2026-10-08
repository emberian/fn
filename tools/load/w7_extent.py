#!/usr/bin/env python3
"""W7: extent-cache contention.  N concurrent readers on one node, ARTICLE by
message-id over a Zipf(s=1.0) choice of 2,000 stored articles, 90% at about
8 KiB and 10% at about 32 KiB (S changed the 512 KiB tail: no profile admits it).

    run_cell(image, readers, run_index, workdir) -> dict      (load-harness imports this)
    python3 tools/load/w7_extent.py run --image LABEL=PATH [--image LABEL=PATH ...]
        --readers 1,4,16,32 --runs 3 --workdir D --out cells.jsonl [--mode stats|full|none]
    python3 tools/load/w7_extent.py evaluate cells.jsonl

Runs go A B A B ... (one pass per run index over the images), and every cell
prints one `FN_LOAD_RESULT {json}` line.  Python stdlib only.

Store: `init --profile scale` (W7_PROFILE=scale, default) or, as the fallback, `--profile development
--max-transactions 4096` (W7_PROFILE=dev; development's T=128 refuses the 128th POST); deputy L's ruling.  The owner is started at the heap and control stack the image's own probe decides
(`IMAGE --fn heap -- operator CONFIG run`, as tests/native_harness.py decided_launch does); the
decided figures are recorded in every cell.

Readers are processes (no shared GIL) and read replies with large recv()s up
to the dot terminator.  Each cell: fresh store, load (one POST connection),
WARM seconds of the same traffic, then SECONDS measured.  Extent counters and
lock sums come from tools/../planning/evidence/load/2026-10-07-w7/w7hook.lisp,
loaded into the image with --eval before acl2::sbcl-restart (W7_MODE).

preads_per_article: delta of *fnn-extent-stats* misses (physical preads) over
ARTICLEs answered in the window.  hit_ratio: *fnn-extent-stats* hits count
octets served from cache, not articles, so the article hit ratio is reported
as the LOWER BOUND 1 - preads/article (valid when a missing article costs at
least one pread); hits_octets/preads are in `extent_raw`.
"""
import argparse
import bisect
import json
import multiprocessing as mp
import os
import random
import re
import socket
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HOOK = ROOT / "planning/evidence/load/2026-10-07-w7/w7hook.lisp"
N_ARTICLES = int(os.environ.get("W7_ARTICLES", 2000))     # 2000 = W7; 20000 = W7b
CELL_NAME = "W7" if N_ARTICLES == 2000 else "W7b"
SMALL = 8 * 1024         # 90%
LARGE = 32000            # "32 KiB" (S, 2026-10-07): under A = 32768 with headers
ZIPF_S = 1.0
WARM = float(os.environ.get("W7_WARM", 10))
def _cores():
    spec = os.environ.get("W7_CORES", "12-23")
    if spec == "all":
        return []
    lo, hi = spec.split("-")
    return list(range(int(lo), int(hi) + 1))


CORES = _cores()
SECONDS = float(os.environ.get("W7_SECONDS", 30))
if os.environ.get("W7_PROFILE", "scale") == "scale":
    INIT_FLAGS = ["--profile", "scale", "fn.letters", "fn.test"]
    PRESET = "scale"
else:
    INIT_FLAGS = ["--profile", "development", "--max-transactions", "4096", "fn.letters", "fn.test"]
    PRESET = "development+T4096"
LINE = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdef\r\n"


def msgid(i):
    return "<w7-%06d@example.invalid>" % i


def is_large(i):
    return random.Random(i * 7919 + 13).random() < 0.10


def article(i):
    octets = LARGE if is_large(i) else SMALL
    head = ("From: w7@example.invalid\r\nNewsgroups: fn.test\r\nSubject: w7 %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n"
            % (i, msgid(i))).encode("ascii")
    need = octets - len(head)
    body = LINE * (need // len(LINE))
    rest = need - len(body)
    if rest >= 2:
        body += LINE[:rest - 2] + b"\r\n"
    return head + body


def zipf_cdf():
    ranks = list(range(N_ARTICLES))
    random.Random(20261007).shuffle(ranks)       # rank -> article, size independent of rank
    acc, cdf = 0.0, []
    for r in range(N_ARTICLES):
        acc += 1.0 / (r + 1) ** ZIPF_S
        cdf.append(acc)
    return ranks, cdf


class Wire:
    def __init__(self, port):
        self.s = socket.create_connection(("127.0.0.1", port), timeout=30)
        self.s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.buf = b""
        g = self.line()
        if not g.startswith(b"200"):
            self.s.close()
            raise OSError("greeting refused: " + g[:40].decode("ascii", "replace"))

    def line(self):
        while b"\r\n" not in self.buf:
            chunk = self.s.recv(65536)
            if not chunk:
                raise OSError("eof (connection closed by the node)")
            self.buf += chunk
        out, self.buf = self.buf.split(b"\r\n", 1)
        return out

    def article(self, mid):
        self.s.sendall(b"ARTICLE " + mid.encode() + b"\r\n")
        first = self.line()
        if not first.startswith(b"220"):
            return first, 0
        n = 0
        tail = self.buf
        self.buf = b""
        while True:
            if tail.endswith(b"\r\n.\r\n") or tail == b".\r\n":
                return first, n
            chunk = self.s.recv(262144)
            if not chunk:
                raise OSError("eof mid-reply after %d octets (the node closed the connection)" % n)
            n += len(chunk)
            tail = (tail + chunk)[-8:]

    def post(self, data):
        self.s.sendall(b"POST\r\n")
        if not self.line().startswith(b"340"):
            raise SystemExit("POST refused")
        self.s.sendall(data + b".\r\n")
        r = self.line()
        if not r.startswith(b"240"):
            raise SystemExit("POST body: %r" % r)

    def close(self):
        try:
            self.s.sendall(b"QUIT\r\n")
        except OSError:
            pass
        self.s.close()


def reader(port, seed, t_warm_end, t_end, out):
    t_origin = t_end - WARM - SECONDS - 2
    ranks, cdf = zipf_cdf()
    rng = random.Random(seed)
    try:
        w = Wire(port)
    except OSError as e:
        out.send(([], 1, 0, {"connect failed " + str(e)[:40]: 1}, {}))
        return
    lat, errs, nbytes, why, persec = [], 0, 0, {}, {}
    total = cdf[-1]
    while True:
        t0 = time.time()
        if t0 >= t_end:
            break
        mid = msgid(ranks[bisect.bisect_left(cdf, rng.random() * total)])
        p = time.perf_counter()
        try:
            first, n = w.article(mid)
        except OSError as e:
            errs += 1
            key = "OSError " + str(e)[:50]
            why[key] = why.get(key, 0) + 1
            persec[int(t0 - t_origin)] = persec.get(int(t0 - t_origin), 0) + 1
            w.s.close()
            try:
                w = Wire(port)
            except OSError:
                break
            continue
        dt = time.perf_counter() - p
        if not first.startswith(b"220"):
            errs += 1
            k = first[:60].decode("ascii", "replace")
            why[k] = why.get(k, 0) + 1
            sec = int(t0 - t_origin)
            persec[sec] = persec.get(sec, 0) + 1
        elif t0 >= t_warm_end:
            lat.append(dt)
            nbytes += n
    w.close()
    out.send((lat, errs, nbytes, why, persec))


def pct(sorted_ms, q):
    return sorted_ms[min(len(sorted_ms) - 1, max(0, int(round(q * len(sorted_ms))) - 1))]


def proc_status(pid):
    try:
        t = Path("/proc/%d/status" % pid).read_text()
        return {k: int(re.search(k + r":\s+(\d+)", t).group(1))
                for k in ("RssAnon", "RssFile", "VmHWM")}
    except (OSError, AttributeError):
        return {}


def read_log(path):
    rows = []
    try:
        for ln in Path(path).read_text().splitlines():
            p = ln.split()
            if len(p) in (7, 10):
                p = p + ["0"] * (10 - len(p))
            if len(p) == 10:
                rows.append([int(x) for x in p])
    except OSError:
        pass
    return rows


def row_at(rows, t_us):
    best = None
    for r in rows:
        if r[0] <= t_us:
            best = r
    return best


def cpu_stat():
    out = {}
    for ln in Path("/proc/stat").read_text().splitlines():
        if ln.startswith("cpu") and ln[3].isdigit():
            f = [int(x) for x in ln.split()[1:]]
            out[int(ln.split()[0][3:])] = (sum(f), f[3] + f[4])      # total, idle+iowait
    return out


def busy(a, b):
    return {c: round(1.0 - (b[c][1] - a[c][1]) / max(1, b[c][0] - a[c][0]), 3) for c in sorted(a) if c in b}


def wait_quiet(limit=1500):
    """Before a cell: the cores must read quiet (5 s mean busy < 0.15, max < 0.5) or the cell waits."""
    if not CORES:
        return None
    t0 = time.time()
    while True:
        a = cpu_stat()
        time.sleep(5)
        b = busy(a, cpu_stat())
        v = [b[c] for c in CORES if c in b]
        mean, mx = sum(v) / len(v), max(v)
        if (mean < 0.15 and mx < 0.5) or time.time() - t0 > limit:
            return {"mean": round(mean, 3), "max": mx, "waited_s": round(time.time() - t0), "quiet": mean < 0.15 and mx < 0.5}


def _tree_sha(image):
    f = Path(image).resolve().parent / "TREE_SHA"
    try:
        return f.read_text().strip()
    except OSError:
        return None


def git_head():
    if os.environ.get("W7_GIT"):
        return os.environ["W7_GIT"]
    try:
        return subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
    except OSError:
        return None


def launcher(image, workdir, mode):
    """A copy of the saved launcher that loads the hook before sbcl-restart."""
    text = Path(image).read_text()
    new = text.replace("--eval '(acl2::sbcl-restart)'",
                       "--eval '(load \"%s\")' --eval '(acl2::sbcl-restart)'" % HOOK)
    if new == text:
        raise SystemExit("launcher %s has no sbcl-restart --eval" % image)
    path = Path(workdir) / "launch.sh"
    path.write_text(new)
    path.chmod(0o755)
    return str(path)


def _node_env():
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
    env.pop("ACL2_SYSTEM_BOOKS", None)
    return env


def _decide(image, config, env):
    probe = subprocess.run([str(image), "--fn", "heap", "--", "operator", str(config), "run"],
                           env=env, capture_output=True, text=True, timeout=300)
    hm, sm = re.search(r"heap=(\d+) MB", probe.stdout), re.search(r"stack=(\d+) KB", probe.stdout)
    if not (hm and sm):
        raise SystemExit("heap probe: " + (probe.stdout + probe.stderr)[-400:])
    env["SBCL_USER_ARGS"] = "--dynamic-space-size %sMB --control-stack-size %sKB" % (hm.group(1), sm.group(1))
    return int(hm.group(1)), int(sm.group(1))


def make_template(image, tdir):
    """Init a fresh store and load the 2,000 articles once; later cells copy it (cp -a), so every
    cell of an arm starts from the same bytes.  Returns the store path."""
    tdir = Path(tdir).resolve()
    tdir.mkdir(parents=True, exist_ok=True)
    env = _node_env()
    config = tdir / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n'
                      '[control]\npath = "%s"\n' % (tdir / "store", tdir / "c.sock"))
    init = subprocess.run([str(image), "--fn", "operator", str(config), "init"] + INIT_FLAGS,
                          env=env, capture_output=True, text=True, timeout=900)
    if "accepted operator init" not in init.stdout + init.stderr:
        raise SystemExit("init refused: " + (init.stdout + init.stderr)[-600:])
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]
    config.write_text(config.read_text().replace("port = 1\n", "port = %d\n" % port))
    _decide(image, config, env)
    err = open(tdir / "owner.stderr", "wb")
    proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], env=env,
                            stdout=subprocess.PIPE, stderr=err)
    try:
        while True:
            ln = proc.stdout.readline()
            if ln.startswith(b"LISTENING ") or not ln:
                break
        time.sleep(2)
        w = Wire(port)
        t = time.time()
        for i in range(N_ARTICLES):
            w.post(article(i))
        w.close()
        (tdir / "load_seconds").write_text(str(round(time.time() - t, 1)))
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=300)
        except subprocess.TimeoutExpired:
            proc.kill()
        err.close()
    return tdir / "store"


def run_cell(image, readers, run_index, workdir, mode="stats", label=None, template=None):
    quiet = wait_quiet()
    workdir = Path(workdir).resolve() / ("%s-R%d-run%d" % (label or "img", readers, run_index))
    workdir.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
    env.pop("ACL2_SYSTEM_BOOKS", None)
    log = workdir / "w7.log"
    if mode != "none":
        env["W7_LOG"], env["W7_MODE"] = str(log), mode
        exe = launcher(image, workdir, mode)
    else:
        exe = str(image)
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        port = probe.getsockname()[1]
    config = workdir / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (workdir / "store", port, workdir / "c.sock"))
    if template:
        subprocess.run(["cp", "-a", str(template), str(workdir / "store")], check=True)
    else:
        init = subprocess.run([exe, "--fn", "operator", str(config), "init"] + INIT_FLAGS,
                              env=env, capture_output=True, text=True, timeout=900)
        if "accepted operator init" not in init.stdout + init.stderr:
            raise SystemExit("init refused: " + (init.stdout + init.stderr)[-600:])
    heap_mb, stack_kb = _decide(image, config, env)
    err = open(workdir / "owner.stderr", "wb")
    proc = subprocess.Popen([exe, "--fn", "operator", str(config), "run"], env=env,
                            stdout=subprocess.PIPE, stderr=err)
    cell = {"cell": "%s@%s/R%d" % (CELL_NAME, PRESET, readers), "articles": N_ARTICLES, "image": str(image), "arm": label,
            "box": os.uname().nodename, "git": git_head(), "mode": mode, "run_index": run_index,
            "preset": PRESET, "pid": proc.pid, "image_sha": _tree_sha(image), "quiet_check": quiet, "decided_heap_mb": heap_mb,
            "decided_stack_kb": stack_kb, "from_template": bool(template), "uptime": subprocess.run(["uptime"], capture_output=True, text=True).stdout.strip(), "loadavg_start": os.getloadavg()[0]}
    try:
        deadline = time.time() + 900
        while True:
            ln = proc.stdout.readline()
            if ln.startswith(b"LISTENING ") or not ln or time.time() > deadline:
                break
        time.sleep(2)
        if not template:
            w = Wire(port)
            t = time.time()
            for i in range(N_ARTICLES):
                w.post(article(i))
            w.close()
            cell["post_seconds"] = round(time.time() - t, 1)
        pipes, procs = [], []
        t_start = time.time() + 2
        t_warm_end, t_end = t_start + WARM, t_start + WARM + SECONDS
        snaps = {}

        def sampler():
            for name, when in (("start", t_start), ("warm_end", t_warm_end), ("end", t_end)):
                time.sleep(max(0, when - time.time()))
                snaps[name] = cpu_stat()
        import threading
        th = threading.Thread(target=sampler)
        th.start()
        for k in range(readers):
            a, b = mp.Pipe(False)
            pr = mp.Process(target=reader, args=(port, 1000 + k + 100 * run_index, t_warm_end, t_end, b))
            pr.start()
            pipes.append(a)
            procs.append(pr)
        results = []
        for a, pr in zip(pipes, procs):
            if a.poll(max(1.0, t_end + 90 - time.time())):
                results.append(a.recv())
            else:
                pr.terminate()       # our own reader process, hung past the cell end
                results.append(([], 1, 0, {"reader hung": 1}, {}))
        for pr in procs:
            pr.join(timeout=10)
        th.join()
        cell["core_busy_warmup"] = busy(snaps["start"], snaps["warm_end"])
        cell["core_busy_measured"] = busy(snaps["warm_end"], snaps["end"])
        cores = [c for c in cell["core_busy_measured"] if c in CORES] if CORES else list(cell["core_busy_measured"])
        cell["cores"] = "%d-%d" % (min(CORES), max(CORES)) if CORES else "all"
        cell["busy_max_on_cores"] = max([cell["core_busy_measured"][c] for c in cores] or [None])
        cell["busy_mean_on_cores"] = round(sum(cell["core_busy_measured"][c] for c in cores) / max(1, len(cores)), 3)
        cell["load_start"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t_warm_end))
        cell["load_end"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t_end))
        lat = sorted(x * 1000.0 for r in results for x in r[0])
        errs = sum(r[1] for r in results)
        why = {}
        for r in results:
            for k, v in r[3].items():
                why[k] = why.get(k, 0) + v
        cell["error_kinds"] = why
        persec = {}
        for r in results:
            for k, v in r[4].items():
                persec[k] = persec.get(k, 0) + v
        total_s = int(WARM + SECONDS + 2)
        cell["refusals_per_s"] = [persec.get(i, 0) for i in range(total_s + 1)]   # second 0 = 2 s before the warm-up starts
        cell["refusals_warmup"] = sum(persec.get(i, 0) for i in range(0, int(2 + WARM)))
        cell["refusals_steady"] = sum(persec.get(i, 0) for i in range(int(2 + WARM), total_s + 1))
        cell["refusals"] = errs      # client-seen non-220 replies and dropped connections
        cell["seconds"] = SECONDS
        cell["loadavg_end"] = os.getloadavg()[0]
        cell["loaded"] = max(cell["loadavg_start"], cell["loadavg_end"]) > 8
        if lat:
            cell["cmd"] = {"ARTICLE": {"n": len(lat), "p50_ms": statistics.median(lat),
                                       "p95_ms": pct(lat, 0.95), "p99_ms": pct(lat, 0.99),
                                       "max_ms": lat[-1]}}
        cell["rate"] = {"article_per_s": len(lat) / SECONDS,
                        "octets_per_s": sum(r[2] for r in results) / SECONDS}
        cell["errors"] = errs
        ext = {"preads_per_article": None, "hit_ratio": None, "lock_wait_ms": None,
               "lock_hold_ms": None}
        rows = read_log(log) if mode != "none" else []
        a = row_at(rows, int(t_warm_end * 1e6))
        b = row_at(rows, int(t_end * 1e6))
        if a and b and lat:
            dh, dm, dr = b[1] - a[1], b[2] - a[2], b[3] - a[3]
            ext["preads_per_article"] = dm / len(lat)
            ext["hit_ratio"] = max(0.0, 1.0 - dm / len(lat))
            ext["hit_ratio_kind"] = "lower bound 1 - preads/article"
            ext["extent_raw"] = {"hits_octets": dh, "preads": dm, "refusals_delta": dr}
            if mode == "full":
                ext["lock_acquires"] = b[4] - a[4]
                ext["lock_contended_waits"] = b[7] - a[7]
                ext["mutex_wait_calls_all_mutexes"] = b[8] - a[8]
                ext["lock_wait_ms"] = (b[5] - a[5]) / 1000.0
                ext["lock_hold_ms"] = (b[6] - a[6]) / 1000.0
            else:
                ext["lock_wait_ms"] = None
                ext["lock_wait_reason"] = ("NOT-MEASURED: mode %s; the lock is taken by an inlined "
                                           "with-mutex, wait needs W7_MODE=full" % mode)
        else:
            ext["reason"] = "no extent counters (mode %s)" % mode
        cell["extent"] = ext
        s = proc_status(proc.pid)
        cell["rss_kib"] = {"anon": s.get("RssAnon"), "file": s.get("RssFile"), "hwm": s.get("VmHWM")}
        cell["bar"] = "p99(16) <= 2*p99(1) and hit ratio does not fall as readers rise (judged over the matrix)"
        cell["verdict"] = "n/a per cell; see evaluate"
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=120)
        except subprocess.TimeoutExpired:
            proc.kill()
        err.close()
    return cell


def evaluate(path):
    cells = [json.loads(l) for l in Path(path).read_text().splitlines() if l.strip()]
    keys = sorted({(c["arm"], c["mode"]) for c in cells})
    out = []
    for arm, mode in keys:
        by = {}
        for c in cells:
            if (c["arm"], c["mode"]) == (arm, mode) and "cmd" in c:
                by.setdefault(int(c["cell"].rsplit("/R", 1)[1]), []).append(c)
        row = {"arm": arm, "mode": mode, "R": {}}
        for r, cs in sorted(by.items()):
            hits = [c["extent"].get("hit_ratio") for c in cs if c["extent"].get("hit_ratio") is not None]
            row["R"][r] = {"runs": len(cs),
                           "p50_worst": max(c["cmd"]["ARTICLE"]["p50_ms"] for c in cs),
                           "p99_worst": max(c["cmd"]["ARTICLE"]["p99_ms"] for c in cs),
                           "rate_worst": min(c["rate"]["article_per_s"] for c in cs),
                           "hit_worst": min(hits) if hits else None,
                           "preads_per_article_worst": max([c["extent"]["preads_per_article"] for c in cs
                                                           if c["extent"].get("preads_per_article") is not None] or [None]),
                           "wait_ms_worst": max([c["extent"]["lock_wait_ms"] for c in cs
                                                 if c["extent"].get("lock_wait_ms") is not None] or [None]),
                           "loaded_runs": sum(1 for c in cs if c.get("loaded"))}
        r1, r16 = row["R"].get(1), row["R"].get(16)
        if r1 and r16:
            row["ratio_p99_16_over_1"] = r16["p99_worst"] / r1["p99_worst"]
            row["ratio_ok"] = row["ratio_p99_16_over_1"] <= 2.0
        hs = [row["R"][r]["hit_worst"] for r in sorted(row["R"]) if row["R"][r]["hit_worst"] is not None]
        row["hit_non_decreasing"] = all(b >= a - 0.005 for a, b in zip(hs, hs[1:])) if hs else None
        out.append(row)
    print(json.dumps(out, indent=1))
    return out


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--image", action="append", required=True, help="LABEL=PATH")
    r.add_argument("--readers", default="1,4,16,32")
    r.add_argument("--runs", type=int, default=3)
    r.add_argument("--first-run", type=int, default=0)
    r.add_argument("--workdir", required=True)
    r.add_argument("--out", required=True)
    r.add_argument("--mode", default="stats", choices=["stats", "full", "none"])
    t = sub.add_parser("template")
    t.add_argument("--image", required=True, help="LABEL=PATH")
    t.add_argument("--workdir", required=True)
    e = sub.add_parser("evaluate")
    e.add_argument("path")
    a = p.parse_args()
    if a.cmd == "evaluate":
        evaluate(a.path)
        return
    if a.cmd == "template":
        label, path = a.image.split("=", 1)
        print(make_template(path, Path(a.workdir).resolve() / ("template-" + label)))
        return
    Path(a.workdir).mkdir(parents=True, exist_ok=True)
    templates = {}
    for spec in a.image:
        label, path = spec.split("=", 1)
        t = Path(a.workdir).resolve() / ("template-" + label)
        templates[label] = t / "store" if (t / "load_seconds").exists() else make_template(path, t)
    for run in range(a.first_run, a.first_run + a.runs):
        for spec in a.image:
            label, path = spec.split("=", 1)
            for n in [int(x) for x in a.readers.split(",")]:
                cell = run_cell(path, n, run, a.workdir, a.mode, label, templates[label])
                line = "FN_LOAD_RESULT " + json.dumps(cell)
                print(line, flush=True)
                with open(a.out, "a") as f:
                    f.write(json.dumps(cell) + "\n")


if __name__ == "__main__":
    main()
