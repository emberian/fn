#!/usr/bin/env python3
"""The cost gate: what every host-called entry, and its guard, costs on a
realistic served state, how that grows with the store, and a check that a
change does not bend a curve (lane cost-gate, 2026-10-03).

Why: correctness had fast checks on every push and cost had none.  A
quadratic owner guard sat on dev unnoticed because each lane measured on its
own synthetic store (zero successes since open; a state that failed
fn-sn-statep).  Guards run on every counterpart call: a guard is served cost.

    cost_gate.py box  [--sizes 1000,3000,10000,30000,100000] [--image IMAGE | --rev REV]
                      [--label L] [--out LOCAL_DIR]
        (laptop) ships this tree's tools/ to hbox, runs `run` there in a
        systemd-run --user scope (MemoryMax 48G, taskset, nice), waits,
        fetches the per-size dumps and the fitted table into --out
        (default build/cost-gate/LABEL), prints the head of the table.
    cost_gate.py run  --image IMAGE --sizes ... --out DIR [--work /dev/shm/...]
        (hbox) builds the fixture at each size (WORKLOAD below), measures the
        windows, writes DIR/N/WINDOW.txt (the probe's dumps) and DIR/run.json.
    cost_gate.py table DIR [--md PATH] [--json PATH]
        (anywhere) fits every (entry, window) series over the sizes and writes
        the generated table: planning/guard-cost.md and .json.
    cost_gate.py check DIR [--baseline planning/cost-baseline.json]
        compares a run (all sizes, or a sample) with the committed baseline:
        an entry whose fitted exponent rises by more than EXPONENT_TOL, or
        whose per-call bytes at a common size exceed max(base * (1 + BYTES_TOL),
        base + BYTES_FLOOR), fails, naming the entry; an entry the baseline has
        and the run did not exercise is NOT EXERCISED and fails too (fail
        closed: a workload that stopped reaching an entry is not a pass).
    cost_gate.py baseline DIR [--baseline PATH]  writes the baseline from a run.

THE PROBE.  tools/cost-probe.lisp is loaded (`--eval (load (compile-file ..))')
into a DEVELOPER image's own launch, before `(acl2::sbcl-restart)'; no image,
build script or host file carries it, and `run' refuses a launcher that is not
a developer image.  It wraps fnn-call (every host call into ACL2) and every
tree function that occurs in a guard of the image's world, and counts, per
entry: calls, ns, bytes of the whole call (entry guard, counterpart guard,
body); and of the part spent in guard predicates, per predicate and per
(predicate, enclosing predicate).  The node serves with guard checking t, as
fnn-main requires; `--guards off' (FN_COST_PROBE_GUARDS=0) wraps only fnn-call.

THE PROBE'S OWN COST.  Each wrapper's cost is calibrated in the node's own
process at the start of every window (cp-calibrate: a wrapped no-op, a loop
of 100,000 calls); the table subtracts (wrapped predicate activations x that
cost) from each entry's ns, and quotes the uncorrected figure beside it.  An
unwrapped arm of the same workload (the plain launcher, no probe) times the
build phase end to end, and the two are printed together; a probe arm more
than PROBE_DRIFT slower than the plain arm per POST is flagged.

THE FIXTURE (WORKLOAD), one per size N, built through the node's real
entries over its real interfaces (NNTP and the operator verbs), never from
hand-assembled records:
  - init: the scale profile, G = 8 groups (fn.g0 .. fn.g7) and fn.test;
  - a LAGGING READER opens first: GROUP fn.g0, reads its first article,
    then stays idle with its view pinned through everything below;
  - N POSTs since open (2 KiB each), group i mod 8, every 5th cross-posted to
    a second group: N archive pins, N successes since open;
  - every WITHDRAW_EVERY-th article is withdrawn by the operator (article
    withdraw): withdrawals and the releases of their pins, W = N /
    WITHDRAW_EVERY;
  - the fixture's invariant is asserted in the live node (fn-sn-statep of
    the owner's store, fn-owner-retain-statep of the live state) and its
    dimensions are read back (articles, successes, pins, releases,
    withdrawals); a failed assertion fails the run (no number is taken on a
    state the invariant refuses);
WINDOWS, each reset-then-dump, the same operations at every N:
  since-open  M_POST POSTs; ARTICLE / HEAD / BODY / STAT by number and by
              Message-ID over old (cold after a restart) and new articles;
              GROUP, LISTGROUP of a range, OVER of a range, NEXT, LAST, LIST,
              LIST ACTIVE, NEWNEWS, HDR; the lagging reader reads at its old
              view; M_WITHDRAW withdrawals;
  reclaim     `store reclaim' on the running owner, then the same window;
  checkpoint  `store checkpoint', a restart (the owner opens from it), then
              the same window (no successes since this open: the
              carried-index refreshes after a reload are what this shows);
  recovered   a SIGKILL'd owner, the restart's recovery, the same window.

The BUILD phase answers T for the whole-state predicates ELIDE_FOR_BUILD
(cost-probe.lisp cp-elide), raw and counterpart, because with them walking
the build is itself the quadratic this gate exists to find (N POSTs x an O(N)
guard: about 3 hours to 100k).  Each is an invariant the entries preserve,
so on the states the build visits its value is T and nothing computed
changes; the build's end evaluates them for real (cp-fixture-report) and
refuses the fixture if one is false.  (Guard checking NIL would not help: it
still evaluates a guard to choose the raw definition; :NONE runs the :logic
branches, a different program.)  Every measured window runs with nothing
elided and guard checking T.

THE FIT.  Per (entry, window) series: ns per call and bytes per call (each
loop averaged over the window's calls, never a single call), and the guard
share of both, fitted against N with tools/scale_curve.py's models and its
flags (ambiguous, bend, steepens); the exponent is the log-log slope (the
power-law k).  The table is ranked by exponent, then by ns per call at the
largest N.  Bytes are SBCL's get-bytes-consed deltas: a lower bound of what
one call allocated, which is why only loop averages are quoted.
"""
from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
import shutil
import signal
import socket
import subprocess
import sys
import time

TREE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TREE / "tools"))
sys.path.insert(0, str(TREE))

DEFAULT_SIZES = [1000, 3000, 10000, 30000, 100000]
GROUPS = ["fn.g%d" % i for i in range(8)]
OCTETS = 2048
WITHDRAW_EVERY = 200
M_POST = 200
M_READ = 200
M_WITHDRAW = 5
EXPONENT_TOL = 0.25
BYTES_TOL = 0.25
BYTES_FLOOR = 4096
NS_TOL = 0.5
PROBE_DRIFT = 0.5
BASELINE = TREE / "planning" / "cost-baseline.json"
TABLE_MD = TREE / "planning" / "guard-cost.md"
TABLE_JSON = TREE / "planning" / "guard-cost.json"
# Whole-state predicates answered T during the fixture's BUILD only (see THE
# FIXTURE); the build's end evaluates them for real.
ELIDE_FOR_BUILD = ["fn-sn-statep", "fn-node-statep", "fn-sf-statep", "fn-cat-handles-inp"]
WINDOWS = ["since-open", "reclaim", "checkpoint", "recovered"]


# --------------------------------------------------------------------------
# The node, with the probe loaded.

def launcher_argv(image, probe, work, guards):
    import throughput_gate as tg
    text = Path(image).read_text()
    if "developer" not in Path(image).name:
        raise SystemExit("cost_gate: %s is not a developer image; the probe never runs in a "
                         "production image" % image)
    argv = tg.runtime_argv(image) + ["--no-userinit"]
    if probe:
        argv += ["--eval", '(load (compile-file "%s" :output-file "%s"))'
                 % (TREE / "tools" / "cost-probe.lisp", work / "cost-probe.fasl")]
    argv += ["--eval", "(acl2::sbcl-restart)", "--disable-debugger", "--end-toplevel-options"]
    del text
    return argv


class Node:
    """One owner process of IMAGE over WORK's store, probe loaded or not.
    The process is its own session: stop() ends the whole group, so a driver
    that dies never leaves an owner behind."""

    def __init__(self, image, work, probe=True, guards=True):
        import throughput_gate as tg
        import msgid_measure as m
        self.image, self.work, self.probe, self.guards = Path(image), Path(work), probe, guards
        self.port = m.free_port()
        self.config = tg.write_config(self.work, self.port, self.work / "store")
        self.env = dict(os.environ, FN_COST_PROBE=str(self.work),
                        FN_COST_PROBE_GUARDS="1" if guards else "0", **tg.runtime_env(image))
        self.proc = None

    def operator(self, *words, check=True, timeout=3600):
        r = subprocess.run([str(self.image), "--fn", "operator", str(self.config)] + list(words),
                           env=self.env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=timeout)
        text = r.stdout.decode("utf-8", "replace")
        if check and r.returncode != 0:
            raise SystemExit("operator %s: rc=%d %s" % (" ".join(words), r.returncode, text[-600:]))
        return r.returncode, text

    def init(self):
        return self.operator("init", "--profile", "scale", "--max-transactions", "1048576",
                             "--max-history-octets", str(1 << 30),
                             "--max-article-octets", "4096", *GROUPS, "fn.test", "control.cancel")

    def start(self, timeout=3600):
        from tests.native_harness import wait_for_announcement
        argv = launcher_argv(self.image, self.probe, self.work, self.guards) + [
            "--fn", "operator", str(self.config), "run"]
        self.stderr_path = self.work / "owner.stderr"
        self.stderr = open(self.stderr_path, "ab")
        t0 = time.perf_counter()
        self.proc = subprocess.Popen(argv, env=self.env, stdout=subprocess.PIPE,
                                     stderr=self.stderr, start_new_session=True)
        wait_for_announcement(self.proc, b"LISTENING ", timeout=timeout, stderr_path=self.stderr_path)
        return time.perf_counter() - t0

    def stop(self, sig=signal.SIGTERM, timeout=600):
        if self.proc is None:
            return
        try:
            os.killpg(self.proc.pid, sig)
            self.proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(self.proc.pid, signal.SIGKILL)
            self.proc.wait()
        except ProcessLookupError:
            pass
        self.proc = None
        self.stderr.close()

    def request(self, forms, timeout=3600):
        """Evaluate FORMS in the live node (the probe's request hook)."""
        reply = self.work / "reply.txt"
        reply.unlink(missing_ok=True)
        tmp = self.work / "request.tmp"
        tmp.write_text('(in-package "ACL2")\n' + forms + "\n")
        os.rename(tmp, self.work / "request.lisp")
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if reply.exists():
                text = reply.read_text()
                if "CP-REQUEST-OK" not in text:
                    raise SystemExit("cost_gate: request failed: %s" % text[-800:])
                return text
            if self.proc.poll() is not None:
                raise SystemExit("cost_gate: the owner exited during a request")
            time.sleep(0.05)
        raise SystemExit("cost_gate: no reply to a request in %d s" % timeout)

    def client(self, source=None):
        import msgid_measure as m
        return m.Conn(self.port, buffered=True)


# --------------------------------------------------------------------------
# Articles.

def msgid(i):
    return "<cg-%07d@cost.invalid>" % i


def article(i, groups):
    head = ("From: cg@cost.invalid\r\nNewsgroups: %s\r\nSubject: cost gate %d\r\n"
            "Date: Thu, 01 Oct 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n"
            % (",".join(groups), i, msgid(i)))
    line = "the quick brown fox jumps over the lazy dog, again and again, at a cost.\r\n"
    body = line * max(1, (OCTETS - len(head)) // len(line))
    return (head + body).encode("ascii")


def groups_of(i):
    g = [GROUPS[i % len(GROUPS)]]
    if i % 5 == 0:
        g.append(GROUPS[(i + 3) % len(GROUPS)])
    return g


def post(c, i):
    r = c.line("POST")
    if not r.startswith(b"340"):
        raise SystemExit("POST %d: %r" % (i, r))
    c.stream.write(article(i, groups_of(i)) + b".\r\n")
    r = c.readline()
    if not r.startswith(b"240"):
        raise SystemExit("POST %d body: %r" % (i, r))


MULTI = {b"220", b"221", b"222", b"224", b"225", b"215", b"230", b"231", b"282"}


def multiline(c, text):
    """One command and its whole reply (RFC 3977 3.1: the multi-line codes;
    211 is multi-line only for LISTGROUP)."""
    reply = c.line(text)
    code = reply[:3]
    if code in MULTI or (code == b"211" and text.upper().startswith("LISTGROUP")):
        while True:
            line = c.readline()
            if not line:
                raise SystemExit("connection closed in a reply to %s" % text)
            if line == b".\r\n":
                break
    return reply


# --------------------------------------------------------------------------
# The fixture and the windows.

INVARIANT_FORMS = r"""
(cp-fixture-report)
"""


def build(node, n, log):
    """The since-open state at size N (see THE FIXTURE)."""
    node.request("(cp-elide '(%s))" % " ".join(ELIDE_FOR_BUILD))
    lag = node.client()
    c = node.client()
    t0 = time.perf_counter()
    withdrawn = []
    stalled = None
    for i in range(n):
        post(c, i)
        if i == 0:
            multiline(lag, "GROUP %s" % GROUPS[0])
            multiline(lag, "ARTICLE %s" % msgid(0))
        if i == n // 2:
            stalled = stalled_reader(node.port)
        if i % WITHDRAW_EVERY == WITHDRAW_EVERY - 1:
            node.operator("article", "withdraw", msgid(i - 1), "--reason", "cost-gate fixture")
            withdrawn.append(i - 1)
    log["build_s"] = round(time.perf_counter() - t0, 3)
    log["build_posts"] = n
    log["build_withdrawals"] = len(withdrawn)
    node.request("(cp-unelide)")
    rc, text = node.operator("pins", check=False)
    log["pins_report_lines"] = len(text.splitlines())
    log["pins_report_head"] = text[:600]
    return lag, c, withdrawn, stalled


def stalled_reader(port):
    """A slow reader (Astra r71 item 14): a 4 KiB receive buffer, the group's
    whole overview asked for and never read, so the reply's response pin is
    held across every commit after it (half the build and the since-open and
    reclaim windows)."""
    s = socket.socket()
    s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
    s.connect(("127.0.0.1", port))
    s.recv(512)
    s.sendall(b"GROUP %s\r\n" % GROUPS[0].encode())
    s.recv(512)
    s.sendall(b"OVER 1-2147483647\r\nHDR Subject 1-2147483647\r\nLISTGROUP\r\n")
    return s


def window(node, n, name, out_dir, lag, base, log):
    """The same operations at every N; the probe's dump to OUT_DIR/NAME.txt."""
    node.request("(cp-calibrate) (cp-reset)")
    c = node.client()
    t0 = time.perf_counter()
    for k in range(M_POST):
        post(c, base + k)
    olds = [int(n * j / M_READ) for j in range(M_READ)]
    for i in olds:
        if i % WITHDRAW_EVERY == WITHDRAW_EVERY - 2:
            continue
        multiline(c, "ARTICLE %s" % msgid(i))
        multiline(c, "STAT %s" % msgid(i))
    for g in GROUPS:
        reply = multiline(c, "GROUP %s" % g)
        r = reply.split()
        if r[:1] != [b"211"]:
            raise SystemExit("GROUP %s: %r" % (g, reply))
        lo, hi = int(r[2]), int(r[3])
        for k in range(10):
            num = lo + (hi - lo) * k // 10
            multiline(c, "ARTICLE %d" % num)
            multiline(c, "HEAD %d" % num)
            multiline(c, "BODY %d" % num)
            multiline(c, "STAT %d" % num)
            multiline(c, "NEXT")
            multiline(c, "LAST")
        multiline(c, "OVER %d-%d" % (max(lo, hi - 99), hi))
        multiline(c, "LISTGROUP %s %d-%d" % (g, max(lo, hi - 99), hi))
        multiline(c, "HDR Subject %d-%d" % (max(lo, hi - 99), hi))
    multiline(c, "LIST")
    multiline(c, "LIST ACTIVE")
    multiline(c, "NEWNEWS fn.* 20261001 000000 GMT")
    if lag is not None:
        multiline(lag, "ARTICLE %s" % msgid(1))
        multiline(lag, "NEXT")
        multiline(lag, "OVER")
    for k in range(M_WITHDRAW):
        node.operator("article", "withdraw", msgid(base + k), "--reason", "cost-gate window")
    c.close()
    log.setdefault("windows", {})[name] = {"s": round(time.perf_counter() - t0, 3)}
    dump = out_dir / ("%s.txt" % name)
    node.request('(cp-dump "%s")' % dump)
    return dump


def run_size(image, n, work, out_dir, guards, log):
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    out_dir.mkdir(parents=True, exist_ok=True)
    node = Node(image, work, probe=True, guards=guards)
    node.init()
    try:
        log["open_s"] = node.start()
        lag, c, withdrawn, stalled = build(node, n, log)
        c.close()
        rep = node.request("(cp-fixture-report)")
        log["fixture"] = parse_report(rep)
        if log["fixture"].get("sn_statep") != "T" or log["fixture"].get("retain_statep") != "T":
            raise SystemExit("cost_gate: the fixture at N=%d fails the invariant: %s" % (n, rep[-800:]))
        base = n
        window(node, n, "since-open", out_dir, lag, base, log); base += M_POST
        t0 = time.perf_counter()
        log["reclaim_text"] = node.operator("store", "reclaim")[1][-400:]
        log["reclaim_s"] = round(time.perf_counter() - t0, 3)
        window(node, n, "reclaim", out_dir, lag, base, log); base += M_POST
        lag.sock.close()
        if stalled is not None:
            stalled.close()
        t0 = time.perf_counter()
        log["checkpoint_text"] = node.operator("store", "checkpoint")[1][-400:]
        log["checkpoint_s"] = round(time.perf_counter() - t0, 3)
        node.stop()
        log["reopen_checkpoint_s"] = node.start()
        window(node, n, "checkpoint", out_dir, None, base, log); base += M_POST
        node.stop(sig=signal.SIGKILL)
        log["reopen_recovered_s"] = node.start()
        window(node, n, "recovered", out_dir, None, base, log)
    finally:
        node.stop()
    (out_dir / "size.json").write_text(json.dumps(log, indent=1, sort_keys=True))


def plain_arm(image, n, work, log):
    """The build phase on the plain launcher (no probe): its wall time."""
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    node = Node(image, work, probe=False)
    node.init()
    try:
        node.start()
        c = node.client()
        t0 = time.perf_counter()
        for i in range(min(n, 2000)):
            post(c, i)
        log["plain_post_ms"] = round(1000 * (time.perf_counter() - t0) / min(n, 2000), 4)
        c.close()
    finally:
        node.stop()


def parse_report(text):
    out = {}
    for line in text.splitlines():
        if line.startswith("FIXTURE "):
            for word in line.split()[1:]:
                k, _, v = word.partition("=")
                out[k] = int(v) if v.isdigit() else v
    return out


def _terminated(signum, frame):
    raise SystemExit("cost_gate: terminated by signal %d" % signum)


def cmd_run(a):
    # A SIGTERM (a timeout, systemd) unwinds through every Node.stop: no
    # owner outlives its driver.
    signal.signal(signal.SIGTERM, _terminated)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    meta = {"image": str(a.image), "sizes": a.sizes, "guards": a.guards,
            "core_sha256": None, "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    core = Path(str(a.image) + ".core")
    if core.exists():
        import hashlib
        h = hashlib.sha256()
        with open(core, "rb") as f:
            for block in iter(lambda: f.read(1 << 20), b""):
                h.update(block)
        meta["core_sha256"] = h.hexdigest()
    (out / "run.json").write_text(json.dumps(meta, indent=1))
    for n in a.sizes:
        log = {"n": n}
        try:
            run_size(a.image, n, Path(a.work) / ("n%d" % n), out / ("n%d" % n), a.guards == "on", log)
            plain_arm(a.image, n, Path(a.work) / ("plain%d" % n), log)
        except SystemExit as e:
            log["failed"] = str(e)
        finally:
            shutil.rmtree(Path(a.work) / ("n%d" % n), ignore_errors=True)
            shutil.rmtree(Path(a.work) / ("plain%d" % n), ignore_errors=True)
        (out / ("n%d" % n)).mkdir(parents=True, exist_ok=True)
        (out / ("n%d" % n) / "size.json").write_text(json.dumps(log, indent=1, sort_keys=True))
        print(json.dumps({k: log.get(k) for k in ("n", "build_s", "plain_post_ms", "failed", "fixture")}),
              flush=True)
    meta["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    (out / "run.json").write_text(json.dumps(meta, indent=1))
    return 0


# --------------------------------------------------------------------------
# Reading the dumps, the fit, the table.

def read_dump(path):
    """{entry: {...}} with per-predicate rows."""
    entries, preds, calib = {}, {}, {}
    for line in Path(path).read_text().splitlines():
        w = line.split()
        if not w:
            continue
        if w[0] == "E":
            calls, ns, by, gcalls, gns, gby, mx = (int(x) for x in w[2:9])
            # w[9]: every predicate-wrapper pass inside the entry
            entries[w[1]] = {"calls": calls, "ns": ns, "bytes": by, "gcalls": gcalls,
                             "gns": gns, "gbytes": gby, "max_ns": mx,
                             "wrapped": int(w[9]) if len(w) > 9 else 0}
        elif w[0] == "P":
            calls, ns, by, top = (int(x) for x in w[4:8])
            preds.setdefault(w[1], []).append({"pred": w[2], "parent": w[3], "calls": calls,
                                               "ns": ns, "bytes": by, "top": top})
        elif w[0] == "C":
            calib[w[1]] = float(w[2])
    for name, row in entries.items():
        row["preds"] = preds.get(name, [])
    return entries, calib


def per_call(row, calib):
    timed = sum(p["calls"] for p in row["preds"])
    over = (calib.get("wrapper_ns", 0.0) * timed
            + calib.get("skip_ns", 0.0) * max(0, row.get("wrapped", 0) - timed))
    ns = max(0.0, row["ns"] - over)
    gns = max(0.0, row["gns"] - min(over, row["gns"]))
    c = max(1, row["calls"])
    return {"ns": ns / c, "ns_raw": row["ns"] / c, "bytes": row["bytes"] / c,
            "gns": gns / c, "gbytes": row["gbytes"] / c, "calls": row["calls"]}


def load_run(d):
    d = Path(d)
    sizes = {}
    for sub in sorted(d.glob("n*")):
        try:
            n = int(sub.name[1:])
        except ValueError:
            continue
        for w in WINDOWS:
            p = sub / ("%s.txt" % w)
            if p.exists():
                entries, calib = read_dump(p)
                sizes.setdefault(n, {})[w] = {"entries": entries, "calib": calib}
        if (sub / "size.json").exists():
            sizes.setdefault(n, {})["_size"] = json.loads((sub / "size.json").read_text())
    return sizes


def series(sizes, window, entry, key):
    xs, ys = [], []
    for n in sorted(sizes):
        w = sizes[n].get(window)
        if not w or entry not in w["entries"]:
            continue
        v = per_call(w["entries"][entry], w["calib"])[key]
        xs.append(n)
        ys.append(v)
    return xs, ys


def exponent(xs, ys):
    """The log-log slope over the points, with a floor so that a constant of
    zero bytes is an exponent of 0, not a failed fit."""
    pts = [(math.log(x), math.log(max(y, 1.0))) for x, y in zip(xs, ys)]
    if len(pts) < 2:
        return None
    mx = sum(p[0] for p in pts) / len(pts)
    my = sum(p[1] for p in pts) / len(pts)
    sxx = sum((p[0] - mx) ** 2 for p in pts)
    return sum((p[0] - mx) * (p[1] - my) for p in pts) / sxx if sxx else None


def fitted(xs, ys, key):
    import scale_curve as sc
    out = {"k": exponent(xs, ys)}
    if len(xs) >= 3 and all(y > 0 for y in ys):
        f = sc.fit_series(xs, ys, xs, key)
        out.update(best=f.get("best"), residual=f.get("residual"), flags=f.get("flags", []),
                   at_1M=f.get("at_1M"))
    return out


def top_preds(sizes, window, entry, n):
    w = sizes[n].get(window)
    if not w or entry not in w["entries"]:
        return []
    row = w["entries"][entry]
    agg = {}
    for p in row["preds"]:
        a = agg.setdefault(p["pred"], {"ns": 0, "bytes": 0, "calls": 0})
        # inclusive per (pred, parent): the predicate's own activations only
        # once per parent, so the outermost row of each predicate is a sum
        a["ns"] += p["ns"]
        a["bytes"] += p["bytes"]
        a["calls"] += p["calls"]
    c = max(1, row["calls"])
    ranked = sorted(agg.items(), key=lambda kv: -kv[1]["ns"])[:3]
    return [{"pred": k, "ns_per_call": v["ns"] / c, "bytes_per_call": v["bytes"] / c,
             "activations_per_call": v["calls"] / c} for k, v in ranked]


def table(sizes):
    rows = []
    ns_sorted = sorted(sizes)
    for w in WINDOWS:
        names = set()
        for n in ns_sorted:
            if w in sizes[n]:
                names.update(sizes[n][w]["entries"])
        for e in sorted(names):
            xs, t = series(sizes, w, e, "ns")
            if not xs:
                continue
            _, b = series(sizes, w, e, "bytes")
            _, g = series(sizes, w, e, "gns")
            _, gb = series(sizes, w, e, "gbytes")
            _, calls = series(sizes, w, e, "calls")
            top_n = xs[-1]
            rows.append({
                "entry": e, "window": w, "sizes": xs, "calls": calls,
                "ns": t, "bytes": b, "guard_ns": g, "guard_bytes": gb,
                "fit_ns": fitted(xs, t, "ns"), "fit_bytes": fitted(xs, b, "bytes"),
                "fit_guard_ns": fitted(xs, g, "guard_ns"),
                "guard_share": (g[-1] / t[-1]) if t[-1] else 0.0,
                "top_guards": top_preds(sizes, w, e, top_n),
            })
    def key(r):
        k = r["fit_ns"]["k"]
        return (-(k if k is not None else -9), -r["ns"][-1])
    rows.sort(key=key)
    return rows


def fmt_ns(v):
    if v >= 1e9:
        return "%.2f s" % (v / 1e9)
    if v >= 1e6:
        return "%.2f ms" % (v / 1e6)
    if v >= 1e3:
        return "%.1f us" % (v / 1e3)
    return "%.0f ns" % v


def fmt_b(v):
    for unit, size in (("GB", 1 << 30), ("MB", 1 << 20), ("KB", 1 << 10)):
        if v >= size:
            return "%.1f %s" % (v / size, unit)
    return "%.0f B" % v


def fmt_k(f):
    return "-" if f.get("k") is None else "%.2f" % f["k"]


def markdown(rows, meta, limit=None):
    out = ["# Guard cost per host-called entry (GENERATED by tools/cost_gate.py table; do not edit)", "",
           "Image: `%s` (core sha256 `%s`). Sizes N = %s. Each figure is per call, averaged over the "
           "window's calls (loop average), with the probe's calibrated wrapper cost subtracted; "
           "guards ON (guard checking t, as fnn-main runs). k is the log-log slope over N of ns per "
           "call (k_b of bytes per call, k_g of the guard's ns per call). Ranked by k, then by ns at "
           "the largest N. Windows: since-open (N commits since open), reclaim (after store "
           "reclaim), checkpoint (reopened from a checkpoint), recovered (reopened after SIGKILL)."
           % (meta.get("image"), (meta.get("core_sha256") or "?")[:16],
              ", ".join("{:,}".format(n) for n in meta.get("sizes", []))), "",
           "| # | entry | window | calls | ns/call at sizes | k | bytes/call (largest N) | k_b | "
           "guard share | k_g | top guard predicates (per call at the largest N) | flags |",
           "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for i, r in enumerate(rows[:limit] if limit else rows, 1):
        tops = "; ".join("%s %s (%s, %.0f act.)" % (p["pred"], fmt_ns(p["ns_per_call"]),
                                                    fmt_b(p["bytes_per_call"]), p["activations_per_call"])
                         for p in r["top_guards"])
        flags = "; ".join(r["fit_ns"].get("flags", []))[:120]
        out.append("| %d | `%s` | %s | %d | %s | %s | %s | %s | %.0f%% | %s | %s | %s |" % (
            i, r["entry"], r["window"], r["calls"][-1],
            " / ".join(fmt_ns(v) for v in r["ns"]), fmt_k(r["fit_ns"]), fmt_b(r["bytes"][-1]),
            fmt_k(r["fit_bytes"]), 100 * r["guard_share"], fmt_k(r["fit_guard_ns"]), tops, flags))
    return "\n".join(out) + "\n"


def cmd_table(a):
    sizes = load_run(a.dir)
    meta = json.loads((Path(a.dir) / "run.json").read_text()) if (Path(a.dir) / "run.json").exists() else {}
    rows = table(sizes)
    md = markdown(rows, meta, a.limit)
    if a.md:
        Path(a.md).write_text(md)
    if a.json:
        Path(a.json).write_text(json.dumps({"meta": meta, "rows": rows}, indent=1, sort_keys=True) + "\n")
    if not a.md:
        sys.stdout.write(md)
    return 0


# --------------------------------------------------------------------------
# The gate.

def baseline_rows(rows):
    out = {}
    for r in rows:
        key = "%s@%s" % (r["entry"], r["window"])
        out[key] = {"k": r["fit_ns"]["k"], "k_bytes": r["fit_bytes"]["k"],
                    "bytes": dict(zip((str(n) for n in r["sizes"]), (round(b) for b in r["bytes"]))),
                    "ns": dict(zip((str(n) for n in r["sizes"]), (round(t) for t in r["ns"])))}
    return out


def cmd_baseline(a):
    sizes = load_run(a.dir)
    meta = json.loads((Path(a.dir) / "run.json").read_text())
    rows = table(sizes)
    doc = {"about": "Per (entry, window): the fitted exponent of ns per call (k) and of bytes per "
                    "call (k_bytes) over N, and per-call bytes and ns at each size, from one "
                    "tools/cost_gate.py run on hbox. `cost_gate.py check' fails an entry whose "
                    "exponent rises by more than %.2f or whose bytes per call at a common size exceed "
                    "max(base x %.2f, base + %d), and an entry here that a run did not exercise."
                    % (EXPONENT_TOL, 1 + BYTES_TOL, BYTES_FLOOR),
           "image": meta.get("image"), "core_sha256": meta.get("core_sha256"),
           "sizes": meta.get("sizes"), "entries": baseline_rows(rows)}
    Path(a.baseline).write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")
    print("baseline: %d (entry, window) rows -> %s" % (len(doc["entries"]), a.baseline))
    return 0


def cmd_check(a):
    base = json.loads(Path(a.baseline).read_text())
    sizes = load_run(a.dir)
    rows = {"%s@%s" % (r["entry"], r["window"]): r for r in table(sizes)}
    run_sizes = sorted(sizes)
    failures, notes = [], []
    for key, b in sorted(base["entries"].items()):
        r = rows.get(key)
        if r is None:
            failures.append("NOT EXERCISED %s (the baseline has it; this run never called it)" % key)
            continue
        k = r["fit_ns"]["k"]
        if len(r["sizes"]) >= 2 and k is not None and b.get("k") is not None and k > b["k"] + EXPONENT_TOL:
            failures.append("BENT %s: exponent %.2f > baseline %.2f + %.2f" % (key, k, b["k"], EXPONENT_TOL))
        kb = r["fit_bytes"]["k"]
        if len(r["sizes"]) >= 2 and kb is not None and b.get("k_bytes") is not None \
                and kb > b["k_bytes"] + EXPONENT_TOL:
            failures.append("BENT %s: bytes exponent %.2f > baseline %.2f + %.2f"
                            % (key, kb, b["k_bytes"], EXPONENT_TOL))
        for n, by in zip(r["sizes"], r["bytes"]):
            bb = b["bytes"].get(str(n))
            if bb is not None and by > max(bb * (1 + BYTES_TOL), bb + BYTES_FLOOR):
                failures.append("BYTES %s at N=%d: %s per call > baseline %s" % (key, n, fmt_b(by), fmt_b(bb)))
    for key in sorted(set(rows) - set(base["entries"])):
        notes.append("NEW %s (not in the baseline: k=%s)" % (key, fmt_k(rows[key]["fit_ns"])))
    for line in failures + notes:
        print(line)
    print("cost_gate check: %d failure(s), %d new row(s); sizes %s" % (len(failures), len(notes), run_sizes))
    return 1 if failures else 0


# --------------------------------------------------------------------------
# The laptop side.

def cmd_box(a):
    label = a.label or time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    remote = "/tank/fn/scratch/cost-gate/runs/%s" % label
    tree = remote + "/tree"
    subprocess.run(["ssh", "hbox", "mkdir -p %s/tree/tests %s/out" % (remote, remote)], check=True)
    subprocess.run(["rsync", "-a", "--exclude", "__pycache__", str(TREE / "tools") + "/",
                    "hbox:%s/tools/" % tree], check=True)
    subprocess.run(["rsync", "-a", str(TREE / "tests" / "native_harness.py"), str(TREE / "tests" / "__init__.py"),
                    "hbox:%s/tests/" % tree], check=True)
    subprocess.run(["rsync", "-a", "--include", "*/", "--include", "outcome-class.lisp", "--exclude", "*",
                    str(TREE / "books") + "/", "hbox:%s/books/" % tree], check=True)
    sizes = ",".join(str(n) for n in a.sizes)
    inner = ("cd %s && systemd-run --user --scope -q -p MemoryMax=48G taskset -c 16-31 nice -n 5 "
             "python3 tools/cost_gate.py run --image %s --sizes %s --guards %s --out %s/out "
             "--work /dev/shm/fn-cost-gate/%s > %s/run.log 2>&1; echo $? > %s/status"
             % (tree, a.image, sizes, a.guards, remote, label, remote, remote))
    subprocess.run(["ssh", "hbox", "nohup sh -c '%s' >/dev/null 2>&1 &" % inner.replace("'", "'\\''")],
                   check=True)
    print("cost_gate: started on hbox: %s (status file %s/status)" % (remote, remote))
    if a.detach:
        return 0
    while subprocess.run(["ssh", "hbox", "test -f %s/status" % remote]).returncode != 0:
        time.sleep(30)
    local = Path(a.out or (TREE / "build" / "cost-gate" / label))
    local.mkdir(parents=True, exist_ok=True)
    subprocess.run(["rsync", "-a", "hbox:%s/out/" % remote, str(local) + "/"], check=True)
    subprocess.run(["rsync", "-a", "hbox:%s/run.log" % remote, str(local) + "/"], check=True)
    print("cost_gate: fetched into %s" % local)
    return 0


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)

    def sizes(text):
        return [int(x) for x in text.split(",") if x]

    r = sub.add_parser("run")
    r.add_argument("--image", required=True)
    r.add_argument("--sizes", type=sizes, default=DEFAULT_SIZES)
    r.add_argument("--guards", choices=("on", "off"), default="on")
    r.add_argument("--out", required=True)
    r.add_argument("--work", default="/dev/shm/fn-cost-gate/work")
    r.set_defaults(fn=cmd_run)
    b = sub.add_parser("box")
    b.add_argument("--image", required=True)
    b.add_argument("--sizes", type=sizes, default=DEFAULT_SIZES)
    b.add_argument("--guards", choices=("on", "off"), default="on")
    b.add_argument("--label")
    b.add_argument("--out")
    b.add_argument("--detach", action="store_true")
    b.set_defaults(fn=cmd_box)
    t = sub.add_parser("table")
    t.add_argument("dir")
    t.add_argument("--md")
    t.add_argument("--json")
    t.add_argument("--limit", type=int)
    t.set_defaults(fn=cmd_table)
    c = sub.add_parser("check")
    c.add_argument("dir")
    c.add_argument("--baseline", default=str(BASELINE))
    c.set_defaults(fn=cmd_check)
    s = sub.add_parser("baseline")
    s.add_argument("dir")
    s.add_argument("--baseline", default=str(BASELINE))
    s.set_defaults(fn=cmd_baseline)
    a = p.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
