"""W6 peers: a second node B beside the harness node A.

    catchup       B pulls A's backlog by `peer catch-up A 2`            (W6a, L-CATCHUP)
    feed          A takes POSTs at a fixed rate with B as its feed peer (W6b)
    catchup-load  as catchup while A takes POSTs at a fixed rate        (W6c)

The setup mirrors tests/test_native_peer_catchup.py: both stores are made by
`operator init` under the same profile, each gets a `path-identity`, B is
funded with the peer flight profile (FNP1 and six big-endian u64), B's peer
row for A is `peer add A ID 127.0.0.1 PORT fn.* - source-address 127.0.0.9 true`
and `peer catch-up A 2` (B dials A only), and the round's completion is
read from B's owner log (`catch-up peer=A round=done|failed ...`, written
when a round closes).  Progress inside a round is B's own `GROUP fn.test`
count, polled twice a second.

Everything above `class Ctx` is pure (no image, no sockets): laptop-tested in
tests/test_load_harness.py.  `setup` and `run_phase` are driven by driver.py
(`d` is the driver module, passed in to avoid a circular import).
"""
from __future__ import annotations

import re
import shutil
import threading
import time
from pathlib import Path

from .result import lat_stats

A_ID = "a.load.example.invalid"
B_ID = "b.load.example.invalid"
# tests/native_harness.PEER_FLIGHT_POLICY: heap, disk, flights, workers, spool per flight, metered work.
PEER_FLIGHT_POLICY = (8 << 20, 512 << 20, 2, 1, 64 << 20, 1 << 50)
CATCHUP_INTERVAL = "2"
GROUP = "fn.test"
POLL_S = 0.5

ROUND_RE = re.compile(
    r"catch-up peer=(?P<peer>\S+) round=(?P<round>done|failed) position=(?P<position>\d+) end=(?P<end>\d+)"
    r" imported=(?P<imported>\d+) duplicate=(?P<duplicate>\d+) refused=(?P<refused>\d+) digest=(?P<digest>[0-9a-f]{64})"
    r"(?: reason=(?P<reason>\S+))?(?: at=(?P<at>\S+))?(?: transport=(?P<transport>\S+))?")


# ------------------------------------------------------------------ pure

def parse_round_line(line):
    """The fields of one owner-log `catch-up peer=` line (books/peer-catchup.lisp
    fn-cu-session-log-line), or None.  Numbers are ints; reason/at/transport may be None."""
    mo = ROUND_RE.search(line)
    if not mo:
        return None
    d = mo.groupdict()
    for k in ("position", "end", "imported", "duplicate", "refused"):
        d[k] = int(d[k])
    return d


def splits(series, t0, step=1000):
    """Seconds taken by each successive STEP articles: series is [(t, count)] in time order
    (t in the same clock as t0, the moment the count was zero); the k-th entry is the time
    from the (k-1)-th crossing to the k-th.  A partial last step is not reported."""
    out, prev, k = [], t0, 1
    for t, c in series:
        while c >= k * step:
            out.append(round(t - prev, 2))
            prev, k = t, k + 1
    return out


def cpu_splits(rows, base, step=1000):
    """CPU seconds A and B each spent per successive STEP articles.  rows [(count, a_cpu_s, b_cpu_s)] in
    time order, base (a_cpu_s, b_cpu_s) at count 0; the figures at the first row at or past each multiple of
    STEP, differenced.  Returns [{"a_cpu_s", "b_cpu_s"}]."""
    out, prev = [], base
    for row in crossings(rows, step):
        a, b = row[1], row[2]
        out.append({"a_cpu_s": round(a - prev[0], 2), "b_cpu_s": round(b - prev[1], 2)})
        prev = (a, b)
    return out


def crossings(rows, step=1000):
    """The first row (count first) at or past each multiple of STEP."""
    out, k = [], 1
    for row in rows:
        while row[0] >= k * step:
            out.append(row)
            k += 1
    return out


def gc_splits(gc_lines, base_us, crossing_us):
    """B's GC per step from the hook's log (`GC <epoch-us> <cumulative gc-run-us> <dynamic-usage>`):
    for each crossing instant (epoch-us) the GC milliseconds and count since the previous crossing, and the
    dynamic usage (MiB) after the last GC at or before it.  base_us is the epoch-us at count 0."""
    parsed = []
    for line in gc_lines:
        w = line.split()
        if len(w) == 4 and w[0] == "GC":
            parsed.append((int(w[1]), int(w[2]), int(w[3])))
    out, prev_run, prev_n = [], 0, 0
    for at in crossing_us:
        upto = [g for g in parsed if g[0] <= at]
        run = upto[-1][1] if upto else 0
        out.append({"gc_ms": round((run - prev_run) / 1000.0, 1), "gcs": len(upto) - prev_n,
                    "dynamic_mib_after_gc": round(upto[-1][2] / 1048576.0, 1) if upto else None})
        prev_run, prev_n = run, len(upto)
    return out


def thread_deltas(base, at_crossings, top=3):
    """Per step, the TOP threads by CPU seconds: base and each entry of at_crossings are {"tid comm": cpu_s}."""
    out, prev = [], base
    for cur in at_crossings:
        d = {k: round(v - prev.get(k, 0.0), 2) for k, v in cur.items()}
        out.append(dict(sorted(d.items(), key=lambda kv: -kv[1])[:top]))
        prev = cur
    return out


def pace(count, seconds):
    return None if not seconds or seconds <= 0 else round(count / seconds, 2)


def thin(series, limit=400):
    """At most LIMIT evenly spaced points, always keeping the last."""
    if len(series) <= limit:
        return list(series)
    stride = -(-len(series) // limit)
    out = list(series[::stride])
    if out[-1] != series[-1]:
        out.append(series[-1])
    return out


def without_xref(octets):
    head, _, body = octets.partition(b"\r\n\r\n")
    kept = [l for l in head.split(b"\r\n") if not l.lower().startswith(b"xref:")]
    return b"\r\n".join(kept) + b"\r\n\r\n" + body


def without_path_and_xref(octets):
    head, _, body = octets.partition(b"\r\n\r\n")
    kept = [l for l in head.split(b"\r\n") if not (l.lower().startswith(b"path:") or l.lower().startswith(b"xref:"))]
    return b"\r\n".join(kept) + b"\r\n\r\n" + body


def chain_digest(order, articles, blake3):
    """tests/test_native_peer_catchup expected_digest: chain = blake3(chain + blake3(octets) + msgid)
    over the articles in A's log order, each without its Xref line; hex."""
    chain = bytes(32)
    for msgid in order:
        chain = blake3(chain + blake3(without_xref(articles[msgid])) + msgid.encode("ascii"))
    return chain.hex()


def compare(a, a_order, b, b_order):
    """Divergence of B from A: Message-IDs only in A (missing), only in B (extra), present in both
    with different octets once Path and Xref are dropped (differing).  divergence is their sum;
    order_equal says B numbered them in A's order (catch-up is oldest first)."""
    missing = sorted(set(a) - set(b))
    extra = sorted(set(b) - set(a))
    differing = sorted(m for m in set(a) & set(b) if without_path_and_xref(a[m]) != without_path_and_xref(b[m]))
    return {"a_articles": len(a), "b_articles": len(b), "missing": len(missing), "extra": len(extra),
            "differing": len(differing), "divergence": len(missing) + len(extra) + len(differing),
            "order_equal": list(a_order) == list(b_order), "first_bad": (missing + extra + differing)[:3]}


def digest_lines(text):
    """`store ROOT digest` output -> {name: hex}.  Lines are `digest NAME HEX` (history, pool, field ..., config,
    canonical, genesis, state) and `checkpoint-digest sequence=N HEX`; the name is the word after `digest`,
    else the first word."""
    out = {}
    for line in text.splitlines():
        words = line.split()
        hexes = [w for w in words if re.fullmatch(r"[0-9a-f]{64}", w)]
        if not words or not hexes:
            continue
        name = words[1] if words[0] == "digest" and len(words) > 2 else words[0].rstrip(":=")
        out[name] = hexes[-1]
    return out


def post_stats(samples):
    """samples [(intended_t, latency_s)] -> lat_stats; p99 null under 200 samples (result.lat_stats)."""
    return lat_stats([lat for _, lat in samples])


def p99_ratio(during, idle):
    """during/idle p99, or None when either has fewer than 200 samples."""
    d, i = (during or {}).get("p99_ms"), (idle or {}).get("p99_ms")
    return None if d is None or not i else round(d / i, 2)


def lag_summary(series):
    """series [(t, a_count, b_count)] -> max and final articles A holds that B does not (the feed's
    backlog, a proxy for A's per-peer queue depth) and the time B was at lag 0 last."""
    lags = [max(0, a - b) for _, a, b in series]
    return {"max": max(lags) if lags else None, "final": lags[-1] if lags else None}


# ---------------------------------------------------------------- derive (cells.py maps to these)

def _peers_phase(phases):
    return next((p for p in phases if p.get("kind") == "peers" and p.get("status") != "not-implemented" and "peers" in p), None)


def _put(m, key, val):
    if val is not None:
        m[key] = val


def derive_catchup(phases, m, nm):
    ph = _peers_phase(phases)
    if ph is None:
        return
    r = ph["peers"]
    n = r.get("nominal")
    if n is not None:
        _put(m, "catchup.rate_%d" % n, r.get("pace_excl_start"))
        _put(m, "catchup.rate_incl_start_%d" % n, r.get("pace_incl_start"))
        if r.get("pace_excl_start") is None:
            nm["catchup.rate_%d" % n] = "round did not complete: %s" % (r.get("terminal") or "unknown")
    _put(m, "catchup.imported", r.get("b_count_final"))
    _put(m, "catchup.rounds_failed", r.get("rounds_failed"))
    _put(m, "catchup.first_import_s", r.get("first_import_s"))
    cmp_ = r.get("compare") or {}
    if "divergence" in cmp_:
        m["peers.divergence"] = cmp_["divergence"]
        m["peers.digest_chain_equal"] = 1 if r.get("chain_equal") else 0
    else:
        nm["peers.divergence"] = r.get("compare_error") or "comparison did not run"
    b = r.get("b_mem") or {}
    _put(m, "b.rss_kib.vmrss", b.get("vmrss"))
    _put(m, "b.rss_kib.hwm", b.get("hwm"))
    _put(m, "b.rss_kib.peak_vmrss", b.get("peak_vmrss"))
    during, idle = r.get("post_during"), r.get("post_idle")
    for tag, st in (("during", during), ("idle", idle)):
        if st:
            _put(m, "post.p50_ms." + tag, st.get("p50_ms"))
            _put(m, "post.p99_ms." + tag, st.get("p99_ms"))
    if during is not None or idle is not None:
        ratio = p99_ratio(during, idle)
        if ratio is not None:
            m["post.p99_ratio"] = ratio
        else:
            nm["post.p99_ratio"] = "fewer than 200 POSTs in the idle or the during window"
    lag = r.get("lag")
    if lag:
        _put(m, "feed.lag_max", lag.get("max"))
        _put(m, "feed.lag_final", lag.get("final"))
    if r.get("a_count_final") is not None:
        m["peers.a_articles"] = r["a_count_final"]


# ---------------------------------------------------------------- the nodes

class Ctx:
    def __init__(self, b, mode, work):
        self.b, self.mode, self.work = b, mode, work

    def close(self, keep=False):
        self.b.stop()
        if not keep:
            shutil.rmtree(self.work / "store", ignore_errors=True)


def setup(a, spec, d):
    """Make B's store and give both nodes their rows, before A starts.  Ports are fixed first
    (driver.Node.write_config keeps a port once chosen) because each side's `peer add` names the other's."""
    mode = spec["peers"]["mode"]
    work = a.work / "B"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    prof = spec["peers"].get("prof_window_s")
    hooks = [d.HOOK] if "FN_LOAD_GC_LOG" in a.env else []      # --gc-hook: B carries the same GC hook as A
    extra = {}
    if prof:                                                  # the mechanism runs: B also carries the sb-sprof window hook
        hooks = [d.HOOKS / "w6-prof.lisp"]                    # which loads w13-idle-gc.lisp itself
        extra = {"FN_LOAD_PROF": str(work / "prof"), "FN_LOAD_PROF_WINDOW": str(prof)}
    b = d.Node(a.target, work, a.flags, a.groups, a.env["SBCL_USER_ARGS"], hooks, work / "gc.log", extra, 1.0,
               a.heap_mode)
    b.log_path = work / "fn.log"
    a.write_config()
    b.write_config()
    a.post_init = [("policy", "set", "path-identity", A_ID)]
    if mode == "feed":
        a.post_init.append(("peer", "add", "B", B_ID, "127.0.0.1", str(b.port), "fn.*", "fn.*", "127.0.0.1", "true"))
    b.init()
    (b.store / "peer-flight-profile").write_bytes(b"FNP1" + b"".join(v.to_bytes(8, "big") for v in PEER_FLIGHT_POLICY))
    b.operator("policy", "set", "path-identity", B_ID)
    if mode == "feed":
        b.operator("peer", "add", "A", A_ID, "127.0.0.1", str(a.port), "fn.*", "-", "127.0.0.1", "true")
    else:
        b.operator("peer", "add", "A", A_ID, "127.0.0.1", str(a.port), "fn.*", "-", "source-address", "127.0.0.9", "true")
        b.operator("peer", "catch-up", "A", CATCHUP_INTERVAL)
    return Ctx(b, mode, work)


# ---------------------------------------------------------------- the phase

class Poster:
    """Open-loop POSTs at rate_per_s on one connection to A; latency from the intended send time."""

    def __init__(self, run, d, rate, octets, limit=None):
        self.run, self.d, self.rate, self.octets, self.limit = run, d, rate, octets, limit
        self.samples, self.errors = [], []
        self.stop_ev = threading.Event()
        self.thread = threading.Thread(target=self._loop, daemon=True)
        self.t_start = self.t_end = None

    def _loop(self):
        try:
            c = self.run.conn()
            if c is None:
                return
            gap = 1.0 / self.rate
            t0 = time.perf_counter()
            self.t_start = time.monotonic()
            k = 0
            while not self.stop_ev.is_set() and (self.limit is None or k < self.limit):
                intended = t0 + k * gap
                now = time.perf_counter()
                if intended > now:
                    time.sleep(intended - now)
                dt = self.d.post_one(c, self.run.ctr, self.octets)
                if dt is not None:
                    self.samples.append((intended, time.perf_counter() - intended))
                k += 1
            c.close()
        except Exception as e:      # noqa: BLE001 - recorded
            self.errors.append(repr(e))
        finally:
            self.t_end = time.monotonic()

    def start(self):
        self.thread.start()
        return self

    def stop(self):
        self.stop_ev.set()
        self.thread.join()
        return self

    @property
    def alive(self):
        return self.thread.is_alive()

    @property
    def posted(self):
        return len(self.samples)


def thread_cpu(pid, clk):
    """{"tid comm": cpu seconds} for every thread of PID (utime+stime from /proc/PID/task/TID/stat)."""
    out = {}
    try:
        for t in Path("/proc/%d/task" % pid).iterdir():
            try:
                text = (t / "stat").read_text()
                comm = text[text.index("(") + 1:text.rindex(")")]
                f = text[text.rindex(")") + 2:].split()
                out["%s %s" % (t.name, comm)] = (int(f[11]) + int(f[12])) / clk
            except (OSError, ValueError, IndexError):
                continue
    except OSError:
        pass
    return out


def group_count(conn):
    """`GROUP fn.test` -> article count, or None."""
    reply = conn.line("GROUP " + GROUP).split()
    return int(reply[1]) if len(reply) >= 2 and reply[0] == b"211" else None


def fetch_articles(port, d):
    """({msgid: octets}, [msgid in article-number order]) of fn.test on the node at PORT."""
    m, _ = d._clients()
    c = m.Conn(port, buffered=True)
    try:
        status = c.line("LISTGROUP " + GROUP)
        if not status.startswith(b"211"):
            raise d.CellError("LISTGROUP: %r" % status[:60])
        numbers = []
        while True:
            line = c.readline()
            if line == b".\r\n":
                break
            numbers.append(int(line))
        out, order = {}, []
        for n in numbers:
            status = c.line("ARTICLE %d" % n)
            if not status.startswith(b"220"):
                raise d.CellError("ARTICLE %d: %r" % (n, status[:60]))
            msgid = status.split()[2].decode("ascii")
            lines = []
            while True:
                line = c.readline()
                if line == b".\r\n":
                    break
                lines.append(line[1:] if line.startswith(b"..") else line)
            out[msgid] = b"".join(lines)
            order.append(msgid)
        return out, order
    finally:
        c.close()


CKPT_SEQ = re.compile(r"CHECKPOINT auto sequence=(\d+)")


class RoundLog:
    """Incremental reader of B's owner log for `catch-up peer=` lines."""

    def __init__(self, path):
        self.path, self.seen, self.lines = Path(path), 0, []
        self.sequence = None        # last `CHECKPOINT auto sequence=N` (records committed), for count="log"

    def poll(self):
        new = []
        try:
            text = self.path.read_text(errors="replace").splitlines()
        except OSError:
            return new
        for line in text[self.seen:]:
            self.seen += 1
            mo = CKPT_SEQ.search(line)
            if mo:
                self.sequence = int(mo.group(1))
            if "catch-up peer=" in line:
                rec = parse_round_line(line)
                if rec:
                    rec["seen_t"] = time.monotonic()
                    rec["line"] = line.strip()[-400:]
                    self.lines.append(rec)
                    new.append(rec)
        return new


def run_phase(run, ph, d):
    mode = ph["mode"]
    ctx = run.peers
    a, b = run.node, ctx.b
    octets = ph.get("octets", 2048)
    rate = ph.get("rate_per_s")
    deadline_s = ph.get("deadline_s", 2400)
    m, _ = d._clients()
    out = {"mode": mode, "nominal": run.spec.get("_preloaded") or None, "rate_per_s": rate, "octets": octets}
    r = {"nominal": out["nominal"], "mode": mode, "rate_per_s": rate}

    ac = m.Conn(a.port, buffered=True)
    a_start = group_count(ac)
    r["a_count_start"] = a_start

    # idle POST baseline on A alone (before B exists as a client of A)
    poster_idle = None
    if mode == "catchup-load":
        poster_idle = Poster(run, d, rate, octets, limit=int(rate * ph.get("baseline_s", 15))).start()
        poster_idle.thread.join()
        r["post_idle"] = post_stats(poster_idle.samples)
        r["post_idle_posted"] = poster_idle.posted
    target = group_count(ac)
    r["target"] = target

    t_launch = time.monotonic()
    b.start()
    t_listen = time.monotonic()
    r["b_open_s"] = round(t_listen - t_launch, 2)
    r["heap_a"] = a.env.get("SBCL_USER_ARGS")
    r["heap_b"] = b.env.get("SBCL_USER_ARGS")
    log = RoundLog(b.log_path)
    bc = m.Conn(b.port, buffered=True)
    series, lagser, b_peak = [], [], {"vmrss": 0, "hwm": 0}
    cpu_rows = []
    a0, b0 = d.proc_snapshot(a.pid), d.proc_snapshot(b.pid)
    cpu_base = ((a0 or {}).get("cpu_s") or 0.0, (b0 or {}).get("cpu_s") or 0.0)
    thread0, base_us = thread_cpu(b.pid, d.CLK), int(time.time() * 1e6)
    poster = None
    if mode in ("feed", "catchup-load"):
        poster = Poster(run, d, rate, octets, limit=ph.get("posts")).start()
    first_import = None
    done = None
    terminal = None
    t_end = t_listen + deadline_s
    posts_over_at = None

    count_mode = ph.get("count", "group")
    pending = []

    def poll():
        nonlocal first_import
        if count_mode == "log":
            # No client command reaches B while it imports (S, 2026-10-08: the GROUP poll re-pins
            # and contaminates the pace): progress is B's own auto-checkpoint sequence line, read
            # from its log file; one record per imported article (A's checkpoint-digest sequence
            # equals its article count).
            pending.extend(log.poll())     # round lines read here are handed to the main loop below
            n = log.sequence
        else:
            n = group_count(bc)
        now = time.monotonic()
        snap = d.proc_snapshot(b.pid)
        asnap = d.proc_snapshot(a.pid)
        if snap and asnap and n is not None and snap.get("cpu_s") is not None and asnap.get("cpu_s") is not None:
            cpu_rows.append((n, asnap["cpu_s"], snap["cpu_s"], int(time.time() * 1e6), thread_cpu(b.pid, d.CLK)))
        if snap:
            b_peak["vmrss"] = max(b_peak["vmrss"], snap["vmrss"] or 0)
            b_peak["hwm"] = max(b_peak["hwm"], snap["hwm"] or 0)
        if n is not None:
            series.append((now, n))
            if first_import is None and n > 0:
                first_import = now - t_listen
            if poster is not None:
                lagser.append((now, (a_start or 0) + poster.posted, n))
        return n

    while True:
        n = poll()
        fresh, pending[:] = pending + log.poll(), []
        for rec in fresh:
            if rec["round"] == "done" and mode != "feed" and rec["position"] >= (target or 0) and done is None:
                done = rec
        if mode == "feed":
            if poster is not None and not poster.alive and posts_over_at is None:
                posts_over_at = time.monotonic()
            if posts_over_at is not None and n is not None and n >= (a_start or 0) + poster.posted:
                terminal = "feed-drained"
                break
            if posts_over_at is not None and time.monotonic() - posts_over_at > ph.get("drain_s", 300):
                terminal = "feed-drain-timeout"
                break
        elif done is not None:
            terminal = "round-done"
            break
        if b.proc is not None and b.proc.poll() is not None:
            terminal = "b-exited %s" % b.proc.returncode
            break
        if time.monotonic() > t_end:
            terminal = "deadline-%ds" % deadline_s
            break
        time.sleep(POLL_S)
    t_stop = time.monotonic()

    # A's POSTs during the window: stop the poster at the moment the round closed
    if poster is not None:
        poster.stop()
    n_final = (group_count(bc) if count_mode == "log" else poll()) if not terminal.startswith("b-exited") else None
    r["count_basis"] = ("B's CHECKPOINT auto sequence lines (no client command during the round)"
                        if count_mode == "log" else "B GROUP count polled every %.1f s" % POLL_S)
    if mode == "catchup-load" and n_final is not None:
        # the POSTs that landed after the round's cursor: wait for B to hold all of A's articles
        drain_end = time.monotonic() + ph.get("drain_s", 180)
        while time.monotonic() < drain_end and n_final < (group_count(ac) or 0):
            time.sleep(POLL_S)
            log.poll()
            n_final = poll()
    log.poll()
    t_first_series = series[0][0] if series else t_listen
    b_snap = d.proc_snapshot(b.pid) if b.pid else None
    r["b_mem"] = {"vmrss": (b_snap or {}).get("vmrss"), "hwm": (b_snap or {}).get("hwm"),
                  "peak_vmrss": b_peak["vmrss"], "peak_hwm": b_peak["hwm"], "threads": (b_snap or {}).get("threads"),
                  "cpu_s": (b_snap or {}).get("cpu_s")}
    a_snap = d.proc_snapshot(a.pid)
    if a_snap:
        out["mem"] = {k: a_snap[k] for k in ("vmrss", "hwm", "anon", "file", "pss", "threads")}
    r["terminal"] = terminal
    r["b_count_final"] = n_final
    r["a_count_final"] = group_count(ac)
    r["first_import_s"] = None if first_import is None else round(first_import, 2)
    r["rounds"] = [{k: v for k, v in rec.items() if k != "seen_t"} | {"seen_after_listen_s": round(rec["seen_t"] - t_listen, 2)}
                   for rec in log.lines]
    r["rounds_failed"] = sum(1 for rec in log.lines if rec["round"] == "failed")
    if log.lines:
        first = log.lines[0]
        r["first_round"] = {"round": first["round"], "reason": first["reason"], "imported": first["imported"],
                            "position": first["position"], "seconds_after_listen": round(first["seen_t"] - t_listen, 2)}
    r["round_outcome"] = (log.lines[-1]["round"] + (" reason=" + log.lines[-1]["reason"] if log.lines[-1]["reason"] else "")) if log.lines else None
    if mode != "feed" and done is not None:
        secs_excl = done["seen_t"] - t_listen
        secs_incl = done["seen_t"] - t_launch
        count = n_final if n_final is not None else done["position"]
        r["done_seconds_excl_start"], r["done_seconds_incl_start"] = round(secs_excl, 2), round(secs_incl, 2)
        r["pace_excl_start"], r["pace_incl_start"] = pace(count, secs_excl), pace(count, secs_incl)
        r["pace_basis"] = "B GROUP count at the round=done line / seconds from LISTENING (excl) or from process launch (incl)"
    elif mode != "feed" and n_final:
        secs_excl = t_stop - t_listen
        r["partial_pace_excl_start"] = pace(n_final, secs_excl)
        r["partial_pace_basis"] = "round never reached done (%s): B count / seconds from LISTENING" % terminal
    if mode == "feed":
        r["feed_seconds"] = round((posts_over_at or t_stop) - (poster.t_start or t_listen), 2) if poster else None
        r["drain_seconds_after_last_post"] = round(t_stop - posts_over_at, 2) if posts_over_at else None
        r["lag"] = lag_summary(lagser)
        r["lag_series"] = thin([(round(t - t_listen, 1), a_, b_) for t, a_, b_ in lagser], 200)
        r["posts_acked"] = poster.posted if poster else 0
    r["splits_per_1000_s"] = splits([(t, c) for t, c in series], t_listen)
    r["cpu_per_1000_s"] = cpu_splits(cpu_rows, cpu_base)
    cross = crossings(cpu_rows)
    r["b_threads_cpu_per_1000_s"] = thread_deltas(thread0, [row[4] for row in cross])
    if b.env.get("FN_LOAD_GC_LOG"):
        try:
            r["b_gc_per_1000"] = gc_splits(Path(b.env["FN_LOAD_GC_LOG"]).read_text().splitlines(), base_us,
                                           [row[3] for row in cross])
        except OSError as e:
            r["b_gc_per_1000"] = "unreadable: %r" % e
    r["count_series"] = thin([(round(t - t_listen, 1), c) for t, c in series], 400)
    if poster is not None:
        r["post_during"] = post_stats(poster.samples)
        r["post_during_posted"] = poster.posted
        if mode == "feed":
            cut = 1024 - (a_start or 0)
            if cut > 0 and poster.posted > cut:
                r["post_before_1024"] = post_stats(poster.samples[:cut])
                r["post_after_1024"] = post_stats(poster.samples[cut:])
        if poster.errors:
            run.errors += poster.errors
    # equality
    try:
        a_arts, a_order = fetch_articles(a.port, d)
        b_arts, b_order = fetch_articles(b.port, d)
        r["compare"] = compare(a_arts, a_order, b_arts, b_order)
        last = next((rec for rec in reversed(log.lines) if rec["round"] == "done" and rec["position"] == len(a_arts)), None)
        if mode != "feed" and last is not None:
            import blake3_ref
            want = chain_digest(a_order, a_arts, blake3_ref.blake3)
            r["chain_expected"], r["chain_done_line"] = want, last["digest"]
            r["chain_equal"] = want == last["digest"]
    except Exception as e:      # noqa: BLE001 - recorded
        r["compare_error"] = "%s: %s" % (type(e).__name__, e)
    ac.close()
    bc.close()
    # the store digest verb, offline on both stores (labelled: Path/Xref differ between nodes by design)
    b.stop()
    a.stop()
    r["store_digest"] = {}
    for name, node in (("A", a), ("B", b)):
        try:
            import subprocess
            p = subprocess.run([str(node.launcher), "--fn", "store", str(node.store), "digest"], env=node.env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1800)
            text = p.stdout.decode("utf-8", "replace")
            r["store_digest"][name] = {"rc": p.returncode, "lines": digest_lines(text), "tail": text[-300:]}
        except Exception as e:      # noqa: BLE001
            r["store_digest"][name] = {"error": repr(e)}
    da, db = (r["store_digest"].get(k, {}).get("lines") or {} for k in ("A", "B"))
    r["store_digest_canonical_equal"] = (da.get("canonical") == db.get("canonical")) if da.get("canonical") else None
    out["peers"] = r
    out["rate"] = {"b_articles_per_s_excl_start": r.get("pace_excl_start")}
    if poster is not None and poster.samples:
        out["cmd"] = {"POST": r["post_during"]}
    if poster_idle is not None:
        out["post_idle"] = r["post_idle"]
    if terminal and terminal.startswith(("b-exited", "deadline", "feed-drain-timeout")):
        out["status"] = "ok"      # the failure is the measurement; derive/judge say NOT-MEASURED with the reason
    return out
