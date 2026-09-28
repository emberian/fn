#!/usr/bin/env python3
"""The release's fundamentals F1 to F8 measured on ONE image, and judged.

    fundamentals.py run --tree TREE --revision REV [--label L] [--steps ...]
        (laptop) ships tools/fundamentals/ to hbox, runs its rows.sh on TREE
        (a tools/hbox_native.sh tree with the four images,
        --images developer,production,dtn,dtn-developer) under nohup, waits,
        fetches the outputs into planning/evidence/fundamentals-DATE-REV12/out,
        then judges them (below).  Hours: the F4 mixed hour runs beside the
        other rows; F7's module runs twice (dtn, dtn-developer).
    fundamentals.py judge --out DIR --revision REV [--write]
        reads DIR (a run's outputs), prints each row's verdict per clause and,
        with --write, writes DIR/../F1.md .. F8.md and README.md and updates
        the checklist's fundamentals table (planning/release-vVERSION.md):
        a row's status and evidence change only for a row this run measured,
        and it says MET only when every clause of its bar is met by this
        evidence.  A clause the tool cannot measure (a proof, an account it
        has no access to, a bound nobody has named) keeps the row OPEN and
        is named.

The methods are the fundamentals scoreboard's (planning/evidence/
fundamentals-2026-09-27/README.md; tools/fundamentals/ holds its harness,
maintained here): every row pinned to four cores (ROW_CORES, default 20-23)
in its own systemd scope, one after another, the box's load, ARC and three
largest processes logged before each; the F4 mixed hour on four cores of
its own (16-19) at the same time, then the stall case there; the native
modules as hbox_native.sh runs them.  Where a clause names two disks (F3:
hbox's NVMe and its ZFS pool; the public edge's with --edge-ssh) both are
measured.  No row is a before/after comparison unless it says so.

The bars are parameters (defaults: the checklist as written, and where it
leaves a number open, the reading named here and in the record):
  F1  --f1-slope-max 1.5 (B per payload octet after a reopen: "about 1"),
      --f1-reopen-mb 128, --f1-reopen hwm|rss (the 1,000-post reopen's peak,
      VmHWM, by default; VmRSS after it is the lenient reading)
  F2  --f2-r-evidence PATH (the committed record discharging R at every host
      entry); the lookup count needs a `lookups' figure in sr_measure's JSON
  F3  --f3-fsync-max 1.0 (fsyncs per POST at 8 posters: "well under 7");
      the edge disk's POST/s needs --edge-ssh
  F4  planning/design-time-model-2026-09-27.md section 4: F4-R, every served
      read and every status/health within D_R = 3 x Q_max, in the mixed hour
      and under the injected 30 s stall; F4-W, every POST answered within
      H + Q_max.  --f4-q-max-ms Q_MAX and --f4-h-ms H: until they are given
      (Q_max is measured by nobody yet; H is slice 2's) the row is OPEN and
      says which is missing.  --f4-client-deadline-ms 10000: every control
      request answered within it (the qualification's observable).
  F5  a stated figure per idle connection and tests.test_native_mux OK
  F6  --f6-bar-s 10 (every open at 20,000 and 40,000, both modes): from the
      scale curve when step f6c ran (tools/scale_curve.py: full replay and
      checkpoint opens at 1k .. 100k, judged at the next point up, 25k and
      50k, with the fit's 1M extrapolation named; F8 names the curve's
      memory extrapolation beside its own bars), else from step f6's
      fixtures (chain-20000, t40k-2k-cp5)
  F7  --f7-reading as-written (the module wholly OK on dtn and on
      dtn-developer) or scn077-on-dtn (SCN-077's case OK on dtn, the module
      wholly OK on dtn-developer: F7.md's alternative reading, ember's call)
  F8  --f8-reserved-mb 256, --f8-in-use-mb 128 (--f8-in-use rss|hwm, rss
      as the scoreboard read it), --f8-reopen-mb 256
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import re
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HOST = "hbox"
MB = 1_000_000
ROW_IDS = ("F1", "F2", "F3", "F4", "F5", "F6", "F7", "F8")


# --------------------------------------------------------------------------
# reading a run's outputs

def load(out: Path, name: str):
    p = out / name
    if not p.is_file() or p.stat().st_size == 0:
        return None
    try:
        return json.loads(p.read_text())
    except ValueError:
        return None


def after_gc(text: str | None) -> int | None:
    m = re.search(r"dynamic-usage-after-gc (\d+)", text or "")
    return int(m.group(1)) if m else None


def driver_lines(out: Path, prefix: str) -> list[str]:
    p = out / "driver.log"
    if not p.is_file():
        return []
    return [l for l in p.read_text().splitlines() if l.split(" ", 2)[1:2] and l.split(" ", 2)[1].startswith(prefix)]


def load_of(out: Path, prefix: str) -> str:
    """The 1-minute load averages logged before PREFIX's rows: 'a to b'."""
    vals = []
    for line in driver_lines(out, prefix):
        m = re.search(r" load: ([\d.]+)", line)
        if m:
            vals.append(float(m.group(1)))
    if not vals:
        return "not logged"
    lo, hi = min(vals), max(vals)
    return f"{lo:.0f}" if round(lo) == round(hi) else f"{lo:.0f} to {hi:.0f}"


def verdict_line(out: Path, label: str) -> str | None:
    """A native module's verdict line (tools/test_budget.py --verdict of its log)."""
    p = out / "logs" / f"{label}.verdict"
    if p.is_file() and p.read_text().strip():
        return p.read_text().strip().splitlines()[0]
    log = out / "logs" / f"{label}.log"
    if not log.is_file():
        return None
    r = subprocess.run([sys.executable, str(ROOT / "tools" / "test_budget.py"), "--verdict", str(log)],
                       capture_output=True, text=True)
    return (r.stdout.strip().splitlines() or [None])[0]


class Row:
    def __init__(self, rid: str):
        self.id = rid
        self.clauses: list[tuple[str, bool | None, str]] = []  # (clause, met, what)
        self.measured = False
        self.notes: list[str] = []
        self.commands: list[str] = []
        self.raw: list[str] = []

    def clause(self, name: str, met: bool | None, what: str):
        self.clauses.append((name, met, what))

    @property
    def met(self) -> bool:
        return self.measured and bool(self.clauses) and all(m is True for _, m, _ in self.clauses)


def mib(kib) -> str:
    return f"{int(kib) / 1024:.1f} MiB"


# --------------------------------------------------------------------------
# the rows

def f1(out: Path, a) -> Row:
    r = Row("F1")
    s = {n: load(out, f"f1-slope-{n}.json") for n in ("a1000x2048", "a1000x8000", "a2000x2048")}
    floor = load(out, "f8-floor-prod.json")
    if not (s["a1000x2048"] and s["a1000x8000"]) and not floor:
        return r
    r.measured = True
    r.commands.append("taskset -c ROW_CORES python3 tools/fundamentals/slope.py TREE build/fn-host-developer-heap WORK --posts N --octets L (MemoryMax=8G)")
    r.commands.append("taskset -c ROW_CORES python3 tools/fundamentals/floor.py TREE build/fn-host WORK --posts 1000 --octets 2048 (MemoryMax=8G)")
    rows = []
    for n, d in s.items():
        if not d:
            continue
        e, p, o = after_gc(d.get("empty")), after_gc(d.get("posted")), after_gc(d.get("reopen"))
        if None in (e, p, o):
            r.notes.append(f"{n}: no live-heap figure (the heap hook did not report; {n}.err)")
            continue
        rows.append((n, d["posts"], d["octets"], e, p - e, o - e))
    table = ["| N x L | empty (B) | after POSTs, minus empty | after reopen, minus empty | reopen per payload octet |",
             "| --- | --- | --- | --- | --- |"]
    for n, posts, octets, e, dp, do in rows:
        table.append(f"| {posts:,} x {octets:,} | {e:,} | {dp:,} | {do:,} | {do / (posts * octets):.2f} B |")
    r.raw += table
    by = {n: (posts, octets, dp, do) for n, posts, octets, _, dp, do in rows}
    if "a1000x2048" in by and "a1000x8000" in by:
        (n1, l1, p1, o1), (n2, l2, p2, o2) = by["a1000x2048"], by["a1000x8000"]
        slope_open = (o2 - o1) / (n1 * (l2 - l1))
        slope_post = (p2 - p1) / (n1 * (l2 - l1))
        per_open = o1 / n1 - slope_open * l1
        per_post = p1 / n1 - slope_post * l1
        r.clause(f"retained heap about 1 B per payload octet (read: at most {a.f1_slope_max} B after a reopen)",
                 slope_open <= a.f1_slope_max,
                 f"{slope_open:.2f} B per payload octet after a reopen ({slope_post:.2f} while posting)")
        r.clause("per-record metadata stated", True,
                 f"{per_open / 1000:.1f} KB per record after a reopen, {per_post / 1000:.1f} KB while posting; "
                 f"at 2 KiB the whole increment is {o1 / (n1 * l1):.2f} B per payload octet after a reopen")
    else:
        r.clause("retained heap per payload octet", None, "the 1,000 x 2,048 and 1,000 x 8,000 rows did not both report")
    if floor and floor.get("after_reopen"):
        rss, hwm = floor["after_reopen"]["rss_kib"], floor["after_reopen"]["hwm_kib"]
        judged = hwm if a.f1_reopen == "hwm" else rss
        ok = judged * 1024 < a.f1_reopen_mb * MB
        r.clause(f"the 1,000-post reopen under {a.f1_reopen_mb:g} MB RSS "
                 f"({'VmHWM: the peak through the reopen' if a.f1_reopen == 'hwm' else 'VmRSS after it'})", ok,
                 f"VmRSS {mib(rss)}, VmHWM {mib(hwm)} after the reopen ({floor.get('status_open', '?')}, {floor.get('reopen_s')} s)")
    else:
        r.clause(f"the 1,000-post reopen under {a.f1_reopen_mb} MB RSS", None, "floor.py reported no reopen")
    r.notes.append(f"load {load_of(out, 'f1-')} (slope rows), {load_of(out, 'f8')} (the reopen)")
    return r


def f2(out: Path, a) -> Row:
    r = Row("F2")
    runs = {n: load(out, f"f2-{n}.json") for n in ("load", "after-1", "after-2", "before-1", "before-2")}
    if not any(runs.values()):
        return r
    r.measured = True
    r.commands.append("taskset -c ROW_CORES python3 tools/fundamentals/sr_measure.py --image build/fn-host-developer --fixture FX --articles 10000 --client bulk (MemoryMax=40G)")
    table = ["| run | GROUP reply | ARTICLE by number | OVER 40 | OVER 1-2000 | owner CPU per OVER 1-2000 |",
             "| --- | --- | --- | --- | --- | --- |"]
    for n, d in runs.items():
        if d:
            table.append(f"| {n} | {d.get('group_reply', '?')} | {d['article_by_number']['median_ms']} | "
                         f"{d['over_40']['median_ms']} | {d['over_2000']['median_ms']} | {d['over_2000'].get('owner_cpu_ms_per_op')} ms |")
    r.raw += table
    ev = a.f2_r_evidence
    r.clause("R established at every host entry (fn-sca-join discharged)",
             bool(ev) and (ROOT / ev).is_file(),
             f"cited: {ev}" if ev else "no record given (--f2-r-evidence); lane sca-join owns the discharge")
    has_lookups = any(d and "lookups" in d for d in runs.values())
    r.clause("index lookups per served command measured on the served path", has_lookups,
             "counted by sr_measure" if has_lookups else "nothing counts them on the served path (sr_measure reports no `lookups')")
    before = runs["before-1"] or runs["before-2"]
    r.clause("before/after at N = 10,000", bool(before and (runs["after-1"] or runs["after-2"])),
             "measured against F2_BEFORE" if before else "no before image opens this store (F2_BEFORE not given or refused)")
    r.clause("GROUP/LISTGROUP/ARTICLE/OVER read v/fn-cat", None,
             "a source property (tests/test_native_served_cost.py), not measured here")
    r.notes.append(f"load {load_of(out, 'f2-')}")
    return r


def f3(out: Path, a) -> Row:
    r = Row("F3")
    runs = {fs: load(out, f"f3-gc-{fs}.json") for fs in ("nvme", "tank", "edge")}
    if not (runs["nvme"] or runs["tank"]):
        return r
    r.measured = True
    r.commands.append("FN_TREE=TREE taskset -c ROW_CORES python3 tools/fundamentals/gc_measure.py --image build/fn-host-developer --dir D --connections 1,8,32 --fsync-posts 64 (MemoryMax=110G)")
    table = ["| disk | fsync per POST (8 posters) | POST/s at each poster count | p99 ms |", "| --- | --- | --- | --- |"]
    worst = None
    for fs, d in runs.items():
        if not d:
            continue
        per = (d.get("fsync") or {}).get("per_post")
        if per is not None:
            worst = per if worst is None else max(worst, per)
        rates = " / ".join(f"{row['post_per_s']}" for row in d.get("rows", []))
        p99 = " / ".join(f"{row['latency']['p99_ms']}" for row in d.get("rows", []))
        cons = "/".join(str(row["connections"]) for row in d.get("rows", []))
        table.append(f"| {fs} | {per} | {rates} ({cons}) | {p99} |")
    r.raw += table
    r.clause(f"fsyncs per POST at 8 posters well under 7 (read: at most {a.f3_fsync_max})",
             worst is not None and worst <= a.f3_fsync_max,
             f"worst of the disks measured: {worst}")
    edge = runs["edge"]
    r.clause("POST/s on the public node's edge disk stated", bool(edge and edge.get("rows")),
             "measured over --edge-ssh" if edge else "not measured: no account on the edge (PKT-751); pass --edge-ssh")
    r.notes.append(f"load {load_of(out, 'f3-')}; 'batch 8' is 8 concurrent posters (PKT-828 b)")
    return r


def f4(out: Path, a) -> Row:
    r = Row("F4")
    d = load(out, "f4-mixed.json")
    stall = (out / "f4-stall.log").read_text(errors="replace") if (out / "f4-stall.log").is_file() else ""
    if not d:
        return r
    r.measured = True
    r.commands.append("FN_MIXED_AGENTS=0 FN_MIXED_CONTROL=1 taskset -c F4_CORES python3 tools/fundamentals/mixed.py WORK SECONDS (MemoryMax=40G)")
    r.commands.append("taskset -c F4_CORES python3 -m unittest -v tests.test_native_slow_disk (the 30 s stall)")
    lat = d["latency"]
    table = ["| class | n | p50 ms | p95 ms | p99 ms | max ms |", "| --- | --- | --- | --- | --- | --- |"]
    for k, v in lat.items():
        table.append(f"| {k} | {v['n']:,} | {v['p50_ms']:.1f} | {v['p95_ms']:.1f} | {v['p99_ms']:.1f} | {v['max_ms']:,.0f} |")
    r.raw += table
    events = d.get("events", [])
    kinds = {}
    for e in events:
        kinds[e.get("kind")] = kinds.get(e.get("kind"), 0) + 1
    control = [e for e in events if e.get("kind") in ("status", "health", "group-create", "control-grant")]
    bad = [e for e in control if e.get("rc") != 0]
    ctl_max = max((v["max_ms"] for k, v in lat.items() if k.startswith(("status", "health", "control"))), default=None)
    r.clause(f"every control request answered within the {a.f4_client_deadline_ms / 1000:g} s client deadline",
             not bad and ctl_max is not None and ctl_max <= a.f4_client_deadline_ms,
             f"{len(control) - len(bad)} of {len(control)} answered with exit 0; slowest {ctl_max:,.0f} ms")
    read_classes = [k for k in lat if k.startswith("reader-") or k in ("status-live", "health-live")]
    read_max = max(lat[k]["max_ms"] for k in read_classes) if read_classes else None
    m = re.search(r"reads n=(\d+) max=([\d.]+)s.*?status n=(\d+) max=([\d.]+)s.*?health max ([\d.]+)s", stall, re.S)
    stall_ok = bool(re.search(r"^OK", stall, re.M))
    stall_max = max(float(m.group(2)), float(m.group(4)), float(m.group(5))) * 1000 if m else None
    if a.f4_q_max_ms is None:
        r.clause("F4-R: every served read and status/health within D_R = 3 x Q_max", None,
                 f"Q_max not given (--f4-q-max-ms; nobody measures it yet): mixed-hour read/status max {read_max:,.0f} ms"
                 + (f", under the 30 s stall {stall_max:.0f} ms" if stall_max is not None else ", stall case not run"))
    else:
        dr = 3 * a.f4_q_max_ms
        r.clause(f"F4-R: every served read and status/health within D_R = 3 x {a.f4_q_max_ms:g} = {dr:g} ms",
                 read_max is not None and read_max <= dr and stall_ok and stall_max is not None and stall_max <= dr,
                 f"mixed-hour max {read_max:,.0f} ms; under the 30 s stall {stall_max if stall_max is not None else '?'} ms"
                 f" (tests.test_native_slow_disk {'OK' if stall_ok else 'not OK'})")
    lost = kinds.get("post-error", 0)
    post_max = lat.get("post", {}).get("max_ms")
    if a.f4_q_max_ms is None or a.f4_h_ms is None:
        r.clause("F4-W: every POST answered within H + Q_max", None,
                 f"{'H' if a.f4_h_ms is None else ''}{' and ' if a.f4_h_ms is None and a.f4_q_max_ms is None else ''}"
                 f"{'Q_max' if a.f4_q_max_ms is None else ''} not given (H is slice 2's): "
                 f"{lat.get('post', {}).get('n', 0):,} POSTs, {lost} unanswered, max {post_max:,.0f} ms")
    else:
        w = a.f4_h_ms + a.f4_q_max_ms
        r.clause(f"F4-W: every POST answered within H + Q_max = {w:g} ms", lost == 0 and post_max is not None and post_max <= w,
                 f"{lost} unanswered; max {post_max:,.0f} ms")
    r.clause("no reader error and the owner alive at the end", kinds.get("reader-error", 0) == 0 and d.get("owner_alive_at_end", False),
             f"reader errors {kinds.get('reader-error', 0)}; owner alive at the end: {d.get('owner_alive_at_end')}")
    r.notes.append(f"the hour: {d.get('hour_seconds')} s from {(out / 'f4-start.txt').read_text().strip() if (out / 'f4-start.txt').is_file() else '?'}, "
                   f"load {load_of(out, 'f4')} at its start and {load_of(out, '')} over the run; mutating control is the design's named exception, its tail stated above")
    if m:
        r.notes.append("the stall case: " + " ".join(stall[m.start():m.end()].split()))
    return r


def f5(out: Path, a) -> Row:
    r = Row("F5")
    runs = [load(out, f"f5-mux-{i}.json") for i in (1, 2)]
    runs = [d for d in runs if d]
    native = verdict_line(out, "f5-native-mux")
    if not runs and not native:
        return r
    r.measured = True
    r.commands.append("taskset -c ROW_CORES python3 tools/mux_measure.py build/fn-host-developer WORK --idle 1000 --active 200 --overs 10 --posts 50 (MemoryMax=24G), twice")
    r.commands.append("tests.test_native_mux on the developer and production images (hbox_native.sh's environment)")
    per = [d["idle_held"]["rss_per_connection_kib"] for d in runs if d.get("idle_held")]
    r.raw += ["| run | RSS at rest | RSS with 1,000 idle held | per idle connection | threads |", "| --- | --- | --- | --- | --- |"]
    for i, d in enumerate(runs, 1):
        r.raw.append(f"| {i} | {d['rest']['rss_kib']:,} KiB | {d['idle_held']['rss_kib']:,} KiB | {d['idle_held']['rss_per_connection_kib']} KiB | {d['idle_held']['threads']} |")
    r.clause("memory per idle connection measured and stated", bool(per) and all(d.get("errors_total", 1) == 0 for d in runs),
             f"{min(per):.2f} to {max(per):.2f} KiB per idle connection (pessimistic {max(per):.2f})" if per else "no figure")
    r.clause("the capacity check against memory (tests.test_native_mux)", bool(native and ": OK" in native), native or "not run")
    r.notes.append(f"load {load_of(out, 'f5')}")
    return r


# tools/scale_curve.py's models (the fitted curve's g(N)).
CURVE_G = {"constant": lambda n: 0.0, "log N": math.log, "N": float,
           "N log N": lambda n: n * math.log(n), "N^2": lambda n: float(n) * n}
CURVE_OPENS = (("open_replay.s", "full replay"), ("open_checkpoint.s", "from its checkpoint"))


def f6_curve(curve: dict, a) -> Row:
    """F6 from the scale curve (tools/scale_curve.py, step f6c): the owner's open
    by full replay and from a checkpoint at N = 1k .. 100k.  A bar size is judged
    by the MEASURED point at the least curve N at or above it (25k for 20k, 50k
    for 40k: an open that grows with N is no faster at the smaller store); the
    fitted model's value at the bar size and its extrapolation to 1M are named
    beside it, and a flagged fit (ambiguous, bend, steepens, failed) is named."""
    r = Row("F6")
    r.measured = True
    meta = curve.get("meta", {})
    r.commands.append("python3 tools/scale_curve.py run --image build/fn-host --probes "
                      "open_replay,checkpoint,open_checkpoint --jobs 1 --cores 4 (the curve "
                      "fixture's copies on /dev/shm, MemoryMax per point)")
    ns = sorted(int(n) for n in curve.get("points", {}))
    r.raw += ["| open | " + " | ".join(f"{n // 1000}k" for n in ns) + " | fit | resid | at 1M | flags |",
              "|---|" + "---|" * (len(ns) + 4)]
    for series, mode in CURVE_OPENS:
        f = (curve.get("fits") or {}).get(series, {})
        vals = [curve["points"][str(n)].get("values", {}).get(series) for n in ns]
        r.raw.append(f"| {mode} | " + " | ".join("-" if v is None else f"{v:.2f}" for v in vals)
                     + f" | {f.get('best', '-')} | {f.get('residual', float('nan')):.3f} | "
                     + (f"{f['at_1M']:.1f} s" if f.get("at_1M") is not None else "-")
                     + f" | {'; '.join(f.get('flags') or []) or '-'} |")
    for size in (20000, 40000):
        at = next((n for n in ns if n >= size), None)
        values, where = [], []
        for series, mode in CURVE_OPENS:
            v = curve["points"][str(at)].get("values", {}).get(series) if at else None
            values.append(v)
            text = f"{mode}: {v:.2f} s measured at {at // 1000}k" if v is not None else f"{mode}: not measured"
            f = (curve.get("fits") or {}).get(series, {})
            if f.get("best") in CURVE_G:
                m = f["models"][f["best"]]
                text += f" (fit {f['best']}: {m['a'] + m['b'] * CURVE_G[f['best']](size):.2f} s at {size // 1000}k)"
            where.append(text)
        worst = None if None in values else max(values)
        r.clause(f"the owner's open at {size // 1000}k under {a.f6_bar_s:g} s (both modes; the curve's "
                 f"next point up)", worst is not None and worst < a.f6_bar_s, "; ".join(where))
    r.notes.append(f"the scale curve, one point per N on 4 cores; load {' '.join(meta.get('load_start', []))} "
                   f"at the start, {' '.join(meta.get('load_end', []))} at the end; wall {meta.get('wall_s')} s; "
                   "the extrapolation to 1M is the fitted model's, not a measurement")
    return r


def f6(out: Path, a) -> Row:
    curve = load(out, "f6-curve/curve.json")
    if curve:
        return f6_curve(curve, a)
    r = Row("F6")
    runs = {(fx, mode): load(out, f"f6-{fx}-{mode}.json") for fx in ("chain-20000", "t40k-2k-cp5") for mode in ("asis", "reckpt")}
    if not any(runs.values()):
        return r
    r.measured = True
    r.commands.append("taskset -c ROW_CORES python3 tools/fundamentals/reopen_ckpt.py TREE build/fn-host-developer-heap FIXTURE WORK JSON MODE (MemoryMax=40G, /dev/shm)")
    r.raw += ["| store | mode | open (s) | open line | VmRSS / VmHWM | checkpoint verb |", "| --- | --- | --- | --- | --- | --- |"]
    worst = {}
    for (fx, mode), d in runs.items():
        if not d:
            continue
        res = d.get("residency_open") or {}
        ck = f"{d['checkpoint_seconds']:.1f} s" if d.get("checkpoint_seconds") is not None else "-"
        r.raw.append(f"| {fx} | {mode} | {d.get('open_seconds', float('nan')):.2f} | {' '.join(d.get('open_line') or ['?'])} | "
                     f"{mib(res.get('rss_kib', 0))} / {mib(res.get('hwm_kib', 0))} | {ck} |")
        size = "20k" if fx.startswith("chain-20000") else "40k"
        if d.get("open_seconds") is not None:
            worst[size] = max(worst.get(size, 0), d["open_seconds"])
    for size in ("20k", "40k"):
        w = worst.get(size)
        r.clause(f"the owner's open at {size} under {a.f6_bar_s:g} s (both modes)", w is not None and w < a.f6_bar_s,
                 f"slowest {w:.2f} s" if w is not None else "not measured")
    r.notes.append(f"load {load_of(out, 'f6-')}; one run per row; fixtures chain-20000 and t40k-2k-cp5 copied, never opened in place")
    return r


def f7(out: Path, a) -> Row:
    r = Row("F7")
    v = {img: verdict_line(out, f"f7-bp-{img}") for img in ("dtn", "dtn-developer")}
    if not any(v.values()):
        return r
    r.measured = True
    r.commands.append("tests.test_bp_fragment_node_native with FN_NATIVE_DEVELOPER_HOST = build/fn-host-dtn, then build/fn-host-dtn-developer (24G scope, unpinned)")

    def scn077(img):
        p = out / "logs" / f"f7-bp-{img}.log"
        text = p.read_text(errors="replace") if p.is_file() else ""
        ran = re.search(r"^test_ten_mebibyte_article_through_four_kib_fragments .*\.\.\. SCN-077 adu-octets=", text, re.M)
        return bool(ran) and not re.search(r"^(FAIL|ERROR): test_ten_mebibyte_article_through_four_kib_fragments", text, re.M)
    for img, line in v.items():
        r.raw.append(f"- {img}: {line or 'not run'}; SCN-077's case {'ok' if scn077(img) else 'not ok'}")
    ok = {img: bool(line and ": OK" in line) for img, line in v.items()}
    r.clause("tests.test_bp_fragment_node_native wholly OK on dtn-developer", ok["dtn-developer"], v["dtn-developer"] or "not run")
    if a.f7_reading == "as-written":
        r.clause("tests.test_bp_fragment_node_native wholly OK on dtn", ok["dtn"], v["dtn"] or "not run")
    else:
        r.clause("SCN-077 (the 10 MiB ADU) OK on dtn (reading scn077-on-dtn)", scn077("dtn"), v["dtn"] or "not run")
    r.clause("SCN-077 delivering a 10 MiB ADU", scn077("dtn") and scn077("dtn-developer"),
             "test_ten_mebibyte_article_through_four_kib_fragments on both images")
    return r


def f8(out: Path, a) -> Row:
    r = Row("F8")
    d = load(out, "f8-floor-prod.json")
    if not d:
        return r
    r.measured = True
    r.commands.append("taskset -c ROW_CORES python3 tools/fundamentals/floor.py TREE build/fn-host WORK --posts 1000 --octets 2048 (MemoryMax=8G, /dev/shm)")
    fig = re.search(r"heap=(\d+) MB", d.get("figure_line_after") or "")
    fig0 = re.search(r"heap=(\d+) MB", d.get("figure_line") or "")
    res = re.search(r"reservation=(\d+) MB", d.get("init") or "")
    reserved = [int(x.group(1)) for x in (fig, res) if x]
    r.clause(f"under {a.f8_reserved_mb} MB reserved (the launcher's heap figure after 1,000 POSTs and the init's reservation)",
             bool(reserved) and max(reserved) < a.f8_reserved_mb,
             f"figure {fig0.group(1) if fig0 else '?'} MB empty, {fig.group(1) if fig else '?'} MB after 1,000; init reservation {res.group(1) if res else '?'} MB")
    after = d.get("after_1000") or {}
    key = "rss_kib" if a.f8_in_use == "rss" else "hwm_kib"
    use = after.get(key)
    r.clause(f"under {a.f8_in_use_mb} MB in use after 1,000 posts ({'VmRSS' if key == 'rss_kib' else 'VmHWM'})",
             use is not None and use * 1024 < a.f8_in_use_mb * MB,
             f"VmRSS {mib(after.get('rss_kib', 0))}, VmHWM {mib(after.get('hwm_kib', 0))}, anonymous {mib(after.get('anonymous_kib', 0))}")
    fl = (d.get("reopen_post_floor") or {}).get("floor_mb")
    r.clause(f"a reopen of that store under {a.f8_reopen_mb} MB (least heap that reopens, serves and takes 50 POSTs)",
             fl is not None and fl < a.f8_reopen_mb, f"{fl} MB (failed at {(d.get('reopen_post_floor') or {}).get('failed_at_mb')} MB)")
    r.notes.append(f"load {load_of(out, 'f8')}; the small preset: {d.get('flags')}")
    curve = load(out, "f6-curve/curve.json")
    for series in ("open_checkpoint.rss_kib", "open_checkpoint.hwm_kib", "open_checkpoint.anon_peak_kib"):
        f = ((curve or {}).get("fits") or {}).get(series)
        if f and f.get("at_1M") is not None:
            # Information, not a clause: F8's bars are at 1,000 posts.
            r.raw.append(f"- scale curve (F6's step f6c): {series} fits {f['best']} (residual "
                         f"{f['residual']:.3f}); extrapolated {mib(f['at_1M'])} at 1M, "
                         f"{mib(f['at_10M'])} at 10M{'; FLAGGED: ' + '; '.join(f['flags']) if f['flags'] else ''}")
    return r


JUDGES = (f1, f2, f3, f4, f5, f6, f7, f8)


# --------------------------------------------------------------------------
# the records and the checklist

def record(r: Row, rev: str, evdir: Path, bar: str) -> str:
    lines = [f"# {r.id} on {rev[:12]} (tools/fundamentals.py)", "",
             f"**Coordinate:** {rev} on hbox; the shared conditions and the images are in README.md.", "",
             f"**Bar (the checklist):** {bar}", "",
             f"**Verdict: {'MET' if r.met else 'OPEN'}.**", ""]
    for name, met, what in r.clauses:
        word = "met" if met is True else "NOT MET" if met is False else "NOT MEASURABLE HERE"
        lines.append(f"- **{name}**: {word}. {what}.")
    lines.append("")
    if r.raw:
        lines += ["## Figures", ""] + r.raw + [""]
    if r.notes:
        lines += ["## Conditions and scope", ""] + [f"- {n}" for n in r.notes] + [""]
    if r.commands:
        lines += ["## Commands", ""] + [f"- `{c}`" for c in r.commands] + [""]
    lines.append(f"Raw output: {evdir.name}/out/.")
    return "\n".join(lines) + "\n"


def checklist_path(rev: str) -> Path:
    version = subprocess.run(["git", "-C", str(ROOT), "show", f"{rev}:VERSION"], capture_output=True, text=True).stdout.strip() \
        or (ROOT / "VERSION").read_text().strip()
    return ROOT / "planning" / f"release-v{version}.md"


def table_rows(text: str) -> dict[str, list[str]]:
    rows = {}
    on = False
    for line in text.splitlines():
        if "<!-- fundamentals -->" in line:
            on = True
            continue
        if "<!-- end fundamentals -->" in line:
            break
        m = re.match(r"^\| *(F\d+) *\|", line)
        if on and m:
            rows[m.group(1)] = [c.strip() for c in line.strip().strip("|").split("|")]
    return rows


def update_checklist(path: Path, verdicts: dict[str, tuple[bool, str]]) -> None:
    text = path.read_text()
    out, on = [], False
    for line in text.splitlines(keepends=True):
        if "<!-- fundamentals -->" in line:
            on = True
        elif "<!-- end fundamentals -->" in line:
            on = False
        m = re.match(r"^\| *(F\d+) *\|", line)
        if on and m and m.group(1) in verdicts:
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            met, evidence = verdicts[m.group(1)]
            cells[3] = "MET" if met else "OPEN"
            cells[4] = evidence
            line = "| " + " | ".join(cells) + " |\n"
        out.append(line)
    path.write_text("".join(out))


def readme(rev: str, out: Path, rows: list[Row], a) -> str:
    images = (out / "images.sha256").read_text().strip() if (out / "images.sha256").is_file() else "(images.sha256 missing)"
    driver = (out / "driver.log").read_text().splitlines() if (out / "driver.log").is_file() else []
    first = driver[0].split()[0] if driver else "?"
    last = driver[-1].split()[0] if driver else "?"
    loads = [float(m.group(1)) for l in driver if (m := re.search(r" load: ([\d.]+)", l))]
    lines = [f"# Fundamentals F1 to F8 on one image: {rev[:12]} (tools/fundamentals.py)", "",
             "## The coordinate", "",
             f"- **Source revision:** `{rev}`.",
             f"- **Images:** the tools/hbox_native.sh tree `{a.tree or '?'}` (developer, production, dtn, dtn-developer)"
             " and the heap image built on it by tools/fundamentals/build_heap_image.sh (a measuring instrument, never a release image).",
             "- **Core SHA-256s:**", "", "```", images, "```", "",
             "## Conditions", "",
             f"- hbox, {first} to {last}; the 1-minute load before the rows was "
             + (f"{min(loads):.0f} to {max(loads):.0f}" if loads else "not logged") + " (out/driver.log: load, ARC and the three largest processes before every row).",
             f"- Rows pinned to cores {a.row_cores} one after another, each in its own systemd scope; the F4 hour on {a.f4_cores} at the same time, then the stall case there; native modules unpinned in a 24G scope.",
             "- One image, stated load: no row is a before/after comparison unless its record says so.", "",
             "## The bars as read", "",
             f"F1 slope at most {a.f1_slope_max} B/octet, reopen under {a.f1_reopen_mb} MB ({a.f1_reopen}); F3 at most {a.f3_fsync_max} fsync/POST; "
             f"F4 Q_max {a.f4_q_max_ms}, H {a.f4_h_ms}, client deadline {a.f4_client_deadline_ms} ms; F6 under {a.f6_bar_s} s; "
             f"F7 {a.f7_reading}; F8 reserved {a.f8_reserved_mb} MB, in use {a.f8_in_use_mb} MB ({a.f8_in_use}), reopen {a.f8_reopen_mb} MB.", "",
             "## The rows", "", "| ID | record | status here |", "| --- | --- | --- |"]
    for r in rows:
        if r.measured:
            lines.append(f"| {r.id} | {r.id}.md | {'MET' if r.met else 'OPEN'} |")
        else:
            lines.append(f"| {r.id} | - | not measured in this run |")
    return "\n".join(lines) + "\n"


def judge(a) -> int:
    out = Path(a.out).resolve()
    rev = subprocess.run(["git", "-C", str(ROOT), "rev-parse", a.revision], capture_output=True, text=True).stdout.strip() or a.revision
    rows = [j(out, a) for j in JUDGES]
    clpath = Path(a.checklist) if a.checklist else checklist_path(rev)
    bars = {k: v[2] for k, v in table_rows(clpath.read_text()).items()} if clpath.is_file() else {}
    for r in rows:
        if not r.measured:
            print(f"{r.id}: not measured in this run")
            continue
        print(f"{r.id}: {'MET' if r.met else 'OPEN'}")
        for name, met, what in r.clauses:
            print(f"    [{'met' if met is True else 'NOT' if met is False else ' ? '}] {name}: {what}")
    if not a.write:
        return 0
    evdir = out.parent
    verdicts = {}
    for r in rows:
        if r.measured:
            (evdir / f"{r.id}.md").write_text(record(r, rev, evdir, bars.get(r.id, "(not in the checklist)")))
            verdicts[r.id] = (r.met, str((evdir / f"{r.id}.md").relative_to(ROOT)))
    (evdir / "README.md").write_text(readme(rev, out, rows, a))
    if clpath.is_file() and verdicts:
        update_checklist(clpath, verdicts)
        print(f"fundamentals: {len(verdicts)} rows written to {clpath}; records in {evdir}")
    return 0


# --------------------------------------------------------------------------
# the run

def sh(cmd: str, **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, shell=True, text=True, **kw)


def run(a) -> int:
    rev = subprocess.run(["git", "-C", str(ROOT), "rev-parse", a.revision], capture_output=True, text=True).stdout.strip() or a.revision
    day = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    label = a.label or f"{rev[:12]}-{dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')}"
    if not re.fullmatch(r"[A-Za-z0-9._-]+", label):
        raise SystemExit("fundamentals: bad --label")
    box = f"/tank/fn/scratch/fundamentals/{label}"
    evdir = ROOT / "planning" / "evidence" / f"fundamentals-{day}-{rev[:12]}"
    q = shlex.quote
    env = " ".join(f"{k}={q(str(v))}" for k, v in (("ROW_CORES", a.row_cores), ("F4_CORES", a.f4_cores), ("F4_SECONDS", a.f4_seconds),
                                                   ("F2_BEFORE", a.f2_before or ""), ("EDGE_SSH", a.edge_ssh or "")))
    steps = q(a.steps) if a.steps else ""
    if a.dry_run:
        print(f"would: rsync tools/fundamentals/ {HOST}:{box}/harness/")
        print(f"would ({HOST}): cd {box} && {env} nohup sh harness/rows.sh {a.tree} {box}/out {steps} > {box}/rows.log 2>&1; date -u > {box}/done")
        print(f"would: rsync {HOST}:{box}/out/ {evdir}/out/ and judge it")
        return 0
    if sh(f"ssh -n -o BatchMode=yes {HOST} test -x {q(a.tree)}/build/fn-host-developer").returncode:
        raise SystemExit(f"fundamentals: {HOST}:{a.tree}/build/fn-host-developer is not an image (build the tree with tools/hbox_native.sh --images developer,production,dtn,dtn-developer)")
    if sh(f"ssh -n -o BatchMode=yes {HOST} mkdir -p {box}/out").returncode or \
            sh(f"rsync -a --delete {q(str(ROOT / 'tools' / 'fundamentals'))}/ {HOST}:{box}/harness/").returncode:
        raise SystemExit("fundamentals: shipping the harness failed")
    start = f"cd {box} && rm -f done && (env {env} sh harness/rows.sh {q(a.tree)} {box}/out {steps} > rows.log 2>&1; date -u > done) > /dev/null 2>&1 < /dev/null &"
    if sh(f"ssh -n -o BatchMode=yes {HOST} {q('nohup sh -c ' + q(start))}").returncode:
        raise SystemExit("fundamentals: starting the run failed")
    print(f"fundamentals: started {HOST}:{box} (rows.log, out/driver.log)")
    if sh(f"{q(str(ROOT / 'tools' / 'wait_for.sh'))} --host {HOST} --deadline {a.deadline} --interval 60 --file {box}/done >/dev/null").returncode:
        print(f"fundamentals: no `done' after {a.deadline} s; the run may still be going in {HOST}:{box}", file=sys.stderr)
        return 124
    evdir.mkdir(parents=True, exist_ok=True)
    if sh(f"rsync -a {HOST}:{box}/out/ {q(str(evdir / 'out'))}/").returncode:
        raise SystemExit("fundamentals: fetching the outputs failed")
    a.out = str(evdir / "out")
    return judge(a)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    bars = argparse.ArgumentParser(add_help=False)
    bars.add_argument("--f1-slope-max", type=float, default=1.5)
    bars.add_argument("--f1-reopen-mb", type=float, default=128)
    bars.add_argument("--f1-reopen", choices=("hwm", "rss"), default="hwm",
                      help="the reopen's figure: its peak (VmHWM, default) or VmRSS after it")
    bars.add_argument("--f2-r-evidence", default=None)
    bars.add_argument("--f3-fsync-max", type=float, default=1.0)
    bars.add_argument("--f4-q-max-ms", type=float, default=None)
    bars.add_argument("--f4-h-ms", type=float, default=None)
    bars.add_argument("--f4-client-deadline-ms", type=float, default=10000)
    bars.add_argument("--f6-bar-s", type=float, default=10)
    bars.add_argument("--f7-reading", choices=("as-written", "scn077-on-dtn"), default="as-written")
    bars.add_argument("--f8-reserved-mb", type=float, default=256)
    bars.add_argument("--f8-in-use-mb", type=float, default=128)
    bars.add_argument("--f8-in-use", choices=("rss", "hwm"), default="rss")
    bars.add_argument("--f8-reopen-mb", type=float, default=256)
    bars.add_argument("--checklist", default=None, help="default planning/release-vVERSION.md at REV's VERSION")
    bars.add_argument("--row-cores", default="20-23")
    bars.add_argument("--f4-cores", default="16-19")
    bars.add_argument("--tree", "--image", dest="tree", default=None,
                      help="the image: an hbox tree whose build/ holds the four images (tools/hbox_native.sh's)")
    p = sub.add_parser("run", parents=[bars])
    p.add_argument("--revision", required=True)
    p.add_argument("--label", default=None)
    p.add_argument("--steps", default=None, help='rows.sh steps (default "heap f4 f5 f5n f8 f1 f6c f3 f2 f7 wait f4s")')
    p.add_argument("--f4-seconds", type=int, default=3600)
    p.add_argument("--f2-before", default=None)
    p.add_argument("--edge-ssh", default=None)
    p.add_argument("--deadline", type=int, default=4 * 3600)
    p.add_argument("--dry-run", action="store_true")
    # run ends in judge, which reads a.write (batch AZ: without it every run
    # died after fetching its outputs, before printing the verdict's end).
    p.add_argument("--write", action="store_true",
                   help="after fetching, write the records as judge --write does")
    p = sub.add_parser("judge", parents=[bars])
    p.add_argument("--out", required=True)
    p.add_argument("--revision", required=True)
    p.add_argument("--write", action="store_true")
    a = ap.parse_args(argv)
    if a.cmd == "run" and not a.tree:
        ap.error("run needs --tree")
    return {"run": run, "judge": judge}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
