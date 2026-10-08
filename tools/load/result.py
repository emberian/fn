"""Results: latency statistics, the FN_LOAD_RESULT line, the judge, the report, the item filer.

Stdlib only and no image: everything here runs on the laptop against a fixed
result JSON (tests/test_load_harness.py).  A result file holds
    {"schema": 1, "label", "rev", "cells": [cell result, ...]}
and a cell result carries `metrics` (flat dotted names, numbers), `not_measured`
(metric name -> reason), `phases` and the conditions.  tools/load/bars.json rows
name a cell, a quantity and one or more `checks` {metric, cmp, threshold}.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BARS = HERE / "bars.json"
ITEMS = ROOT / "planning" / "repair" / "items"
LOADED_ABOVE = 8.0          # a latency bar is NOT-MEASURED when the box's 1-minute load exceeds this
TIME_LOAD_MAX = 4.0         # a time bar (T-*, ruling 17): busy cores' worth on the cell's own cores <= 4 at start AND end
MIN_P99_SAMPLES = 200       # p99 of fewer samples is not reported

CMP = {"le": lambda v, t: v <= t, "lt": lambda v, t: v < t, "ge": lambda v, t: v >= t,
       "gt": lambda v, t: v > t, "eq": lambda v, t: v == t}
CMP["report"] = lambda v, t: True
CMP_TEXT = {"report": "reported", "le": "<=", "lt": "<", "ge": ">=", "gt": ">", "eq": "=="}


def pct(values, q):
    """scale_curve.pct: nearest rank on the sorted values."""
    if not values:
        return None
    v = sorted(values)
    return v[min(len(v) - 1, int(round(q * (len(v) - 1))))]


def lat_stats(seconds):
    """p50/p95/p99/max in ms of a list of seconds; p99 is null under 200 samples."""
    ms = [s * 1000.0 for s in seconds]
    n = len(ms)
    r = lambda x: None if x is None else round(x, 3)
    return {"n": n, "p50_ms": r(pct(ms, 0.5)), "p95_ms": r(pct(ms, 0.95)) if n >= 20 else None,
            "p99_ms": r(pct(ms, 0.99)) if n >= MIN_P99_SAMPLES else None, "max_ms": r(max(ms)) if ms else None}


def fit_exponent(points):
    """Least-squares slope of log t on log size over (size, t) pairs: t ~ size^k."""
    pts = [(math.log(s), math.log(t)) for s, t in points if s > 0 and t and t > 0]
    if len(pts) < 2:
        return None
    mx = sum(x for x, _ in pts) / len(pts)
    my = sum(y for _, y in pts) / len(pts)
    den = sum((x - mx) ** 2 for x, _ in pts)
    return None if den == 0 else round(sum((x - mx) * (y - my) for x, y in pts) / den, 3)


def cell_head(cell_id):
    return cell_id.split("@")[0].split("/")[0]


def load_bars(path=BARS):
    with open(path) as f:
        data = json.load(f)
    for b in data["bars"]:
        for key in ("id", "quantity", "cell", "workload", "source", "checks"):
            if key not in b:
                raise ValueError("bar %s lacks %s" % (b.get("id"), key))
        for c in b["checks"]:
            if c["cmp"] not in CMP:
                raise ValueError("bar %s: bad cmp %r" % (b["id"], c["cmp"]))
    return data["bars"]


def judge_cell(cr, bars):
    """One verdict row per bar that names this cell: PASS, FAIL, REPORTED or NOT-MEASURED, with the reason.

    A check may name `fs` (zfs, tmpfs): it applies only to a cell on that filesystem.  A `latency` bar is
    NOT-MEASURED above load 8; a `time` bar (ruling 17) needs load <= 4 at start and end and pinned cores."""
    if cr.get("sub"):          # a member of a sweep: the merged cell is judged, not its members
        return []
    head = cell_head(cr.get("cell", ""))
    box = cr.get("box") or {}
    load1 = (box.get("loadavg_start") or [None])[0]
    load2 = (box.get("loadavg_end") or [None])[0]
    fs = (box.get("fs") or "").lower()
    rows = []
    for b in bars:
        if b["cell"] != head:
            continue
        checks, failed, missing = [], False, []
        applicable = 0
        for c in b["checks"]:
            if c.get("fs") and c["fs"] != fs:
                continue
            applicable += 1
            val = (cr.get("metrics") or {}).get(c["metric"])
            row = {"metric": c["metric"], "cmp": c["cmp"], "threshold": c["threshold"], "value": val}
            if val is None:
                row["reason"] = (cr.get("not_measured") or {}).get(c["metric"]) or (
                    "run %s" % cr.get("status", "incomplete") if cr.get("status") != "complete"
                    else "metric absent from the run")
                missing.append(row["reason"])
            elif c.get("time", b.get("time")) and (box.get("busy_cores_start") is None or box.get("busy_cores_end") is None):
                row["reason"] = "per-core busy on the cell's cores was not recorded (load %s)" % load1
                missing.append(row["reason"])
            elif c.get("time", b.get("time")) and (box["busy_cores_start"] > TIME_LOAD_MAX or box["busy_cores_end"] > TIME_LOAD_MAX):
                row["reason"] = "box loaded (%.1f busy cores at start, %.1f at end on cores %s; a time bar needs <= %g at both; loadavg %s)" % (
                    box["busy_cores_start"], box["busy_cores_end"], box.get("busy_cores_set") or "?", TIME_LOAD_MAX, load1)
                missing.append(row["reason"])
            elif c.get("time", b.get("time")) and not box.get("pinned"):
                row["reason"] = "cell not pinned to its own cores (--cores)"
                missing.append(row["reason"])
            elif b.get("latency") and load1 is not None and load1 > LOADED_ABOVE:
                row["reason"] = "box loaded (load %.1f > %.0f)" % (load1, LOADED_ABOVE)
                missing.append(row["reason"])
            else:
                row["ok"] = bool(CMP[c["cmp"]](val, c["threshold"]))
                failed = failed or not row["ok"]
            checks.append(row)
        if not applicable:
            missing.append("no check applies on filesystem %s" % (fs or "unknown"))
        all_report = bool(checks) and all(c["cmp"] == "report" for c in checks)
        verdict = "FAIL" if failed else ("NOT-MEASURED" if missing else ("REPORTED" if all_report else "PASS"))
        rows.append({"bar": b["id"], "quantity": b["quantity"], "verdict": verdict,
                     "reason": "; ".join(sorted(set(missing))) if verdict == "NOT-MEASURED" else None,
                     "checks": checks, "source": b["source"]})
    return rows


def overall(rows):
    if any(r["verdict"] == "FAIL" for r in rows):
        return "fail"
    if rows and all(r["verdict"] in ("PASS", "REPORTED") for r in rows):
        return "pass"
    return "no-bar" if not rows else "not-measured"


def result_line(cr, rows=None):
    """The FN_LOAD_RESULT line's object (LOAD-PROGRAM section 3)."""
    m = cr.get("metrics") or {}
    cmd, count = {}, {}
    for ph in cr.get("phases", []):
        for op in ph.get("cmd") or {}:
            count[op] = count.get(op, 0) + 1
    for ph in cr.get("phases", []):
        for op, st in (ph.get("cmd") or {}).items():
            cmd[op if count[op] == 1 else "%s/%s" % (op, ph["name"])] = st
    rate = {"%s/%s" % (k, ph["name"]): v for ph in cr.get("phases", []) for k, v in (ph.get("rate") or {}).items()}
    rows = rows if rows is not None else cr.get("bars", [])
    return {"cell": cr.get("cell"), "target": cr.get("target"), "arm": cr.get("arm"), "rep": cr.get("rep"),
            "image": (cr.get("image") or {}).get("path"), "core_sha256": (cr.get("image") or {}).get("core_sha256"),
            "box": (cr.get("box") or {}).get("name"), "git": cr.get("git"),
            "load_start": (cr.get("box") or {}).get("loadavg_start"),
            "load_end": (cr.get("box") or {}).get("loadavg_end"), "admitted": cr.get("admitted"), "seconds": cr.get("seconds"),
            "noisy": bool(cr.get("noisy")), "cmd": cmd, "rate": rate,
            "rss_kib": {"anon": m.get("rss_kib.anon"), "file": m.get("rss_kib.file"),
                        "vmrss": m.get("rss_kib.vmrss"), "hwm": m.get("rss_kib.hwm")},
            "gc_s": None if m.get("gc.ms") is None else round(m["gc.ms"] / 1000.0, 3),
            "refusals": cr.get("refusals", {}), "faults": cr.get("faults"),
            "bar": {r["bar"]: r["verdict"] for r in rows}, "verdict": overall(rows),
            "status": cr.get("status")}


def print_line(cr, rows=None, stream=None):
    return "FN_LOAD_RESULT " + json.dumps(result_line(cr, rows), sort_keys=True)


def _fmt(v):
    if v is None:
        return "-"
    if isinstance(v, float):
        return "%.1f" % v if abs(v) >= 100 else "%.3g" % v
    return str(v)


def verdict_table(rows):
    out = ["| bar | quantity | check | value | verdict |", "|---|---|---|---|---|"]
    for r in rows:
        for i, c in enumerate(r["checks"]):
            out.append("| %s | %s | %s %s %s | %s | %s |" % (
                r["bar"] if i == 0 else "", r["quantity"] if i == 0 else "", c["metric"],
                CMP_TEXT[c["cmp"]], _fmt(c["threshold"]), _fmt(c["value"]),
                (r["verdict"] + (" (%s)" % r["reason"] if r.get("reason") and i == 0 else "")) if i == 0 else ""))
    return out


def report(res, bars):
    """One page of markdown: the verdict table first, then per-phase figures, then the conditions."""
    out = ["# Load run %s" % res.get("label", "")]
    for cr in res["cells"]:
        rows = judge_cell(cr, bars)
        box = cr.get("box") or {}
        img = cr.get("image") or {}
        out += ["", "## %s  target=%s arm=%s rep=%s  status=%s%s" % (
            cr.get("cell"), cr.get("target"), cr.get("arm") or "-", cr.get("rep"), cr.get("status"),
            "  NOISY" if cr.get("noisy") else "")]
        out += [""] + (verdict_table(rows) if rows else ["No bar names this cell; the figures below are reported only."])
        out += ["", "| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |",
                "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
        for ph in cr.get("phases", []):
            if ph.get("status") == "not-implemented":
                out.append("| %s | - | NOT-MEASURED: %s |" % (ph["name"], ph.get("reason")))
                continue
            mem, io, gc = ph.get("mem") or {}, ph.get("io") or {}, ph.get("gc") or {}
            cmds = ph.get("cmd") or {}
            op = next(iter(cmds), None)
            st = cmds.get(op) or {}
            rate = next(iter((ph.get("rate") or {}).values()), None)
            out.append("| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
                ph["name"], _fmt(ph.get("seconds")), "%s %s" % (op, st.get("n")) if op else "-",
                _fmt(st.get("p50_ms")), _fmt(st.get("p99_ms")), _fmt(rate), _fmt(mem.get("vmrss")),
                _fmt(mem.get("anon")), _fmt(mem.get("file")), _fmt(mem.get("hwm")), _fmt(ph.get("cpu_s")),
                _fmt(io.get("read_bytes")), _fmt(io.get("write_bytes")), _fmt(gc.get("count")), _fmt(gc.get("ms"))))
        for ph in cr.get("phases", []):
            if ph.get("locks_error"):
                out += ["", "%s locks: NOT-MEASURED: %s" % (ph["name"], ph["locks_error"])]
            if "lock_metrics" not in ph:
                continue
            mt, window = ph["lock_metrics"], ph["lock_window"]
            names = sorted((k[len("locks."):-len(".wait_ms")] for k in mt if k.endswith(".wait_ms")),
                           key=lambda name: (-mt["locks." + name + ".wait_ms"], name))[:8]
            out += ["", "%s contended mutex waits (top 8 by wait; all owner threads, including poster). "
                    "Snapshot window %.6f–%.6f; phase %.6f–%.6f epoch seconds. "
                    "Each boundary uses the last dump at or before it (normally <1 s earlier); "
                    "counts are charged on wait completion, with no interpolation."
                    % (ph["name"], window["epoch_start"], window["epoch_end"], ph["epoch_start"], ph["epoch_end"]), "",
                    "| lock | waits | wait ms | wait ms / ARTICLE |", "|---|---|---|---|"]
            for name in names:
                prefix = "locks." + name
                out.append("| %s | %s | %s | %s |" % (
                    name.replace("|", "&#124;").replace("\n", " "), _fmt(mt[prefix + ".waits"]),
                    _fmt(mt[prefix + ".wait_ms"]), _fmt(mt[prefix + ".wait_ms_per_article"])))
            if not names:
                out.append("| (no contended grabs observed) | 0 | 0 | - |")
        if cr.get("members"):
            keys = [m.split("@", 1)[1] for m in cr["members"]]
            mt = cr.get("metrics") or {}
            base = sorted({k.rsplit("@", 1)[0] for k in mt if "@" in k and k.rsplit("@", 1)[1] in keys})
            out += ["", "Metrics by store size (octets/KiB/seconds as named; exponent = fitted slope of log value on log n):", "",
                    "| metric | " + " | ".join(keys) + " | exponent |", "|---|" + "---|" * (len(keys) + 1)]
            for b in base:
                if b.startswith(("posts.", "gc.", "anon.live", "anon.raw.type", "rss_kib.")):
                    continue
                out.append("| %s | %s | %s |" % (b, " | ".join(_fmt(mt.get("%s@%s" % (b, k))) for k in keys), _fmt(mt.get(b + ".exponent"))))
        if cr.get("refusals"):
            out += ["", "Refusals by name: " + ", ".join("%s x%d" % kv for kv in sorted(cr["refusals"].items()))]
        out += ["", "Conditions: box %s (%s cores), load %s at start and %s at end, ZFS ARC %s -> %s bytes, filesystem %s, "
                "preset %s, launch `%s`, image %s (core sha256 %s), tree %s, hook %s, driver rev %s."
                % (box.get("name"), box.get("cores"), box.get("loadavg_start"), box.get("loadavg_end"),
                   box.get("arc_bytes_start"), box.get("arc_bytes_end"), box.get("fs"), cr.get("preset"),
                   cr.get("launch"), img.get("path"), (img.get("core_sha256") or "-")[:16], img.get("tree_sha"),
                   cr.get("hook") or "none", cr.get("git"))]
        if cr.get("loopback_only", True):
            out.append("Every row is loopback on one box (client and node on the same host).")
    return "\n".join(out) + "\n"


def file_items(res, bars, items_dir=ITEMS, now=None):
    """One LOAD-<bar>-<rev12> item per FAIL, updated in place when it exists.  Returns the paths written."""
    meta = {b["id"]: b for b in bars}
    written = []
    stamp = now or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    for cr in res["cells"]:
        rev12 = str(cr.get("image", {}).get("tree_sha") or cr.get("git") or "unknown")[:12]
        for row in judge_cell(cr, bars):
            if row["verdict"] != "FAIL":
                continue
            b = meta[row["bar"]]
            item_id = "LOAD-%s-%s" % (row["bar"], rev12)
            figs = "; ".join("%s = %s (bar %s %s)" % (c["metric"], _fmt(c["value"]), CMP_TEXT[c["cmp"]], _fmt(c["threshold"]))
                             for c in row["checks"] if c.get("ok") is False)
            box = cr.get("box") or {}
            detail = ("%s: %s. Measured on %s, load %s, preset %s, filesystem %s, image %s (core sha256 %s), cell %s "
                      "target %s arm %s rep %s, run %s. Evidence: tools/load result JSON %s. The bar is %s (%s)."
                      % (row["bar"], figs, box.get("name"), box.get("loadavg_start"), cr.get("preset"), box.get("fs"),
                         (cr.get("image") or {}).get("path"), ((cr.get("image") or {}).get("core_sha256") or "-")[:16],
                         cr.get("cell"), cr.get("target"), cr.get("arm") or "-", cr.get("rep"), res.get("label"),
                         res.get("evidence") or "(not archived)", row["quantity"], row["source"]))
            path = Path(items_dir) / (item_id + ".json")
            if path.exists():
                item = json.loads(path.read_text())
                if item.get("detail") != detail:
                    note = "%s: re-run %s: %s" % (stamp, res.get("label"), figs)
                    if note not in item.get("notes", []):
                        item.setdefault("notes", []).append(note)
                    item["detail"] = detail
                    item["updated"] = stamp
            else:
                item = {"category": "bug", "detail": detail, "file": b.get("file", "tools/load/bars.json"), "id": item_id,
                        "line": "", "notes": [], "owner": b.get("owner", "deputy-L"), "severity": b.get("severity", "medium"),
                        "source": "tools/load", "state": "open",
                        "title": "%s: %s" % (row["bar"], figs), "updated": stamp}
            Path(items_dir).mkdir(parents=True, exist_ok=True)
            tmp = path.with_suffix(".json.tmp")
            tmp.write_text(json.dumps(item, indent=1, sort_keys=True) + "\n")
            os.replace(tmp, path)
            written.append(str(path))
    return written


ANON_TYPES = [("CONS", "anon.raw.type.room:CONS"), ("strings", "anon.raw.type.room:SIMPLE-CHARACTER-STRING"),
              ("u64 arrays", "anon.raw.type.room:SIMPLE-ARRAY-UNSIGNED-BYTE-64"), ("u8 arrays", "anon.raw.type.room:SIMPLE-ARRAY-UNSIGNED-BYTE-8")]
STOBJS = ("anon.raw.CAT", "anon.raw.ARENA", "anon.raw.HIST")


def anon_table(cr, keys=None):
    """Per-type anonymous-heap table of a W15 sweep cell (MEM-013): SBCL `room` octets per type, the named stobjs
    (CAT + ARENA + HIST, walked by slot), and the rest of dynamic space, at each store size; with the fitted exponent of
    the value against n and the growth over the 1k store in octets per article.  Dynamic space includes the core's own
    objects, so the growth column is the one to read."""
    mt = cr.get("metrics") or {}
    members = cr.get("members") or []
    allkeys = [m.split("@", 1)[1] for m in members]
    sizes = {"1k": 1000, "10k": 10000, "25k": 25000, "50k": 50000, "100k": 100000}
    keys = keys or [k for k in allkeys if k in ("25k", "50k", "100k")]
    rows = []

    def val(name, k):
        return mt.get("%s@%s" % (name, k))
    cols = ["1k"] + [k for k in keys if k != "1k"]
    lines = {}
    for label, name in ANON_TYPES:
        lines[label] = {k: val(name, k) for k in allkeys}
    lines["stobjs (CAT+ARENA+HIST; inside the type rows, not additive)"] = {k: (None if any(val(n, k) is None for n in STOBJS) else sum(val(n, k) for n in STOBJS)) for k in allkeys}
    dyn = {k: val("anon.raw.dynamic_usage", k) for k in allkeys}
    lines["others (dynamic space minus the four type rows)"] = {
        k: (None if dyn[k] is None else dyn[k] - sum((lines[l][k] or 0) for l, _ in ANON_TYPES)) for k in allkeys}
    lines["dynamic space total"] = dyn
    out = ["| type | " + " | ".join(cols) + " | exponent (value vs n) | growth over 1k, B per article at " + (keys[-1] if keys else "-") + " |",
           "|---|" + "---|" * (len(cols) + 2)]
    for label, byk in lines.items():
        pts = [(sizes[k], byk[k]) for k in allkeys if byk.get(k)]
        e = fit_exponent(pts) if len(pts) >= 3 else None
        last = keys[-1] if keys else None
        g = None
        if last and byk.get(last) is not None and byk.get("1k") is not None:
            g = (byk[last] - byk["1k"]) / (sizes[last] - 1000)
        out.append("| %s | %s | %s | %s |" % (label, " | ".join(_fmt(byk.get(k)) for k in cols), _fmt(e), _fmt(g)))
    return "\n".join(out) + "\n"


def cmd_anon(args):
    res = read_result(args.result)
    parts = []
    for cr in res["cells"]:
        if cr.get("members") and any("anon.raw.dynamic_usage@" in k for k in cr.get("metrics", {})):
            parts.append("## Anonymous heap by type: %s on %s (%s)\n\n%s" % (cr["cell"], cr.get("target"), (cr.get("image") or {}).get("path"), anon_table(cr)))
    text = "\n".join(parts) or "no sweep cell with a census\n"
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)
    return 0


def read_result(path):
    res = json.loads(Path(path).read_text())
    if "cells" not in res:
        raise ValueError("%s is not a tools/load result (no cells)" % path)
    return res


def cmd_judge(args):
    res, bars = read_result(args.result), load_bars()
    if not res.get("evidence"):
        try:
            res["evidence"] = str(Path(args.result).resolve().relative_to(ROOT))
        except ValueError:
            res["evidence"] = str(args.result)
    worst = 0
    for cr in res["cells"]:
        rows = judge_cell(cr, bars)
        print("== %s target=%s arm=%s rep=%s" % (cr.get("cell"), cr.get("target"), cr.get("arm") or "-", cr.get("rep")))
        print("\n".join(verdict_table(rows)) if rows else "(no bar names this cell)")
        worst = max(worst, 1 if any(r["verdict"] == "FAIL" for r in rows) else 0)
    if args.file_items:
        for p in file_items(res, bars):
            print("item", p)
    return worst


def cmd_report(args):
    res = read_result(args.result)
    text = report(res, load_bars())
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)
    return 0


def main(argv=None):
    p = argparse.ArgumentParser(prog="tools.load.result")
    sub = p.add_subparsers(dest="cmd", required=True)
    j = sub.add_parser("judge")
    j.add_argument("result")
    j.add_argument("--file-items", action="store_true")
    r = sub.add_parser("report")
    r.add_argument("result")
    r.add_argument("--out")
    an = sub.add_parser("anon")
    an.add_argument("result")
    an.add_argument("--out")
    a = p.parse_args(argv)
    return {"judge": cmd_judge, "report": cmd_report, "anon": cmd_anon}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
