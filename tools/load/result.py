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
MIN_P99_SAMPLES = 200       # p99 of fewer samples is not reported

CMP = {"le": lambda v, t: v <= t, "lt": lambda v, t: v < t, "ge": lambda v, t: v >= t,
       "gt": lambda v, t: v > t, "eq": lambda v, t: v == t}
CMP_TEXT = {"le": "<=", "lt": "<", "ge": ">=", "gt": ">", "eq": "=="}


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
    """One verdict row per bar that names this cell: PASS, FAIL or NOT-MEASURED, with the reason."""
    head = cell_head(cr.get("cell", ""))
    load1 = ((cr.get("box") or {}).get("loadavg_start") or [None])[0]
    rows = []
    for b in bars:
        if b["cell"] != head:
            continue
        checks, failed, missing = [], False, []
        for c in b["checks"]:
            val = (cr.get("metrics") or {}).get(c["metric"])
            row = {"metric": c["metric"], "cmp": c["cmp"], "threshold": c["threshold"], "value": val}
            if val is None:
                row["reason"] = (cr.get("not_measured") or {}).get(c["metric"]) or (
                    "run %s" % cr.get("status", "incomplete") if cr.get("status") != "complete"
                    else "metric absent from the run")
                missing.append(row["reason"])
            elif b.get("latency") and load1 is not None and load1 > LOADED_ABOVE:
                row["reason"] = "box loaded (load %.1f > %.0f)" % (load1, LOADED_ABOVE)
                missing.append(row["reason"])
            else:
                row["ok"] = bool(CMP[c["cmp"]](val, c["threshold"]))
                failed = failed or not row["ok"]
            checks.append(row)
        verdict = "FAIL" if failed else ("NOT-MEASURED" if missing else "PASS")
        rows.append({"bar": b["id"], "quantity": b["quantity"], "verdict": verdict,
                     "reason": "; ".join(sorted(set(missing))) if verdict == "NOT-MEASURED" else None,
                     "checks": checks, "source": b["source"]})
    return rows


def overall(rows):
    if any(r["verdict"] == "FAIL" for r in rows):
        return "fail"
    if rows and all(r["verdict"] == "PASS" for r in rows):
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
            "refusals": cr.get("refusals", {}),
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


def read_result(path):
    res = json.loads(Path(path).read_text())
    if "cells" not in res:
        raise ValueError("%s is not a tools/load result (no cells)" % path)
    return res


def cmd_judge(args):
    res, bars = read_result(args.result), load_bars()
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
    a = p.parse_args(argv)
    return {"judge": cmd_judge, "report": cmd_report}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
