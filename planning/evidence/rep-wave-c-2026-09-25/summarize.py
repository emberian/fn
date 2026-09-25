#!/usr/bin/env python3
"""Summarise the round JSONs load_prof.py wrote: one row per (label, round,
payload, N) with the load wall, the POST medians (first quarter, last
quarter, all), RSS after the load and its slope; then the call counts per
POST from the count runs, base beside after.

    summarize.py DIR
"""
import glob, json, os, re, sys

d = sys.argv[1]
rows = []
counts = {}
for p in sorted(glob.glob(os.path.join(d, "*-r[0-9]-*.json"))):
    m = re.match(r"(base|after)-r(\d)-(count|sprof)?-?p(\d+)-n(\d+)\.json", os.path.basename(p))
    if not m:
        continue
    j = json.load(open(p))
    label, rnd, kind, P, N = m.group(1), int(m.group(2)), m.group(3) or "load", int(m.group(4)), int(m.group(5))
    if j.get("error"):
        print("ERROR", p, j["error"][:200])
    if kind == "count":
        counts[(label, rnd)] = j.get("counts_per_post", {})
    fq, lq, al = j.get("post_first_quarter", {}), j.get("post_last_quarter", {}), j.get("post_all", {})
    rows.append((P, N, kind, label, rnd, j.get("load_seconds"), fq.get("median_ms"), lq.get("median_ms"),
                 al.get("median_ms"), j.get("rss_after_load_kib"), j.get("rss_slope_kib_per_article"),
                 j.get("stats_seconds")))
rows.sort()
print("| payload | N | run | image | round | load s | POST first-quarter median ms | last-quarter | all | RSS after load MiB | slope KiB/article |")
print("| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
for P, N, kind, label, rnd, load, fq, lq, al, rss, slope, ss in rows:
    f = lambda x, k=3: "-" if x is None else (f"{x:.{k}f}" if isinstance(x, float) else str(x))
    print(f"| {P} | {N} | {kind} | {label} | {rnd} | {f(load, 2)} | {f(fq)} | {f(lq)} | {f(al)} | {'-' if rss is None else f'{rss/1024:.1f}'} | {f(slope, 1)} |")
names = sorted({n for c in counts.values() for n in c})
if names:
    keys = sorted(counts)
    print()
    print("| calls per served POST | " + " | ".join(f"{l} r{r}" for l, r in keys) + " |")
    print("| --- | " + " | ".join("---:" for _ in keys) + " |")
    for n in names:
        print(f"| `{n}` | " + " | ".join(f"{counts[k].get(n, 0):g}" for k in keys) + " |")
