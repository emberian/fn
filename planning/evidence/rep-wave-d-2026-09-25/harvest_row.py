#!/usr/bin/env python3
"""harvest_row.py RESULT.json LABEL -> one table row for rep-wave-d-2026-09-25.md section 1.1"""
import json, sys
d = json.load(open(sys.argv[1]))
label = sys.argv[2]

def ms(k):
    v = d.get(k)
    return "%.2f ms" % v["median_ms"] if v else "-"

def mb(x):
    return "%.0f MB" % (x / 1e6) if x else "-"

def mib(k):
    return "%.0f" % (k / 1024.0) if k else "-"

rl = d.get("residency_after_load", {})
rc = d.get("residency_after_checkpoint_open", {})
live_load = rl.get("heap", {}).get("dynamic_usage_after_gc")
live_ckpt = rc.get("heap", {}).get("dynamic_usage_after_gc")
ap = d.get("alloc_post", {}).get("bytes_consed_per_op")
aa = d.get("alloc_article", {}).get("bytes_consed_per_op")
row = "| %s | %s | %s / %s | %s | %s | %s | %s | %s / %s MiB | %s | %s | %s | %s / %s | %s (%s / %s MiB) |" % (
    label, ms("greeting"),
    ms("post_first_quarter").replace(" ms", ""), ms("post_last_quarter"),
    ms("stat_present"), ms("article_present"), ms("over_present"),
    mb(live_load), mib(rl.get("rss_kib")), mib(rl.get("hwm_kib")),
    ("%.1f MB" % (ap / 1e6)) if ap else "-", ("%.2f MB" % (aa / 1e6)) if aa else "-",
    ("%.1f s" % d["reopen_seconds"]) if "reopen_seconds" in d else "-",
    ("%.1f" % d["checkpoint_seconds"]) if "checkpoint_seconds" in d else "-",
    ("%.1f s" % d["reopen_from_checkpoint_seconds"]) if "reopen_from_checkpoint_seconds" in d else "-",
    mb(live_ckpt), mib(rc.get("rss_kib")), mib(rc.get("hwm_kib")))
print(row)
c = d.get("contention")
if c:
    print("contention: window %.1f s, %d served to readers, POST %.1f ms (p95 %.1f), ARTICLE %.1f ms (p95 %.1f), errors %s" % (
        c["window_seconds"], c["reader_articles"], c["post"]["median_ms"], c["post"]["p95_ms"],
        c["article"]["median_ms"], c["article"]["p95_ms"], c["reader_errors"]))
print("load %.0f s; first quarter RSS %s" % (d.get("load_seconds", 0), d.get("rss_quarters_kib")))
if "checkpoint_rc" in d:
    print("checkpoint rc", d["checkpoint_rc"], d.get("checkpoint_out", "")[-200:].strip())
