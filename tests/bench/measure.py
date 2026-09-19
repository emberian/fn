#!/usr/bin/env python3
"""Measure one generated store: reopen, reader latency, RSS, bridge bytes.

Every figure comes from the real path.  Reopen is `open_live_store`, which
reads the committed files, unframes each through `fn-frame-store-decode` and
replays them with `fn-store-sn-recover`.  Reader latency is `tools/run_reader`'s
`Reader` sharing the same ACL2 process, so a command is served by the node this
store recovered, not by the reader host's seed archive.

`OVER` is not in `books/nntp`'s command set (GROUP, LISTGROUP, LAST, NEXT,
ARTICLE, HEAD, BODY, STAT), so the OVER-equivalent measured here is the
enumeration a client would have to do instead: LISTGROUP followed by HEAD per
article number.  That substitution is the measurement, not a claim that OVER
exists.

Usage (from the repository root):
  python3 tests/bench/measure.py --root DIR --runs 5 --json OUT.json
"""
import argparse
import json
import os
from pathlib import Path
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))
# `tools/run_reader.py` imports its sibling as `run_store`; `tools.frame_bridge`
# keeps one framing session across both spellings, so the reader and the store
# still share a single ACL2 process.
sys.path.insert(1, str(ROOT / "tools"))
from tools import frame_bridge  # noqa: E402
from tools.run_reader import Acl2Reader  # noqa: E402
from tools.run_store import open_live_store  # noqa: E402
from tests.bench.generate import CallMeter, message_id, rss_kib  # noqa: E402

ENUMERATION_SAMPLE = 32


def summarize(values):
    return {"runs": len(values), "min": min(values), "median": statistics.median(values),
            "max": max(values)}


def timed_command(reader, text):
    before = time.monotonic()
    reply, closing, _ = reader.chunk(text.encode("ascii"))
    return time.monotonic() - before, reply, closing


def measure_once(root, seed, articles, group):
    """One reopen plus one pass of reader commands over the recovered node."""
    out = {}
    before = time.monotonic()
    store, bridge, records = open_live_store(Path(root), writable=False)
    out["reopen_seconds"] = time.monotonic() - before
    meter = CallMeter(bridge)
    frame_bridge.adopt(bridge)
    reader = None
    try:
        out["records"] = len(records)
        out["article_count"] = bridge.article_count()
        out["rss_kib_after_recovery"] = rss_kib(bridge.proc.pid)
        before = time.monotonic()
        reader = Acl2Reader(store_bridge=bridge)
        out["reader_attach_seconds"] = time.monotonic() - before
        reader.reset()
        out["group_seconds"], reply, _ = timed_command(reader, "GROUP %s\r\n" % group)
        out["group_reply"] = reply[:64].decode("ascii", "replace").strip()
        out["listgroup_seconds"], reply, _ = timed_command(
            reader, "LISTGROUP %s\r\n" % group)
        out["listgroup_reply_bytes"] = len(reply)
        # Article retrieval by number at three positions.  `fn-find-article`
        # walks a list whose head is the newest article, so position is the
        # variable that matters, not just N.
        positions = sorted({1, max(1, articles // 2), articles})
        by_number = {}
        for number in positions:
            seconds, reply, _ = timed_command(reader, "ARTICLE %d\r\n" % number)
            by_number[number] = {"seconds": seconds, "reply_bytes": len(reply),
                                 "code": reply[:3].decode("ascii", "replace")}
        out["article_by_number"] = by_number
        seconds, reply, _ = timed_command(
            reader, "ARTICLE %s\r\n" % message_id(seed, 0).decode("ascii"))
        out["article_by_message_id"] = {"seconds": seconds, "reply_bytes": len(reply),
                                        "code": reply[:3].decode("ascii", "replace")}
        # OVER-equivalent: HEAD over a bounded consecutive range.
        sample = min(ENUMERATION_SAMPLE, articles)
        before, enum_bytes = time.monotonic(), 0
        for number in range(1, sample + 1):
            _, reply, _ = timed_command(reader, "HEAD %d\r\n" % number)
            enum_bytes += len(reply)
        elapsed = time.monotonic() - before
        out["over_equivalent"] = {"heads": sample, "seconds": elapsed,
                                  "seconds_per_article": elapsed / sample,
                                  "reply_bytes": enum_bytes}
        out["rss_kib_after_reading"] = rss_kib(bridge.proc.pid)
        out["bridge_calls"] = meter.calls
        out["bridge_form_bytes"] = meter.form_bytes
    finally:
        if reader is not None and reader.owns_process:
            reader.close()
        bridge.close()
        store.close()
        frame_bridge.close()
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--articles", type=int, required=True)
    parser.add_argument("--group", default="fn.letters")
    parser.add_argument("--json", default=None)
    args = parser.parse_args()
    runs = []
    for index in range(args.runs):
        run = measure_once(args.root, args.seed, args.articles, args.group)
        run["run"] = index
        run["loadavg"] = os.getloadavg()
        runs.append(run)
    result = {"root": args.root, "articles": args.articles, "group": args.group,
              "runs": runs,
              "reopen_seconds": summarize([r["reopen_seconds"] for r in runs]),
              "group_seconds": summarize([r["group_seconds"] for r in runs]),
              "listgroup_seconds": summarize([r["listgroup_seconds"] for r in runs]),
              "over_equivalent_seconds_per_article": summarize(
                  [r["over_equivalent"]["seconds_per_article"] for r in runs]),
              "article_by_message_id_seconds": summarize(
                  [r["article_by_message_id"]["seconds"] for r in runs])}
    for position in runs[0]["article_by_number"]:
        result.setdefault("article_by_number_seconds", {})[str(position)] = summarize(
            [r["article_by_number"][position]["seconds"] for r in runs])
    text = json.dumps(result, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
