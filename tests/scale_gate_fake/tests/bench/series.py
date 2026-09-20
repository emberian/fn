#!/usr/bin/env python3
"""Fake host: the shape of tests/bench/series.py without ACL2, for the gate's test.

It walks the same doubling series, applies the same two ceilings, writes the
same `SCALE-SERIES` line, and leaves behind the JSON store
`tests/deploy_gate_fake/tools/run_reader.py` can serve -- so
tools/scale_gate.py's parsing, stopping, table rendering and reader phase are
driven end to end with no ACL2 and no ssh.

Every number here is arithmetic in this file. Nothing it prints is evidence
about fn, and the curve is chosen only to cross a ceiling inside a test.

`FN_FAKE_SERIES_DIE=N` makes the point at N articles die mid-post the way a
real one does (`StoreError: ACL2 prompt timeout`), so the test can require
that the partial curve survives -- the open item the w3 handoff left.
"""
import argparse
import base64
import json
import os
from pathlib import Path
import sys

GROUPS = ["fn.letters", "fn.test"]


def article(index):
    body = ("Message-ID: <bench-1-%d@example.invalid>\r\n"
            "Newsgroups: %s\r\n"
            "From: bench <bench@example.invalid>\r\n"
            "Subject: bench %d\r\n\r\nfake body %d\r\n"
            % (index, ",".join(GROUPS), index, index))
    return {"msgid": "<bench-1-%d@example.invalid>" % index, "groups": list(GROUPS),
            "payload": base64.b64encode(body.encode()).decode()}


def save(root, count):
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    (root / "store.json").write_text(json.dumps(
        {"groups": list(GROUPS), "uncertain": [],
         "articles": [article(i) for i in range(count)]}))


def post_seconds(index, payload):
    return 0.02 + 0.0004 * index + payload / 1024.0 * 0.001


def recover_seconds(count, payload):
    return 0.2 + 0.9 * count * (1.0 + payload / 65536.0)


def summarize(values):
    ordered = sorted(values)
    return {"runs": len(ordered), "min": ordered[0],
            "median": ordered[len(ordered) // 2],
            "p90": ordered[min(len(ordered) - 1, int(0.9 * len(ordered)))],
            "max": ordered[-1], "total": sum(ordered)}


def checkpoints(start, top):
    out, size = [], start
    while size < top:
        out.append(size)
        size *= 2
    out.append(top)
    return out


def profile(root, args):
    out = {"root": root, "bridge_start_seconds": 4.2, "reopen_seconds": 31.5,
           "records": 32, "article_count": 32, "rss_kib": {"VmRSS": 1048576},
           "by_entry_point": {
               "fn-store-sn-recover": {"calls": 1, "seconds": 28.9,
                                       "form_bytes": 2400000},
               "fn-store-record-sequence": {"calls": 32, "seconds": 1.9,
                                            "form_bytes": 76000}}}
    text = json.dumps(out, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + "\n")
    print("SCALE-PROFILE " + text)
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--payload", type=int, default=1024)
    ap.add_argument("--start", type=int, default=16)
    ap.add_argument("--max", type=int, default=4096)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--post-ceiling", type=float, default=20.0)
    ap.add_argument("--recover-ceiling", type=float, default=60.0)
    ap.add_argument("--budget-seconds", type=float, default=3600.0)
    ap.add_argument("--profile-only", action="store_true")
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    if args.profile_only:
        return profile(args.root, args)

    die_at = int(os.environ.get("FN_FAKE_SERIES_DIE", "0"))
    result = {"payload_bytes": args.payload, "profile": "fn-store-profile-scale-1",
              "groups": GROUPS, "seed": args.seed, "start": args.start,
              "max_articles": args.max, "bound": 4096,
              "post_ceiling_seconds": args.post_ceiling,
              "recover_ceiling_seconds": args.recover_ceiling,
              "points": [], "stopped_by": None, "committed": 0, "status": "measured",
              "root": args.root, "elapsed_seconds": 12.5}
    committed, code = 0, 0
    for target in checkpoints(args.start, args.max):
        point = {"articles": target, "records_at_open": committed,
                 "reopen_writable_seconds": recover_seconds(committed, args.payload)}
        stop = target if (die_at and target == die_at) else target
        reach = (committed + (die_at - committed) // 2) if (die_at and target == die_at) \
            else stop
        posts = [post_seconds(i, args.payload) for i in range(committed, reach)]
        committed = reach
        result["committed"] = committed
        save(args.root, committed)
        point["posted"] = len(posts)
        point["post_seconds"] = summarize(posts) if posts else None
        point["post_form_bytes"] = summarize(
            [float(args.payload * 4) for _ in posts]) if posts else None
        worst = max(posts) if posts else 0.0
        point["calls"] = 6 * len(posts)
        point["form_bytes"] = int(args.payload * 4.2 * len(posts))
        point["worst_call"] = {"seconds": worst, "budget_seconds": 20.0 + 0.004 * 4,
                               "form_head": "(fn-store-sn-prepare",
                               "form_bytes": args.payload * 4,
                               "headroom_seconds": 20.016 - worst,
                               "fraction_of_deadline": worst / 20.016}
        if die_at and target == die_at:
            point["error"] = "StoreError: ACL2 prompt timeout"
            result["stopped_by"] = point["error"]
            result["points"].append(point)
            code = 3
            break
        point["recover_seconds"] = recover_seconds(committed, args.payload)
        point["records"] = committed
        point["article_count"] = committed
        point["rss_kib"] = {"VmRSS": 65536 + 512 * committed,
                            "VmHWM": 65536 + 600 * committed}
        result["points"].append(point)
        if worst > args.post_ceiling:
            result["stopped_by"] = ("a single post took %.1f s, over the %.0f s ceiling"
                                    % (worst, args.post_ceiling))
            break
        if point["recover_seconds"] > args.recover_ceiling:
            result["stopped_by"] = ("recover took %.1f s, over the %.0f s ceiling"
                                    % (point["recover_seconds"], args.recover_ceiling))
            break
    passing = [p["articles"] for p in result["points"]
               if p.get("posted") and not p.get("error")
               and (p.get("post_seconds") or {}).get("max", 0) <= args.post_ceiling
               and p.get("recover_seconds", 0) <= args.recover_ceiling]
    result["largest_passing"] = max(passing, default=0)
    result["largest_measured"] = max(
        [p["articles"] for p in result["points"] if p.get("posted")], default=0)
    text = json.dumps(result, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + "\n")
    print("SCALE-SERIES " + text)
    return code


if __name__ == "__main__":
    sys.exit(main())
