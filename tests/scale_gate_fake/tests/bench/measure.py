#!/usr/bin/env python3
"""Fake host: tests/bench/measure.py's summary shape, for the gate's test.

The comparison table reads `reopen_seconds`, `group_seconds` and
`over_equivalent_seconds_per_article` out of this JSON. The values are
arithmetic in this file -- deliberately near the cited pre-realignment
numbers, so the test can require that a ratio is computed and printed.
"""
import argparse
import json
from pathlib import Path
import sys


def summarize(value):
    return {"runs": 3, "min": value * 0.95, "median": value, "max": value * 1.1}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--articles", type=int, required=True)
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--group", default="fn.letters")
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    count = args.articles
    result = {
        "root": args.root, "articles": count, "group": args.group,
        "reopen_seconds": summarize(0.3 + 0.004 * count),
        "group_seconds": summarize(0.0002 + 0.000002 * count),
        "listgroup_seconds": summarize(0.0004 + 0.000004 * count),
        "over_equivalent_seconds_per_article": summarize(0.0006),
        "article_by_message_id_seconds": summarize(0.0008),
        "article_by_number_seconds": {"1": summarize(0.0007)},
    }
    text = json.dumps(result, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
