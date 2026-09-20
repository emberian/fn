#!/usr/bin/env python3
"""Fake host: tests/bench/generate.py's surface without ACL2, for the gate's test.

It writes the JSON store the fake reader serves and prints the summary line
the real one prints. Nothing here measures anything.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from series import GROUPS, article, save        # the fake series' article shape


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--articles", type=int, required=True)
    ap.add_argument("--groups", type=int, default=2)
    ap.add_argument("--fanout", type=int, default=0)
    ap.add_argument("--payload", type=int, default=1024)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--profile", default="dev")
    ap.add_argument("--payload-kind", default="random")
    ap.add_argument("--message-id-octets", type=int, default=0)
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    save(args.root, args.articles)
    result = {"articles": args.articles, "groups": args.groups,
              "group_names": GROUPS, "payload_bytes": args.payload,
              "profile": args.profile, "status": "passed", "root": args.root,
              "committed": args.articles, "commit_seconds": 0.01 * args.articles,
              "first_msgid": article(0)["msgid"]}
    text = json.dumps(result, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
