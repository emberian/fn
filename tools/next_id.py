#!/usr/bin/env python3
"""Print the next free identifier in each registry, so a lane claims a real one.

Two lanes picked the same identifier twice in two days.  Both times the board
CLAIM line caught it and the second lane renumbered, which is the process
working -- but computing the number by eye is the part that keeps going wrong.
Run this, claim what it prints on the board, then write the row.

A decision's sub-ids (D14-a, D14-b) do not consume a number; the base does.
"""
import collections
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent


def decisions():
    text = (ROOT / "planning" / "decisions.md").read_text(errors="replace")
    used = sorted({int(n) for n in re.findall(r"\bD(\d+)", text)})
    return used, (max(used) + 1 if used else 1)


def rows(path, key):
    doc = json.loads((ROOT / path).read_text())
    return doc[key] if isinstance(doc, dict) and key in doc else doc


def next_by_prefix(ids):
    seen = collections.defaultdict(list)
    for one in ids:
        prefix, _, tail = one.rpartition("-")
        if prefix and tail.isdigit():
            seen[prefix].append(int(tail))
    return {p: max(ns) + 1 for p, ns in sorted(seen.items())}


def main(argv=None):
    used, nxt = decisions()
    print(f"decisions.md          next free: D{nxt}   (used: "
          f"{', '.join('D%d' % n for n in used)})")
    for path, key in (("planning/proofs.json", "proofs"),
                      ("planning/requirements.json", "requirements")):
        for prefix, n in next_by_prefix(r["id"] for r in rows(path, key)).items():
            print(f"{path:<21} next free: {prefix}-{n:03d}")
    for prefix, n in next_by_prefix(
            s["id"] for s in rows("tests/scenarios/catalog.json", "scenarios")).items():
        print(f"{'catalog.json':<21} next free: {prefix}-{n:03d}")
    print("\nClaim it on planning/deputies/BOARD.md before you write the row:")
    print("  CLAIM <lane> -> everyone: identifier `<id>` is taken, for <one line>.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
