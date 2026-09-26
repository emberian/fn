#!/usr/bin/env python3
"""Tables from an ia-anatomy.lisp log (lane image-anatomy, 2026-09-26).

    ia_report.py LOG [--top N]

Prints markdown tables, MiB throughout: the core by space, by owner group,
the world by property, ACL2's code by source file, and object types; each
with the octets resident at every residency snapshot the log was joined with
(clean file pages + private pages).  A measurement only.
"""
from __future__ import annotations

import collections
import sys

MIB = 1024 * 1024


def load(path):
    snaps, rows = [], []
    for line in open(path, encoding="utf-8", errors="replace"):
        if line.startswith("IA-COLUMNS"):
            words = line.split()[6:]
            snaps = [w.split(":")[0].replace(".pages", "") for w in words[::2]]
        elif line.startswith("IA-ROW"):
            parts = line.rstrip("\n").split("\t")
            space = parts[0].split()[1]
            owner, typ = parts[1], parts[2]
            nums = [int(x) for x in parts[3:]]
            rows.append((space, owner, typ, nums))
    width = 2 + 2 * len(snaps)
    broken = [r for r in rows if len(r[3]) != width]
    if broken:
        print("(%d rows with a type name split over lines skipped: %d octets)"
              % (len(broken), sum(r[3][0] for r in broken if r[3])))
    return snaps, [r for r in rows if len(r[3]) == width]


def group(owner):
    if owner.startswith("world:"):
        return ":".join(owner.split(":")[:2])
    if owner.startswith("code:acl2-*1*"):
        return "code:acl2-*1*"
    if owner.startswith("code:acl2"):
        return "code:acl2"
    return owner


def table(title, snaps, agg, top, key_name):
    print("\n### %s\n" % title)
    head = "| %s | MiB | objects | " % key_name + " | ".join(
        "%s touched (clean+private)" % s for s in snaps) + " |"
    print(head)
    print("|" + " --- |" * (3 + len(snaps)))
    items = sorted(agg.items(), key=lambda kv: -kv[1][0])
    total = [0] * (2 + 2 * len(snaps))
    for k, v in items:
        total = [a + b for a, b in zip(total, v)]
    for k, v in items[:top] + [("TOTAL", total)]:
        cells = ["%.1f (%.1f+%.1f)" % ((v[2 + 2 * i] + v[3 + 2 * i]) / MIB, v[2 + 2 * i] / MIB,
                                       v[3 + 2 * i] / MIB) for i in range(len(snaps))]
        print("| %s | %.1f | %d | %s |" % (k, v[0] / MIB, v[1], " | ".join(cells)))


def main():
    path = sys.argv[1]
    top = int(sys.argv[sys.argv.index("--top") + 1]) if "--top" in sys.argv else 20
    snaps, rows = load(path)
    width = 2 + 2 * len(snaps)

    def agg(keyf, filt=lambda r: True):
        out = collections.defaultdict(lambda: [0] * width)
        for r in rows:
            if filt(r):
                k = keyf(r)
                out[k] = [a + b for a, b in zip(out[k], r[3])]
        return out

    table("By space", snaps, agg(lambda r: r[0]), top, "space")
    table("By owner group", snaps, agg(lambda r: group(r[1])), 40, "owner")
    table("World by property (all origins)", snaps,
          agg(lambda r: r[1].split(":", 2)[2], lambda r: r[1].startswith("world:")
              and r[1].count(":") >= 2), top, "property")
    table("fn books' world by property", snaps,
          agg(lambda r: r[1].split(":", 2)[2], lambda r: r[1].startswith("world:fn-books:")),
          top, "property")
    table("ACL2 system code by source file", snaps,
          agg(lambda r: r[1], lambda r: r[1].startswith("code:acl2")), top, "file")
    table("By object type", snaps, agg(lambda r: r[2]), top, "type")
    table("Unattributed ('other') by type", snaps,
          agg(lambda r: r[2], lambda r: r[1] == "other"), 12, "type")


if __name__ == "__main__":
    main()
