#!/usr/bin/env python3
"""Per-book certify times of a fn2 tree after forge-certify.sh, as a markdown table.

    python3 fn2/tools/certify-times.py [TREE [LOG]]      (TREE defaults to the repository root of this script; LOG to build/certify-closure.log)

cert.pl wall = the `Built ... (Ns)` line of build/certify-closure.log (includes loading the book's dependencies);
certify-book / prove = the CERTIFY-BOOK summary in the book's .cert.out; CPU = user+sys of its .cert.time (TIME_CERT=1).
"""
import os, re, sys

root = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
log = re.sub(r"\x1b\[[0-9;]*m", "", open(sys.argv[2] if len(sys.argv) > 2 else f"{root}/build/certify-closure.log").read())
rows = []
for m in re.finditer(r"Built (\S+)\.cert \(([\d.]+)s\)", log):
    book, wall = os.path.relpath(m.group(1), f"{root}/fn2"), float(m.group(2))
    out = open(f"{root}/fn2/{book}.cert.out", errors="replace").read()
    t = re.findall(r"Form:\s+\(CERTIFY-BOOK[^\n]*\n(?:[^\n]*\n)?Time:\s+([\d.]+) seconds \(prove: ([\d.]+)", out)
    ct, pv = (float(t[-1][0]), float(t[-1][1])) if t else (float("nan"), float("nan"))
    cpu = float("nan")
    try:
        s = open(f"{root}/fn2/{book}.cert.time").read()
        u = re.search(r"user\s+(\d+)m([\d.]+)s", s); y = re.search(r"sys\s+(\d+)m([\d.]+)s", s)
        cpu = int(u.group(1)) * 60 + float(u.group(2)) + int(y.group(1)) * 60 + float(y.group(2))
    except (OSError, AttributeError):
        pass
    rows.append((book, wall, ct, pv, cpu))
rows.sort(key=lambda r: -r[1])
print("| book | cert.pl wall s | certify-book s | prove s | CPU s |\n|---|---|---|---|---|")
for b, w, c, p, u in rows:
    print(f"| {b} | {w:.1f} | {c:.1f} | {p:.1f} | {u:.1f} |")
print(f"\n{len(rows)} books; sum of cert.pl wall {sum(r[1] for r in rows):.1f} s; sum of CPU {sum(r[4] for r in rows):.1f} s")
