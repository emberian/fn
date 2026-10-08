#!/usr/bin/env python3
"""Where a native gate run's wall time went.

Reads one hbox_native run dir (run.log of `== step HH:MM:SSZ` lines, logs/,
tree/build/acl2/certify-*/*.active.json) or a glob of them, and prints one
JSON line per run, then a summary line (`{"summary": ...}`) when more than one.

Fields per run: total_s; steps (name -> wall seconds, from a step's start to
the next step's start; the parallel image-* steps use their own exit stamp);
image_s (first image-* start to stamp-images: wall, they run at once);
module_s (first test-* start to the last test-* exit); plumbing_share (wall
that is neither a static gate nor the module phase, over total); certify_pre_book_s
(certify start to the earliest book started_utc); top_books (3 by elapsed);
cache (the certify "From the cache" line).

Usage: gate_walls.py RUN_DIR_OR_GLOB...
"""
import glob
import json
import os
import re
import statistics
import sys
from datetime import datetime

STEP = re.compile(r"^== (\S+) (\d\d):(\d\d):(\d\d)Z")
EXIT = re.compile(r"^\s+(\S+) exit (\d+) (\d\d):(\d\d):(\d\d)Z")
STATIC = {"sbcl-check", "world-check", "interfaces-check", "host-books", "attach-order"}
DAY = 86400


def _secs(h, m, s):
    return int(h) * 3600 + int(m) * 60 + int(s)


def _is_image(n):
    return n.startswith("image-") and n != "image-libs"


def parse_run_log(path):
    """-> (starts, exits): starts = [(name, sec)] in order, exits = {name: sec}."""
    starts, exits = [], {}
    with open(path, errors="replace") as fh:
        for line in fh:
            m = STEP.match(line)
            if m:
                starts.append((m.group(1), _secs(*m.group(2, 3, 4))))
                continue
            m = EXIT.match(line)
            if m:
                exits[m.group(1)] = _secs(*m.group(3, 4, 5))
    return starts, exits


def _books(run_dir):
    out = []
    pat = os.path.join(run_dir, "tree", "build", "acl2", "certify-*", "*.active.json")
    for p in glob.glob(pat):
        try:
            with open(p) as fh:
                d = json.load(fh)
            ts = datetime.fromisoformat(d["started_utc"]).timestamp()
            out.append((d.get("book", os.path.basename(p)), float(d.get("elapsed_seconds") or 0), ts))
        except (OSError, ValueError, KeyError, TypeError):
            continue
    return out


def _cache_line(run_dir):
    p = os.path.join(run_dir, "logs", "certify.log")
    try:
        with open(p, errors="replace") as fh:
            for line in fh:
                if line.startswith("From the cache:"):
                    return line.strip()
    except OSError:
        pass
    return None


def _utc_day_start(run_dir):
    """Seconds-since-epoch of 00:00Z of the run's day, from run.log mtime."""
    t = os.path.getmtime(os.path.join(run_dir, "run.log"))
    return t - (t % DAY)


def analyze(run_dir):
    log = os.path.join(run_dir, "run.log")
    starts, exits = parse_run_log(log)
    if not starts:
        return None
    t0 = starts[0][1]
    rel = lambda t: (t - t0) % DAY
    names = [n for n, _ in starts]
    steps = {}
    plain = [(n, t) for n, t in starts if not n.startswith("test-")]
    for i, (n, t) in enumerate(plain):
        if _is_image(n) and n in exits:
            wall = (exits[n] - t) % DAY
        elif i + 1 < len(plain):
            wall = (plain[i + 1][1] - t) % DAY
        else:
            wall = 0
        steps[n] = steps.get(n, 0) + wall
    tests = [(n, t) for n, t in starts if n.startswith("test-")]
    end = rel(starts[-1][1])
    module_s = 0
    if tests:
        last = max([rel(exits[n]) for n, _ in tests if n in exits] + [rel(tests[-1][1])])
        module_s = last - rel(tests[0][1])
        end = max(end, last)
    elif len(plain) > 1:
        end = rel(plain[-1][1])
    image_s = None
    img = [t for n, t in starts if _is_image(n)]
    if img and "stamp-images" in names:
        image_s = (dict(starts)["stamp-images"] - img[0]) % DAY
    static = sum(v for k, v in steps.items() if k in STATIC)
    plumbing = max(0, end - module_s - static)
    # certify's pre-book seconds: certify start to the earliest book start.
    pre = None
    books = _books(run_dir)
    cstart = next((t for n, t in starts if n == "certify"), None)
    if books and cstart is not None:
        day = _utc_day_start(run_dir)
        base = day + cstart
        first = min(b[2] for b in books)
        # run.log is time-of-day only; a run crossing midnight puts base a day off.
        while first - base < -3600:
            base -= DAY
        while first - base > DAY / 2:
            base += DAY
        pre = round(first - base, 1)
    top = sorted(books, key=lambda b: -b[1])[:3]
    return {
        "run": os.path.relpath(run_dir) if not os.path.isabs(run_dir) else run_dir,
        "total_s": end,
        "steps": steps,
        "image_s": image_s,
        "module_s": module_s,
        "plumbing_s": plumbing,
        "plumbing_share": round(plumbing / end, 3) if end else None,
        "certify_pre_book_s": pre,
        "top_books": [{"book": b, "elapsed_s": e} for b, e, _ in top],
        "cache": _cache_line(run_dir),
    }


def main(argv):
    dirs = []
    for a in argv:
        hits = sorted(glob.glob(a)) or [a]
        dirs += [d for d in hits if os.path.isfile(os.path.join(d, "run.log"))]
    rows = []
    for d in dirs:
        r = analyze(d)
        if r:
            rows.append(r)
            print(json.dumps(r, sort_keys=True))
    if len(rows) > 1:
        keys = sorted({k for r in rows for k in r["steps"]})
        med = {k: statistics.median(r["steps"][k] for r in rows if k in r["steps"]) for k in keys}
        print(json.dumps({"summary": {
            "runs": len(rows),
            "median_total_s": statistics.median(r["total_s"] for r in rows),
            "median_step_s": med,
            "median_plumbing_share": statistics.median(
                r["plumbing_share"] for r in rows if r["plumbing_share"] is not None),
        }}, sort_keys=True))
    return 0 if rows else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
