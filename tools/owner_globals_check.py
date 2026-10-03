#!/usr/bin/env python3
"""tools/owner_globals_check.py -- the owner's ACL2 state globals only shrink.

The host keeps ONE canonical owner value, the configured owner in the state
global `fn-owner' (host/owner-host.lisp fn-owner-ocfg / fn-owner-install-ocfg;
books/owner-host-relation.lisp names the relation it carries).  Everything
else the host keeps in a `fn-owner-*' state global is a side channel between
the ACL2 wrappers and the native host (a reply, a log line, a take's carries,
the exposure table, a transit decision) that the adapter-retirement record
(planning/evidence/adapter-retirement-2026-09-26.md) wants folded into the
owner value or a wrapper's own result.  Row Q3c's fifth metric counted
`defvar *fn-owner-' in host/owner-host.lisp, which is 0 on every revision
(the owner globals are `f-put-global' names, not defvars): this is the real
count.

WHAT IT COUNTS.  Per file under host/, the distinct `fn-owner-*' names that
a global accessor reads or writes: a token ending in `-global'
(f-put-global, f-get-global, boundp-global, makunbound-global, the natives'
fnn-owner-list-global / fnn-owner-octets-global / fnn-global, ...) followed
by the quoted name.  A quoted `fn-owner-*' that is a FUNCTION name (the
natives' `(fnn-owner-core 'fn-owner-open-peer ...)') is not a global and is
not counted.  Source-level, no ACL2; comments and strings are skipped.

THE BASELINE, tools/owner_globals_baseline.json, holds the count per file
today.  It only shrinks: a file over its count, or a file not in the baseline
with a global, fails; a file UNDER its count also fails until the baseline is
lowered (`--write-baseline', which refuses to raise any count).  Retire a
global (into the owner value or a wrapper's result) and lower the count.

    python3 tools/owner_globals_check.py                  # the lint (make check)
    python3 tools/owner_globals_check.py --list           # every name per file
    python3 tools/owner_globals_check.py --write-baseline # after a global is retired
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "tools" / "owner_globals_baseline.json"
HOST_DIRS = ("host",)
ACCESSOR = re.compile(r"(?:^|[\s(])[A-Za-z0-9*+/<>=!?.-]*-global\s+'(fn-owner-[a-z0-9*+/<>=!?.-]*)",
                      re.IGNORECASE)


def strip_comments_and_strings(text):
    """The source with `;' comments, `#|...|#' blocks and string contents blanked."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("#|", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("#|", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("|#", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""')
            i = j + 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def globals_of(text):
    """The distinct `fn-owner-*' names a global accessor names in TEXT."""
    return sorted({m.group(1).lower() for m in ACCESSOR.finditer(strip_comments_and_strings(text))})


def parked(root=ROOT):
    """Host files no build loads, parked with their owner (planning/host-
    parked.json, tools/host_loaded_check.py KNOWN).  Their globals are not
    the running owner's; when one is wired into a build its KNOWN entry must
    go (host_loaded_check is red until it does), and it is counted here."""
    import json
    path = root / "planning" / "host-parked.json"
    if not path.exists():
        return set()
    return set(json.loads(path.read_text(encoding="utf-8")).get("parked", {}))


def scan(root=ROOT):
    found = {}
    skip = parked(root)
    for d in HOST_DIRS:
        for path in sorted((root / d).rglob("*.lisp")):
            if str(path.relative_to(root)).replace("\\", "/") in skip:
                continue
            names = globals_of(path.read_text(encoding="utf-8", errors="replace"))
            if names:
                found[str(path.relative_to(root)).replace("\\", "/")] = names
    return found


def judge(found, baseline):
    """The lint's findings: (file, count, baseline count, verdict) for every deviation."""
    findings = []
    for path, names in found.items():
        have = len(names)
        if path not in baseline:
            findings.append((path, have, None, "not in the baseline"))
        elif have > baseline[path]:
            findings.append((path, have, baseline[path], "over the baseline"))
        elif have < baseline[path]:
            findings.append((path, have, baseline[path], "under the baseline: lower it (--write-baseline)"))
    for path, count in baseline.items():
        if path not in found and count > 0:
            findings.append((path, 0, count, "under the baseline: lower it (--write-baseline)"))
    return findings


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--list", action="store_true", help="print every name per file")
    parser.add_argument("--write-baseline", action="store_true",
                        help="write the counts as the baseline (refuses to raise any)")
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--baseline", type=Path, default=None)
    args = parser.parse_args(argv)
    baseline_path = args.baseline or (args.root / "tools" / "owner_globals_baseline.json")
    found = scan(args.root)
    if args.list:
        for path, names in found.items():
            print("{} ({})".format(path, len(names)))
            for name in names:
                print("  " + name)
        return 0
    baseline = json.loads(baseline_path.read_text(encoding="utf-8")) if baseline_path.exists() else {}
    if args.write_baseline:
        raised = [(p, len(n), baseline[p]) for p, n in found.items() if p in baseline and len(n) > baseline[p]]
        if raised:
            for p, have, had in raised:
                print("owner_globals_check: refusing to raise {} from {} to {}".format(p, had, have))
            return 1
        counts = {p: len(n) for p, n in found.items()}
        baseline_path.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print("owner_globals_check: baseline written, {} file(s), {} global(s)".format(
            len(counts), sum(counts.values())))
        return 0
    findings = judge(found, baseline)
    total = sum(len(n) for n in found.values())
    if findings:
        for path, have, had, why in findings:
            print("owner_globals_check: {}: {} owner global(s), baseline {}: {}".format(path, have, had, why))
        return 1
    print("owner_globals_check: {} owner state global(s) across {} file(s), at the baseline".format(
        total, len(found)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
