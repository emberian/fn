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

WHAT IT COUNTS.  Per file under host/ and books/, the distinct `fn-owner-*' names that
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
    python3 tools/owner_globals_check.py --write-baseline --reason "WHY" # a raise: one dated reason line
    python3 tools/owner_globals_check.py --write-baseline --reason "WHY" \\
        --raise-to host/owner-host.lisp=66 --admit fn-owner-sco-serial   # a raise by NAMED globals only

A RAISE needs an ACK.  --write-baseline raises a count (or adds a file) only
when planning/repair/ACKS.md has `ratchet:owner_globals_check:<file>` for it
(tools/ratchet.py); `--reason' then appends one dated line to the baseline's
"_reasons" list naming what moved; the baseline's other keys are file -> count.
A raise without the ACK line is refused.

A raise that admits only some of the globals over the baseline (the rest are
owed elsewhere and stay red) is `--raise-to FILE=N --admit NAME ...': FILE's
row becomes N, which must exceed its baseline by exactly the number of NAMEs,
each a global FILE has, and must not exceed what FILE has; every other row is
left as stored (nothing else is raised or lowered); the reason line names
the admitted globals.  The check stays red until the unadmitted ones go.
"""
import argparse
import datetime
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from tools import ratchet  # noqa: E402
from tools import lisp_source  # noqa: E402
BASELINE = ROOT / "tools" / "owner_globals_baseline.json"
HOST_DIRS = ("host", "books")
ACCESSOR = re.compile(r"(?:^|[\s(])[A-Za-z0-9*+/<>=!?.-]*-global\s+'(fn-owner-[a-z0-9*+/<>=!?.-]*)",
                      re.IGNORECASE)


def strip_comments_and_strings(text):
    """The source with `;' comments and `#|...|#' blocks removed and each
    string literal read as an empty one (tools/lisp_source.py)."""
    return lisp_source.code_only(text, strings='""')


def globals_of(text):
    """The distinct `fn-owner-*' names a global accessor names in TEXT."""
    return sorted({m.group(1).lower() for m in ACCESSOR.finditer(strip_comments_and_strings(text))})


def parked(root=ROOT):
    """Host files no build loads, parked with their owner (planning/host-
    parked.json, tools/host_check.py --loaded KNOWN).  Their globals are not
    the running owner's; when one is wired into a build its KNOWN entry must
    go (host_check --loaded is red until it does), and it is counted here."""
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


def write_named_raise(args, found, baseline, reasons, baseline_path):
    """--raise-to FILE=N --admit NAME...: raise ONE row by exactly the named globals."""
    path, _, text = args.raise_to.rpartition("=")
    if not path or not text.isdigit():
        print("owner_globals_check: --raise-to wants FILE=N")
        return 1
    new = int(text)
    have = found.get(path, [])
    had = baseline.get(path, 0)
    admitted = sorted(set(args.admit))
    problems = []
    if not (args.reason or "").strip():
        problems.append("a raise needs --reason")
    if new <= had:
        problems.append("{} is {} in the baseline: --raise-to only raises".format(path, had))
    if new > len(have):
        problems.append("{} has {} global(s): the baseline cannot exceed what is present".format(path, len(have)))
    if len(admitted) != new - had:
        problems.append("the raise adds {} but {} name(s) admitted: name each global the raise admits".format(
            new - had, len(admitted)))
    for name in admitted:
        if name not in have:
            problems.append("{} is not a global of {}".format(name, path))
    if problems:
        for problem in problems:
            print("owner_globals_check: " + problem)
        return 1
    counts = dict(baseline)
    counts[path] = new
    if ratchet.report("owner_globals_check", ratchet.refused(
            "owner_globals_check", ratchet.old_rows("owner_globals_check", baseline_path, lambda: baseline), counts)):
        return 1
    reasons.append("{}: {} ({} {}->{}, admitting {})".format(
        datetime.date.today().isoformat(), args.reason.strip(), path, had, new, ", ".join(admitted)))
    counts["_reasons"] = reasons
    baseline_path.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("owner_globals_check: {} raised {}->{}, admitting {}; {} present".format(
        path, had, new, ", ".join(admitted), len(have)))
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--list", action="store_true", help="print every name per file")
    parser.add_argument("--write-baseline", action="store_true",
                        help="write the counts as the baseline (refuses to raise any)")
    parser.add_argument("--reason", default=None,
                        help="with --write-baseline: why an ACKed raise happened (one dated line is kept); "
                             "the raise itself needs a ratchet:owner_globals_check:<file> line in "
                             "planning/repair/ACKS.md")
    parser.add_argument("--lower-to", default=None, metavar="FILE=N",
                        help="shrink one row to N, retaining unrelated over-baseline findings")
    parser.add_argument("--raise-to", default=None, metavar="FILE=N",
                        help="with --write-baseline --reason and --admit: raise only FILE's row, to N")
    parser.add_argument("--admit", action="append", default=[], metavar="NAME",
                        help="with --raise-to: a global the raise admits (repeat; as many as the raise adds)")
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
    stored = json.loads(baseline_path.read_text(encoding="utf-8")) if baseline_path.exists() else {}
    reasons = list(stored.get("_reasons", []))
    baseline = {k: v for k, v in stored.items() if not k.startswith("_")}
    if args.write_baseline and args.lower_to:
        path, _, value = args.lower_to.rpartition("=")
        if (not value.isdigit() or path not in baseline
                or int(value) >= baseline[path]):
            print("owner_globals_check: --lower-to must strictly shrink an existing row")
            return 1
        baseline[path] = int(value)
        baseline["_reasons"] = reasons
        baseline_path.write_text(json.dumps(baseline, indent=2, sort_keys=True) + "\n")
        print("owner_globals_check: {} lowered to {}; {} present".format(
            path, value, len(found.get(path, []))))
        return 0
    if args.write_baseline and args.raise_to:
        return write_named_raise(args, found, baseline, reasons, baseline_path)
    if args.write_baseline:
        raised = [(p, len(n), baseline.get(p)) for p, n in found.items()
                  if p not in baseline or len(n) > baseline[p]]
        if ratchet.report("owner_globals_check", ratchet.refused(
                "owner_globals_check", ratchet.old_rows("owner_globals_check", baseline_path, lambda: baseline),
                {p: len(n) for p, n in found.items()})):
            return 1
        if raised:
            reasons.append("{}: {} ({})".format(
                datetime.date.today().isoformat(), (args.reason or "ACKS.md ratchet").strip(),
                ", ".join("{} {}->{}".format(p, had or 0, have) for p, have, had in raised)))
        counts = {p: len(n) for p, n in found.items()}
        if reasons:
            counts["_reasons"] = reasons
        baseline_path.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print("owner_globals_check: baseline written, {} file(s), {} global(s)".format(
            len([k for k in counts if not k.startswith("_")]),
            sum(v for k, v in counts.items() if not k.startswith("_"))))
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
