#!/usr/bin/env python3
"""Why a unit is in the extracted closure: paths over the reference graph.

`xt-fe-export` (tools/extract/forms-export.lisp) writes OUT/edges.tsv: one
`#root<TAB>ID` line per root, then one `ID<TAB>TARGET TARGET ...` line per
unit, the targets being the unit ids that unit's forms reference.  This reads
it and answers, for a set of TARGET units (default: ACL2's evaluator, EVALUATOR
below):

* the boundary: every edge from fn's own code (a unit whose symbol is named
  FN... ) into ACL2 system code that reaches a target, with one shortest path
  from that edge to a target.  Each is either a host-side decision that
  belongs in a book or a call that should be a compiled function;
* the roots that reach a target, with the host file:line that names the root
  (TREE/host/native/*.lisp, the files tools/extract/host_tokens.py scans);
* how many units are reachable only through those boundary edges.

usage: closure_why.py OUT [--tree TREE] [--target ID ...] [--json] [--check]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import deque
from pathlib import Path

# X2's ban (EXTRACTION-PROGRAM-20261007.md section 6): ACL2's evaluator, LD and translator are never
# reachable from a root of the served program.  FMT1 (ACL2's printer, reached through WARNING1 and
# WORMHOLE-ER) is reported with them but not yet banned: its callers are being classified.
BANNED = ("EV", "EV-W", "EV-REC", "EV-FNCALL", "EV-FNCALL-W", "LD-FN", "TRANS-EVAL",
          "TRANSLATE11", "TRANSLATE11-LOCAL-DEF", "TRANSLATE1", "TRANSLATE")
BANNED_IDS = tuple("%s:ACL2::%s" % (k, n) for n in BANNED for k in ("raw", "star1"))

EVALUATOR = ("raw:ACL2::EV", "raw:ACL2::EV-W", "raw:ACL2::EV-REC", "raw:ACL2::LD-FN",
             "raw:ACL2::TRANS-EVAL", "raw:ACL2::TRANSLATE11", "raw:ACL2::TRANSLATE11-LOCAL-DEF",
             "raw:ACL2::FMT1",
             "star1:ACL2::EV", "star1:ACL2::EV-W", "star1:ACL2::EV-REC", "star1:ACL2::LD-FN",
             "star1:ACL2::TRANS-EVAL", "star1:ACL2::TRANSLATE11", "star1:ACL2::TRANSLATE11-LOCAL-DEF",
             "star1:ACL2::FMT1")


def read_edges(path: Path) -> tuple[list[str], dict[str, list[str]]]:
    roots, graph = [], {}
    for line in path.read_text(encoding="latin-1").splitlines():
        if not line:
            continue
        head, _, rest = line.partition("\t")
        if head == "#root":
            roots.append(rest)
        else:
            graph[head] = rest.split() if rest else []
    return roots, graph


def symbol_name(uid: str) -> str:
    return uid.rsplit("::", 1)[-1]


def is_fn(uid: str) -> bool:
    """fn's own code: a function or variable named FN... (FN-, FNN-, *FN...)."""
    return symbol_name(uid).lstrip("*").startswith("FN")


def reaches(graph: dict[str, list[str]], targets: set[str]) -> set[str]:
    """Every unit with a path to a target (the targets included)."""
    rev: dict[str, list[str]] = {}
    for u, vs in graph.items():
        for v in vs:
            rev.setdefault(v, []).append(u)
    seen, todo = set(targets), deque(targets)
    while todo:
        v = todo.popleft()
        for u in rev.get(v, ()):
            if u not in seen:
                seen.add(u)
                todo.append(u)
    return seen


def shortest(graph: dict[str, list[str]], start: str, targets: set[str]) -> list[str] | None:
    prev, todo = {start: None}, deque([start])
    while todo:
        u = todo.popleft()
        if u in targets:
            path = []
            while u is not None:
                path.append(u)
                u = prev[u]
            return path[::-1]
        for v in graph.get(u, ()):
            if v not in prev:
                prev[v] = u
                todo.append(v)
    return None


def reachable(graph: dict[str, list[str]], starts, blocked=frozenset()) -> set[str]:
    seen, todo = set(), deque(s for s in starts if s not in blocked)
    seen.update(todo)
    while todo:
        u = todo.popleft()
        for v in graph.get(u, ()):
            if v not in seen and (u, v) not in blocked:
                seen.add(v)
                todo.append(v)
    return seen


def host_sites(tree: Path, names: list[str]) -> dict[str, str]:
    """NAME -> the first host/native file:line that applies it, `(name' (case-insensitive)."""
    out: dict[str, str] = {}
    want = {n.lower(): n for n in names}
    pat = re.compile(r"\((" + "|".join(re.escape(n) for n in sorted(want, key=len, reverse=True)) + r")[\s)]",
                     re.IGNORECASE) if want else None
    for f in sorted((tree / "host" / "native").glob("*.lisp")):
        for i, line in enumerate(f.read_text(encoding="latin-1").splitlines(), 1):
            if line.lstrip().startswith(";"):
                continue
            for m in pat.finditer(line):
                n = want[m.group(1).lower()]
                out.setdefault(n, "%s:%d" % (f.relative_to(tree), i))
    return out


def analyse(roots: list[str], graph: dict[str, list[str]], targets: set[str], tree: Path | None):
    present = {t for t in targets if t in graph}
    bad = reaches(graph, present)
    boundary = []
    for u in sorted(graph):
        if not is_fn(u) or u not in bad:
            continue
        for v in sorted(graph[u]):
            if v in bad and not is_fn(v):
                boundary.append({"caller": u, "callee": v, "path": shortest(graph, v, present)})
    root_rows = []
    all_roots = sorted({r for r in roots} | {"star1:" + r.split(":", 1)[1] for r in roots})
    names = sorted({symbol_name(r).lower() for r in all_roots if r in bad})
    sites = host_sites(tree, names) if tree else {}
    for r in all_roots:
        if r in bad:
            root_rows.append({"root": r, "host": sites.get(symbol_name(r).lower()),
                              "path": shortest(graph, r, present)})
    full = reachable(graph, all_roots)
    cut = reachable(graph, all_roots, frozenset((b["caller"], b["callee"]) for b in boundary))
    return {"targets_present": sorted(present), "boundary": boundary, "roots": root_rows,
            "units": len(graph), "reachable": len(full), "reachable_without_boundary": len(cut)}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("out", type=Path)
    ap.add_argument("--tree", type=Path)
    ap.add_argument("--target", action="append")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--check", action="store_true",
                    help="X2: exit 1, naming a path, if a BANNED unit is reachable from a root")
    a = ap.parse_args(argv)
    roots, graph = read_edges(a.out / "edges.tsv")
    if a.check:
        all_roots = sorted(set(roots) | {"star1:" + r.split(":", 1)[1] for r in roots})
        banned = {b for b in BANNED_IDS if b in graph}
        bad = [p for p in (shortest(graph, r, banned) for r in all_roots) if p]
        if bad:
            bad.sort(key=len)
            print("closure_why: ACL2's evaluator is reachable from %d root(s); shortest: %s"
                  % (len(bad), " > ".join(bad[0])), file=sys.stderr)
            return 1
        print("closure_why: no banned unit reachable (%d banned ids present in the closure)" % len(banned))
        return 0
    r = analyse(roots, graph, set(a.target or EVALUATOR), a.tree)
    if a.json:
        json.dump(r, sys.stdout, indent=1)
        print()
        return 0
    print("targets present: %s" % " ".join(r["targets_present"]))
    print("units %d; reachable from roots %d; without the boundary edges %d"
          % (r["units"], r["reachable"], r["reachable_without_boundary"]))
    print("boundary edges (fn code -> ACL2 system code reaching a target): %d" % len(r["boundary"]))
    for b in r["boundary"]:
        print("  %s -> %s :: %s" % (b["caller"], b["callee"], " > ".join(b["path"] or [])))
    print("roots reaching a target: %d" % len(r["roots"]))
    for row in r["roots"]:
        print("  %s [%s] :: %s" % (row["root"], row["host"], " > ".join(row["path"] or [])))
    return 0


if __name__ == "__main__":
    sys.exit(main())
