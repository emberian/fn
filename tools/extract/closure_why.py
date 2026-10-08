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

With --check-tables it checks X3's one discovery of carried tables: the
tables core-world.lisp's snapshot carries with row digests (its
FN-CORE-TABLE-DIGESTS manifest) are exactly the `table:` targets of edges.tsv
(the tables an emitted form reads, found by xt-fe-export's closure walk) and
the host's INSTALL_TABLES; and no table is a defs.lisp unit.

usage: closure_why.py OUT [--tree TREE] [--target ID ...] [--json] [--check] [--check-tables]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import deque
from pathlib import Path

# X2's ban (EXTRACTION-PROGRAM-20261007.md section 6): ACL2's evaluator, LD, translator and printer
# are never reachable from a root of the served program.  The printer (FMT0, FMT1, FMT1!, ERROR-FMS)
# was reached only through the *1* scaffolding's WARNING1 and WORMHOLE-ER, which clruntime.lisp now
# defines as runtime entries.
BANNED = ("EV", "EV-W", "EV-REC", "EV-FNCALL", "EV-FNCALL-W", "LD-FN", "TRANS-EVAL",
          "TRANSLATE11", "TRANSLATE11-LOCAL-DEF", "TRANSLATE1", "TRANSLATE",
          "FMT0", "FMT1", "FMT1!", "ERROR-FMS")
BANNED_IDS = tuple("%s:ACL2::%s" % (k, n) for n in BANNED for k in ("raw", "star1"))

EVALUATOR = ("raw:ACL2::EV", "raw:ACL2::EV-W", "raw:ACL2::EV-REC", "raw:ACL2::LD-FN",
             "raw:ACL2::TRANS-EVAL", "raw:ACL2::TRANSLATE11", "raw:ACL2::TRANSLATE11-LOCAL-DEF",
             "raw:ACL2::FMT1",
             "star1:ACL2::EV", "star1:ACL2::EV-W", "star1:ACL2::EV-REC", "star1:ACL2::LD-FN",
             "star1:ACL2::TRANS-EVAL", "star1:ACL2::TRANSLATE11", "star1:ACL2::TRANSLATE11-LOCAL-DEF",
             "star1:ACL2::FMT1")


# the tables host/native/raw-trap.lisp fnn-install-raw-dispatch reads (core-export.lisp xt-carried-table-names)
INSTALL_TABLES = ("ACL2::FN-INTERFACES", "ACL2::FN-RAW-DISPATCH-VERDICTS")


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


def _sexp_end(text: str, i: int) -> int:
    """The index just past the object starting at TEXT[i] (a list, string, |symbol|, #\\char or atom)."""
    depth = 0
    while True:
        c = text[i]
        if c == '"' or c == "|":
            i += 1
            while text[i] != c:
                i += 2 if text[i] == "\\" else 1
        elif c == "#" and text[i + 1] == "\\":
            i += 2
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif depth == 0 and c in " \n\t":
            return i
        i += 1
        if depth == 0 and text[i - 1] in ')"|':
            return i


def qualified(name: str) -> str:
    return name if "::" in name else "ACL2::" + name


def snapshot_tables(core_world: str) -> list[str]:
    """The tables core-world.lisp's snapshot carries with digests: the keys of FN-CORE-TABLE-DIGESTS."""
    head = "(FN-CORE-TABLE-DIGESTS (TABLE-ALIST"
    at = core_world.find(head)
    if at < 0 or core_world.find(head, at + 1) >= 0:
        raise ValueError("core-world.lisp holds %s manifests, not one" % ("no" if at < 0 else "several"))
    i, names = at + len(head), []
    while True:
        while core_world[i] in " \n\t":
            i += 1
        if core_world[i] == ")":
            return names
        if core_world[i] != "(":
            raise ValueError("FN-CORE-TABLE-DIGESTS row is not a list at offset %d" % i)
        j = i + 1
        while core_world[j] not in " ()\n\t":
            j += 1
        names.append(qualified(core_world[i + 1:j]))
        i = _sexp_end(core_world, i)


def table_problems(out: Path) -> list[str]:
    """X3: the snapshot's tables against the forms closure's table reads and the install tables; [] when they agree."""
    _, graph = read_edges(out / "edges.tsv")
    read = {v.split(":", 1)[1] for vs in graph.values() for v in vs if v.startswith("table:")}
    want = read | set(INSTALL_TABLES)
    have = snapshot_tables((out / "core-world.lisp").read_text(encoding="latin-1"))
    problems = ["table %s is read by an emitted form but the snapshot does not carry it" % n
                for n in sorted(want - set(have))]
    problems += ["table %s is carried by the snapshot but no emitted form or install path reads it" % n
                 for n in sorted(set(have) - want)]
    problems += ["table %s is carried twice by the snapshot" % n for n in sorted({n for n in have if have.count(n) > 1})]
    problems += ["%s is a defs.lisp unit; tables are carried by the snapshot only" % u
                 for u in sorted(graph) if u.startswith("table:")]
    return problems


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("out", type=Path)
    ap.add_argument("--tree", type=Path)
    ap.add_argument("--target", action="append")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--check", action="store_true",
                    help="X2: exit 1, naming a path, if a BANNED unit is reachable from a root")
    ap.add_argument("--check-tables", action="store_true",
                    help="X3: exit 1, naming each table, unless the snapshot carries exactly the tables read")
    a = ap.parse_args(argv)
    if a.check_tables:
        problems = table_problems(a.out)
        for p in problems:
            print("closure_why: %s" % p, file=sys.stderr)
        if problems:
            return 1
        print("closure_why: the snapshot carries exactly the %d tables read" % len(snapshot_tables(
            (a.out / "core-world.lisp").read_text(encoding="latin-1"))))
        return 0
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
