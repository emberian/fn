#!/usr/bin/env python3
"""Rewrite rules that fire on every call of a primitive: a shrink-only gate.

A :rewrite rule whose left-hand side is a primitive applied to distinct
variables only -- (car x), (consp x), (member-equal x y) -- is tried on every
such term in the proofs of every book that includes it, and each try
backchains through its hypotheses.  On 2026-10-07 four of them
(books/owner-queued-work, books/failure-scope) took one host guard proof past
the 900 s certify limit after nothing but an include-order change: 13M rule
attempts for 402 prover steps (CONVERGE-1 red 1, lane/attach-order).

This reads the certified world, not source text: tools/coverage_dump.lisp
records, per theorem, `var_lhs' -- the heads of its :rewrite rules whose
left-hand side is a function of distinct variables only.  A theorem of a tree
book whose var_lhs meets HAZARD_HEADS is a row `THEOREM|HEAD'.

    python3 tools/hazard_rules_check.py                 # NEW rows -> exit 1
    python3 tools/hazard_rules_check.py --write         # shrink-only (tools/ratchet.py)
    python3 tools/hazard_rules_check.py --census PATH   # TSV: theorem, book:line, head

--world PATH is the dump (default build/coverage/world.json, written by
`tools/coverage.py dump`).  A dump without var_lhs predates this field and is
refused by name rather than read as "no rows".
"""
import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import coverage  # noqa: E402
import ratchet  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "planning" / "hazard-rules-baseline.json"
TOOL = "hazard_rules_check"

# Structural functions called in nearly every term the prover sees; a rule on
# (F vars) for one of these is tried on everything and backchains through its
# hypotheses there.  Type recognizers (true-listp, natp, stringp, ...) are
# left out on purpose: a rule (implies (fn-x-listp x) (true-listp x)) is the
# ordinary type-rule idiom, one cheap recognizer hypothesis, and gating it
# would bury the hazards (152 rows with them, 2026-10-07 census; the measured
# stalls were all car/consp/member-equal).
HAZARD_HEADS = frozenset({
    "car", "cdr", "consp", "nth", "len", "member-equal", "assoc-equal",
    "equal", "<", "binary-+",
})


class DumpError(Exception):
    pass


def rows_of(doc: dict) -> dict[str, dict]:
    """`THEOREM|HEAD' -> {theorem, book, head} for the tree's own books."""
    out = {}
    theorems = doc.get("theorems")
    if theorems is None:
        raise DumpError("the dump has no theorems")
    if theorems and not any("var_lhs" in t for t in theorems):
        raise DumpError("the dump predates var_lhs (tools/coverage_dump.lisp); "
                        "regenerate it with tools/coverage.py dump")
    for record in theorems:
        book = coverage.book_of(record.get("book"))
        if not coverage.ours(book):
            continue
        name = coverage.sym(record["name"])
        for head in sorted({coverage.sym(h) for h in record.get("var_lhs", [])}):
            if head in HAZARD_HEADS:
                out[f"{name}|{head}"] = {"theorem": name, "book": book, "head": head}
    return out


def load_baseline(path: Path | None = None) -> dict[str, int]:
    path = path or BASELINE
    return json.loads(path.read_text(encoding="utf-8"))["rows"]


def write_baseline(rows: dict[str, dict], path: Path | None = None) -> list[str]:
    path = path or BASELINE
    """Shrink-only write; returns the refusals (nothing written when any)."""
    new = {key: 1 for key in rows}
    old = ratchet.old_rows(TOOL, path, lambda: load_baseline(path))
    refusals = ratchet.refused(TOOL, old, new)
    if refusals:
        return refusals
    path.write_text(json.dumps({
        "description": "theorems whose :rewrite rules fire on every call of a primitive "
                       "(tools/hazard_rules_check.py); shrink-only",
        "rows": dict(sorted(new.items()))}, indent=1) + "\n", encoding="utf-8")
    return []


DEFINER = re.compile(r"^[ \t]*\((?:defthm|defthmd|defrule|defkeystone|defaxiom)\s+(\S+)",
                     re.IGNORECASE | re.MULTILINE)


def locate(book: str, theorem: str, root: Path = ROOT) -> str:
    """`books/x.lisp:LINE' of the form defining THEOREM, or the book alone."""
    path = root / book
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return book
    for match in DEFINER.finditer(text):
        if match.group(1).lower() == theorem:
            return f"{book}:{text.count(chr(10), 0, match.start()) + 1}"
    return book


def census(rows: dict[str, dict], root: Path = ROOT) -> list[str]:
    lines = ["theorem\tsite\thead"]
    for key in sorted(rows, key=lambda k: (rows[k]["book"], k)):
        row = rows[key]
        lines.append(f"{row['theorem']}\t{locate(row['book'], row['theorem'], root)}"
                     f"\t{row['head']}")
    return lines


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--world", type=Path, default=coverage.DEFAULT_WORLD)
    parser.add_argument("--write", action="store_true", help="shrink-only baseline write")
    parser.add_argument("--census", type=Path, metavar="PATH",
                        help="write the rows as TSV (theorem, book:line, head)")
    arguments = parser.parse_args(argv)
    try:
        rows = rows_of(coverage.load_json(arguments.world))
    except (OSError, ValueError, DumpError) as error:
        print(f"{TOOL}: NOT RUN -- {arguments.world}: {error}")
        return 2
    if arguments.census:
        arguments.census.write_text("\n".join(census(rows)) + "\n", encoding="utf-8")
        print(f"{TOOL}: {len(rows)} row(s) -> {arguments.census}")
    if arguments.write:
        refusals = write_baseline(rows)
        if ratchet.report(TOOL, refusals):
            return 1
        print(f"{TOOL}: baseline {len(rows)} row(s) -> {BASELINE.relative_to(ROOT)}")
        return 0
    if not BASELINE.exists():
        print(f"{TOOL}: no baseline at {BASELINE.relative_to(ROOT)}; {len(rows)} row(s)")
        return 1
    base = load_baseline()
    new = sorted(set(rows) - set(base))
    stale = sorted(set(base) - set(rows))
    print(f"{TOOL}: {len(rows)} row(s), {len(new)} NEW, {len(stale)} stale "
          f"(heads: {', '.join(sorted({r['head'] for r in rows.values()})) or 'none'})")
    for key in new:
        print(f"  NEW {key} ({rows[key]['book']}): a rewrite rule on every call of "
              f"{rows[key]['head']}; state it as :rule-classes nil or with a targeted "
              f"left-hand side")
    for key in stale:
        print(f"  stale {key}: gone from the world; --write lowers it")
    return 1 if new else 0


if __name__ == "__main__":
    sys.exit(main())
