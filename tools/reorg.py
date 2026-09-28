#!/usr/bin/env python3
"""The source-tree reorganisation's plan and dry run (planning/reorg-2026-09-28.md).

    python3 tools/reorg.py plan [--write]   # planning/reorg-plan.json from the graph
    python3 tools/reorg.py dry-run [--json] # what the pure move would change; writes nothing
    python3 tools/reorg.py floats           # books whose includes lift them above their subsystem

A DESIGN AID, NOT YET A MIGRATION.  Nothing here moves or edits a file:
`dry-run` only reads.  The move itself (git mv + rewrites) is held until ember
decides on the design (coordinator, 2026-09-28).

THE GRAPH is the farm's: `certify_books.local_closure` over the Makefile roots
(the one `shape_books.py` and `--affected-by` walk).  No second reader of
include-book.

SUBSYSTEM of a book = the subsystem of its name family (the first
hyphen-separated word of its file name; FAMILIES below; design section 1).
Its LAYER comes from LAYERS.  A book FLOATS when it includes a book of a higher
layer; `floats_to` is the highest layer its closure reaches.  Floating books
are the composition layer: each needs a per-book call (move to the higher
subsystem's proofs/, or cut the upward edge by promoting a statement to that
subsystem's api).  The plan records the call as `decision: null` until made.

ROLE is a suggestion only (the pure move keeps every book whole):
  test    under tests/acl2
  attach  a book whose events include defattach (goes to S/impl/attach)
  proofs  a book with no function definitions (theorems only)
  mixed   everything else: definitions and theorems together; the
          subsystem's lane splits it into api / impl / proofs by the recipe
          (planning/evidence/book-split-2026-09-28.md).

The pure move's target is books/S/NAME.lisp (tests: tests/acl2/S/NAME.lisp).
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import certify_books  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "planning" / "reorg-plan.json"

LAYERS = ["lib", "codec", "time", "crypto", "text", "config", "store",
          "nntp", "peer", "bp", "owner"]

FAMILIES = {
    "lib": "rev snoc defrecord deftransition defkeystone octets octet adt assumptions",
    "codec": "cbor frame records codec payload wire held record",
    "time": "clock scheduler",
    "crypto": "blake3 sha256 crypto hybrid stx lace principal identity subject key anchor tls",
    "text": "wildmat article msgid nov injection moderation poster post posting cancel control group",
    "config": "config",
    "store": ("store byte history pagestore checkpoint reclaim retention provenance acceptance "
              "journal heap container snapshot log state catalog index topic consumer replay "
              "statement node mailbox outcome visibility ideal"),
    "nntp": "nntp served protocol reader connection auth login account accounts public",
    "peer": "peer feed transfer relay path transit exchange refused source membership policy",
    "bp": "bp tcpcl app",
    "owner": "owner native web",
}
FAMILY = {word: sub for sub, words in FAMILIES.items() for word in words.split()}

DEFUN = re.compile(r"^\s*\((defund?|define|defun-inline|defun-nx|defund-nx)\s", re.M)
DEFATTACH = re.compile(r"^\s*\(defattach\b", re.M)

# Files outside books/ and tests/acl2/ that name book paths (dry-run reports
# the references a move would rewrite).
REFERENCE_GLOBS = ["Makefile", "host/**/*.lisp", "tools/extract/*.lisp",
                   "tools/extract/*.py", "tools/*.py", "tools/*.sh",
                   "planning/*.json", "docs/**/*.md", "specs/**/*.md"]


def subsystem(book: str) -> str:
    stem = book.rsplit("/", 1)[-1]
    if book.startswith("books/proto/"):
        return "lib"
    return FAMILY.get(stem.split("-")[0], "?")


def graph():
    roots = certify_books.default_books()
    return certify_books.local_closure(roots), roots


def role(book: str) -> str:
    if book.startswith("tests/"):
        return "test"
    text = "\n".join(line.split(";", 1)[0]
                     for line in (ROOT / f"{book}.lisp").read_text().splitlines())
    if DEFATTACH.search(text):
        return "attach"
    if not DEFUN.search(text):
        return "proofs"
    return "mixed"


def test_subsystem(book: str, closure: dict[str, list[str]]) -> str:
    """A test goes with the subsystem most of its direct book includes are in."""
    votes = collections.Counter(subsystem(d) for d in closure[book] if d.startswith("books/"))
    return votes.most_common(1)[0][0] if votes else "lib"


def target(book: str, sub: str) -> str:
    stem = book.rsplit("/", 1)[-1]
    if book.startswith("tests/acl2/"):
        return f"tests/acl2/{sub}/{stem}"
    return f"books/{sub}/{stem}"


def make_plan() -> dict:
    closure, roots = graph()
    layer = {s: i for i, s in enumerate(LAYERS)}
    subs = {}
    for book in closure:
        subs[book] = (test_subsystem(book, closure) if book.startswith("tests/")
                      else subsystem(book))
    floats: dict[str, int] = {}
    sys.setrecursionlimit(100000)

    def reach(book: str) -> int:
        if book not in floats:
            floats[book] = layer.get(subs[book], 0)
            floats[book] = max([floats[book]] + [reach(d) for d in closure[book]
                                                 if d.startswith("books/")])
        return floats[book]

    rows = []
    for book in sorted(closure):
        sub = subs[book]
        up = [d for d in closure[book] if d.startswith("books/")
              and layer.get(subs[d], 0) > layer.get(sub, 0)]
        rows.append({
            "book": book,
            "subsystem": sub,
            "layer": layer.get(sub),
            "role": role(book),
            "new_path": target(book, sub),
            "upward_includes": up,
            "floats_to": (LAYERS[reach(book)] if not book.startswith("tests/")
                          and reach(book) != layer.get(sub) else None),
            "decision": None,
        })
    return {
        "schema_version": 1,
        "description": ("Proposal (planning/reorg-2026-09-28.md). Generated by tools/reorg.py "
                        "plan; decisions are filled by hand after review. Nothing has moved."),
        "layers": LAYERS,
        "families": FAMILIES,
        "books": rows,
    }


def load_plan() -> dict:
    if PLAN.exists():
        return json.loads(PLAN.read_text())
    return make_plan()


def reference_files() -> list[Path]:
    seen = set()
    for pattern in REFERENCE_GLOBS:
        for path in ROOT.glob(pattern):
            if (path.is_file() and path not in seen and path != PLAN
                    and "build/" not in str(path.relative_to(ROOT))):
                seen.add(path)
    return sorted(seen)


def dry_run(plan: dict) -> dict:
    rows = plan["books"]
    moves = {r["book"]: r["new_path"] for r in rows if r["book"] != r["new_path"]}
    collisions = [p for p, n in collections.Counter(moves.values()).items() if n > 1]
    closure, _ = graph()
    # every include edge whose relative path changes: the includer is rewritten
    include_edits = collections.Counter()
    for book, deps in closure.items():
        for dep in deps:
            if book in moves or dep in moves:
                include_edits[book] += 1
    # host/ and tools/extract include-books reach books by path too
    references = {}
    pattern = re.compile(r"(?:books|tests/acl2)/[A-Za-z0-9_./-]+?(?=\.lisp\b|\"|\s|\)|,|$)")
    for path in reference_files():
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        hits = collections.Counter(m for m in pattern.findall(text) if m in moves)
        if hits:
            references[str(path.relative_to(ROOT))] = sum(hits.values())
    by_sub = collections.Counter(r["subsystem"] for r in rows)
    by_role = collections.Counter((r["subsystem"], r["role"]) for r in rows)
    floating = [r for r in rows if r["floats_to"]]
    return {
        "moves": len(moves),
        "collisions": collisions,
        "unassigned": [r["book"] for r in rows if r["subsystem"] == "?"],
        "books_whose_includes_are_rewritten": len(include_edits),
        "include_edges_rewritten": sum(include_edits.values()),
        "reference_files": references,
        "by_subsystem": dict(by_sub),
        "by_subsystem_role": {f"{s}/{r}": n for (s, r), n in sorted(by_role.items())},
        "floating": len(floating),
        "floating_by_pair": dict(collections.Counter(
            f"{r['subsystem']}->{r['floats_to']}" for r in floating).most_common()),
        "move_list": sorted(moves.items()),
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--write", action="store_true", help="write planning/reorg-plan.json")
    d = sub.add_parser("dry-run")
    d.add_argument("--json", action="store_true")
    d.add_argument("--moves", action="store_true", help="print every old -> new path")
    sub.add_parser("floats")
    args = parser.parse_args(argv)

    if args.command == "plan":
        plan = make_plan()
        if args.write:
            PLAN.write_text(json.dumps(plan, indent=2) + "\n")
            print(f"wrote {PLAN.relative_to(ROOT)}: {len(plan['books'])} books")
        else:
            json.dump(plan, sys.stdout, indent=2)
        return 0
    plan = load_plan()
    if args.command == "floats":
        for r in plan["books"]:
            if r["floats_to"]:
                print(f"{r['book']}: {r['subsystem']} -> {r['floats_to']} "
                      f"(via {', '.join(r['upward_includes']) or 'a lower include'})")
        return 0
    report = dry_run(plan)
    if args.json:
        json.dump(report, sys.stdout, indent=2)
        print()
        return 0
    print(f"reorg dry run (nothing written): {report['moves']} files would move")
    print(f"  collisions: {report['collisions'] or 'none'}; unassigned: {report['unassigned'] or 'none'}")
    print(f"  include-book edges rewritten: {report['include_edges_rewritten']} "
          f"in {report['books_whose_includes_are_rewritten']} books")
    print("  path references outside books/ and tests/acl2/ (file: count; planning/ledger.json,"
          " ledger.md and current.md are regenerated, not rewritten):")
    for name, count in sorted(report["reference_files"].items(), key=lambda kv: -kv[1]):
        print(f"    {name}: {count}")
    print("  books per subsystem:", report["by_subsystem"])
    print("  subsystem/role:", report["by_subsystem_role"])
    print(f"  floating books (need a per-book decision): {report['floating']}",
          report["floating_by_pair"])
    if args.moves:
        for old, new in report["move_list"]:
            print(f"  {old}.lisp -> {new}.lisp")
    return 0


if __name__ == "__main__":
    sys.exit(main())
