#!/usr/bin/env python3
"""The books a recorded decision took out of the certify roots.

planning/unhooked.json lists each unhooked book with the decision that
unhooked it (a `Dnn' that is a heading in planning/decisions.md).  Two
tools read it:

- `certify_books.py --lane' leaves a listed book out of the books it adds
  (the direct includers and test companions of the `--affected-by' books)
  and prints `unhooked (Dnn): BOOK' for it, instead of certifying a book
  the decision says is not expected to admit;
- `green_check.py --gate' reports a changed listed book as `unhooked (Dnn)'
  and does not count it as not green.

The list is not read from book comments: a header that says UNHOOKED is
prose for the reader, and no gate scans it.

    python3 tools/unhooked.py --check    # exit 1 on any finding

A finding is a listed book whose decision is missing or is no heading in
planning/decisions.md, a listed book with no source file, a book listed
twice, or a listed book that is a Makefile root (a root is hooked).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIST = Path("planning/unhooked.json")
DECISIONS = Path("planning/decisions.md")
SCHEMA = "fn-unhooked-v1"

_HEADING = re.compile(r"^###\s.*?\b(D\d+)\b")
_ID = re.compile(r"^D\d+$")


def decisions(root: Path = ROOT) -> set[str]:
    """Every `Dnn' named in a `### ' heading of planning/decisions.md."""
    found = set()
    path = root / DECISIONS
    if not path.is_file():
        return found
    for line in path.read_text().splitlines():
        m = _HEADING.match(line)
        if m:
            found.add(m.group(1))
    return found


def entries(root: Path = ROOT) -> list[dict]:
    path = root / LIST
    if not path.is_file():
        return []
    doc = json.loads(path.read_text())
    if doc.get("schema") != SCHEMA:
        raise ValueError(f"{LIST}: schema is not {SCHEMA}")
    return list(doc.get("books") or [])


def load(root: Path = ROOT) -> dict[str, str]:
    """BOOK -> its decision id, for the books listed."""
    return {e["book"]: e.get("decision", "") for e in entries(root)}


def findings(root: Path = ROOT, roots: list[str] | None = None) -> list[str]:
    if roots is None:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import ledger  # noqa: E402
        roots = ledger.makefile_roots()
    rooted = set(roots)
    known = decisions(root)
    out, seen = [], set()
    for e in entries(root):
        book = e.get("book", "")
        decision = e.get("decision", "")
        if book in seen:
            out.append(f"{book}: listed twice")
        seen.add(book)
        if not _ID.match(decision or ""):
            out.append(f"{book}: no decision cited")
        elif decision not in known:
            out.append(f"{book}: {decision} is no heading in {DECISIONS}")
        if not (root / f"{book}.lisp").is_file():
            out.append(f"{book}: no source {book}.lisp")
        if book in rooted:
            out.append(f"{book}: is a Makefile root, so it is hooked")
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args(argv)
    found = findings()
    for line in found:
        print(f"unhooked: {line}")
    if a.check:
        print(f"unhooked: {len(load())} books listed, {len(found)} findings")
        return 1 if found else 0
    for book, decision in sorted(load().items()):
        print(f"unhooked ({decision}): {book}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
