#!/usr/bin/env python3
"""A certified host book keeps its definitions; the theorems about them live in books/.

A host book (host/NAME.lisp, a Makefile root, ld'd by the images) ends with theorems
that only restate its own definitions (`*-refines-...-by-definition`).  The image ld's
the file and so proves them again at every build, and they are lines of host.  The
trailing run of `defthm`s of such a book moves to books/NAME-theorems.lisp, which
includes the host book -- when moving it changes nothing a reader of the host book
sees:

* the run is the end of the file (no definition, declaration or include follows it);
* no theorem of the run is named anywhere else in the tracked code (a keystone, a hint,
  a test, a document would be a reference);
* the host book has no `local` form, so the theory its theorems were proved in is the
  theory the including book has.

    python3 tools/host_theorems.py            # report
    python3 tools/host_theorems.py --check    # exit 1 when a host book still ends in such a run
    python3 tools/host_theorems.py --write    # move them (then list the new roots in the Makefile)
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import host_wrappers as hw, ledger  # noqa: E402

THEOREM = re.compile(r"\(\s*(defthmd?)\s+([^\s()]+)", re.I)


def target(rel: str) -> str:
    return "books/{}-theorems.lisp".format(Path(rel).stem)


def candidates(root: Path = ROOT) -> list[tuple[str, int, int, list[str]]]:
    """(host book, start, end, theorem names) for each movable trailing run."""
    roots = {r + ".lisp" for r in ledger.makefile_roots(root) if r.startswith("host/")}
    found = []
    for rel in sorted(roots):
        if not (root / rel).is_file():
            continue
        text = (root / rel).read_text(encoding="utf-8")
        blanked = hw.blank(text)
        forms = hw.top_forms(blanked)
        run = []
        for start, end in reversed(forms):
            if THEOREM.match(blanked[start:end]):
                run.append((start, end))
            else:
                break
        if not run or re.search(r"(?m)^\(local\b", blanked):
            continue
        run.reverse()
        names = [THEOREM.match(blanked[s:e]).group(2).lower() for s, e in run]
        first = _with_comments(text, run[0][0])
        found.append((rel, first, len(text), names))
    movable = []
    mentioned = hw.mentions(root, {n for _r, _s, _e, names in found for n in names})
    for rel, start, end, names in found:
        if all(set(mentioned.get(n, {})) <= {rel} and mentioned.get(n, {}).get(rel, 0) == 1
               for n in names):
            movable.append((rel, start, end, names))
    return movable


def _with_comments(text: str, start: int) -> int:
    """START moved up over the comment lines directly above it."""
    a = text.rfind("\n", 0, start) + 1
    while a > 0:
        prev = text.rfind("\n", 0, a - 1) + 1
        if text[prev:a - 1].lstrip().startswith(";"):
            a = prev
        else:
            break
    return a


def render(rel: str, moved: str) -> str:
    return ("; Moved from {rel} by tools/host_theorems.py; this book is their source now.\n"
            "; They only restate that host book's definitions, which it keeps.\n"
            '(in-package "ACL2")\n'
            '(include-book "../{rel_book}")\n\n{moved}').format(
                rel=rel, rel_book=rel[:-5], moved=moved.lstrip("\n"))


def findings(root: Path = ROOT) -> list[str]:
    out = [f"{rel} ends in {len(names)} theorem(s) that only restate it: "
           f"tools/host_theorems.py --write moves them to {target(rel)}"
           for rel, _s, _e, names in candidates(root)]
    roots = ledger.makefile_roots(root)
    for path in sorted((root / "books").glob("*-theorems.lisp")):
        head = path.read_text(encoding="utf-8").splitlines()[0]
        if head.startswith("; Moved from host/") \
                and path.relative_to(root).with_suffix("").as_posix() not in roots:
            out.append(f"{path.relative_to(root)} must be a Makefile root")
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--root", default=str(ROOT))
    args = ap.parse_args(argv)
    root = Path(args.root)
    movable = candidates(root)
    for rel, start, end, names in movable:
        text = (root / rel).read_text(encoding="utf-8")
        print("{}: {} theorem(s), {} lines -> {}".format(
            rel, len(names), text.count("\n", start, end), target(rel)))
        if args.write:
            moved = text[start:end]
            (root / target(rel)).write_text(render(rel, moved), encoding="utf-8")
            (root / rel).write_text(text[:start].rstrip("\n") + "\n", encoding="utf-8")
            print("  Makefile root to list: " + target(rel)[:-5])
    if args.check:
        found = findings(root)
        for line in found:
            print(line)
        return 1 if found else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
