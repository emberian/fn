#!/usr/bin/env python3
"""Every tooth in tests/acl2 is a must-fail whose body TRANSLATES.

`std/testing/must-fail` succeeds when its form fails for any reason, with
the output suppressed.  A body that stopped translating -- a call at a stale
arity, an undefined function, a theorem name already in use -- "fails" and
the tooth passes while biting nothing.  The keystone audit of 2026-09-27
found 41 such forms in two test books after the arena flip changed argument
counts: PRF-191, PRF-132 and PRF-144 had never been evaluated, and every
certification was green.

`tests/acl2/must-fail-checked.lisp` defines `must-fail-checked`, which first
translates the claim the body makes (the theorem's term and hints, a new
theorem name, an assertion's expression) and only then runs the must-fail,
so certification refuses a tooth that does not translate.  This lint makes
that the only must-fail in tests/acl2: it fails on a bare `must-fail` (or
`must-fail!`, `must-fail-with-...`) head outside comments and strings,
including inside a test-local `defmacro` template, unless its line
declares `; must-fail-ok: <reason>`.  Accepted declarations are printed on
every run.

    python3 tools/must_fail_check.py            # the lint (exit 1 on a finding)
    python3 tools/must_fail_check.py --convert  # rewrite bare must-fails in place

`--convert` is idempotent and safe to rerun after a merge brings in a book
written with the bare form: it renames each bare head to `must-fail-checked`
and makes the book include "must-fail-checked" (replacing the std include).
Static, no ACL2, under a second.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
TEST_DIR = "tests/acl2"
SUPPORT = "must-fail-checked.lisp"
STD_INCLUDE = re.compile(
    r'\(include-book\s+"std/testing/must-fail"\s+:dir\s+:system\s*\)')
OWN_INCLUDE = '(include-book "must-fail-checked")'
DECLARATION = re.compile(r";\s*must-fail-ok:\s*\S")
# A bare must-fail-family head: `(must-fail`, `(must-fail!`,
# `(must-fail-with-error` ..., but not `(must-fail-checked`.
BARE = re.compile(r"\((must-fail(?:!|-with-[a-z-]+)?)(?=[\s()])", re.IGNORECASE)


def code_mask(text: str) -> list[bool]:
    """True at each character that is Lisp code (not comment, string or
    character literal)."""
    mask = [True] * len(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = False
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                mask[k] = False
            i = j + 1
        elif text.startswith("#|", i):
            j = text.find("|#", i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                mask[k] = False
            i = j
        elif text.startswith("#\\", i):
            for k in range(i, min(i + 3, n)):
                mask[k] = False
            i += 3
        else:
            i += 1
    return mask


def bare_sites(text: str) -> list[tuple[int, str, bool]]:
    """(line, head, declared) for each bare must-fail head in code."""
    mask = code_mask(text)
    lines = text.split("\n")
    found = []
    for match in BARE.finditer(text):
        if not mask[match.start()]:
            continue
        line = text.count("\n", 0, match.start()) + 1
        declared = bool(DECLARATION.search(lines[line - 1]))
        found.append((line, match.group(1), declared))
    return found


def books(root: Path) -> list[Path]:
    return sorted(p for p in (root / TEST_DIR).glob("*.lisp")
                  if p.name != SUPPORT)


def convert_text(text: str) -> str:
    mask = code_mask(text)
    lines = text.split("\n")
    pieces, last = [], 0
    for match in BARE.finditer(text):
        if not mask[match.start()]:
            continue
        line = text.count("\n", 0, match.start()) + 1
        if DECLARATION.search(lines[line - 1]):
            continue
        if match.group(1).lower() != "must-fail":
            continue  # a variant with other options: leave it to the lint
        pieces.append(text[last:match.start()])
        pieces.append("(must-fail-checked")
        last = match.end()
    pieces.append(text[last:])
    out = "".join(pieces)
    uses = "(must-fail-checked" in out
    if uses and OWN_INCLUDE not in out:
        if STD_INCLUDE.search(out):
            out = STD_INCLUDE.sub(OWN_INCLUDE, out, count=1)
        else:
            m = re.search(r'\(in-package\s+"ACL2"\)[^\n]*\n', out)
            if m is None:
                raise SystemExit("no in-package line to include after")
            out = out[:m.end()] + OWN_INCLUDE + "\n" + out[m.end():]
    if OWN_INCLUDE in out:
        # the std include is inside must-fail-checked; a second one is noise
        out = re.sub(STD_INCLUDE.pattern + r"[ \t]*\n?", "", out)
    return out


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--convert", action="store_true",
                        help="rewrite bare must-fails to must-fail-checked")
    parser.add_argument("--book", action="append", default=[], metavar="PATH",
                        help="check only these test books (repeatable)")
    args = parser.parse_args(argv)
    root = args.root
    selected = books(root)
    if args.book:
        chosen = [(Path(b) if Path(b).is_absolute() else root / b).resolve() for b in args.book]
        missing = [str(p) for p in chosen if not p.is_file()]
        if missing:
            print("must_fail_check --book: no such file: " + ", ".join(missing), file=sys.stderr)
            return 2
        selected = chosen
    if args.convert:
        changed = 0
        for path in selected:
            text = path.read_text()
            new = convert_text(text)
            if new != text:
                path.write_text(new)
                changed += 1
        print(f"must_fail_check --convert: {changed} book(s) rewritten")
    findings, declared = [], []
    for path in selected:
        rel = path.relative_to(root)
        for line, head, ok in bare_sites(path.read_text()):
            (declared if ok else findings).append(f"{rel}:{line}: {head}")
    for site in declared:
        print(f"declared (must-fail-ok): {site}")
    for site in findings:
        print(f"bare {site}: its body's translation is not checked; use "
              f"must-fail-checked (tools/must_fail_check.py --convert) or "
              f"declare `; must-fail-ok: <reason>`")
    print(f"must_fail_check: {len(selected)} test books, "
          f"{len(findings)} bare must-fail(s), {len(declared)} declared")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
