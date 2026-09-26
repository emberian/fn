#!/usr/bin/env python3
"""Every byte of a tracked file under books/ and host/ is ASCII (PKT-379).

A non-ASCII character in a book comment broke a native test that reads the
book as text, twice: a `§` in books/native-operator.lisp failed
test_native_operator_cli (operator-daily replaced it, e5c58f2e) and
qual-harness-c18 made its test read the book as UTF-8 (4ee732da).  Books and
host files are read by ACL2, by SBCL's compile-file in the native image
build, and by Python tools and tests, each with its own default external
format; ASCII is the one encoding they all agree on, so it is refused at the
source, with the file, line, column and byte named.

Debt, not exemption: tools/ascii_debt.json `debt.PKT-496` names the files
that carried a `§` in a comment when this check landed, each with its
exact count of non-ASCII lines.  Rewriting them changes 32 certified books,
the foundations among them (books/records, books/cbor), so it rides the next
closure recertification instead of costing one of its own.  A listed file is
reported and counted, never silent; `--strict` fails on any non-ASCII byte in
an unlisted file, on a listed file whose count differs (a new character in a
debt file is refused like any other), and on a listed file that is now clean
(so the list only shrinks).  No book needs a non-ASCII byte: the list has no
exemption section.

    python3 tools/ascii_check.py --strict     # make check
    python3 tools/ascii_check.py --list       # every non-ASCII byte, debt included
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import unicodedata

ROOT = Path(__file__).resolve().parent.parent
DEBT = ROOT / "tools" / "ascii_debt.json"
TREES = ("books", "host")
SKIP_SUFFIXES = (".cert", ".port", ".fasl", ".out", ".log")


def tracked(root: Path) -> list[Path]:
    """The tracked files under books/ and host/ (a certificate or build
    product is not source; untracked scratch is not checked)."""
    try:
        out = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", *TREES],
                             check=True, capture_output=True).stdout
        names = [n for n in out.decode("utf-8", "surrogateescape").split("\0") if n]
    except (OSError, subprocess.CalledProcessError):
        names = [p.relative_to(root).as_posix()
                 for tree in TREES for p in sorted((root / tree).rglob("*")) if p.is_file()]
    return [root / n for n in sorted(names) if not n.endswith(SKIP_SUFFIXES)]


def describe(raw: bytes) -> str:
    try:
        char = raw.decode("utf-8")
        return "U+%04X %s" % (ord(char), unicodedata.name(char, "?"))
    except UnicodeDecodeError:
        return "not UTF-8"


def findings(path: Path) -> list[tuple[int, int, bytes]]:
    """(line, column, the offending character's bytes) per non-ASCII run
    start; one entry per character, UTF-8 sequences kept together."""
    out = []
    for number, line in enumerate(path.read_bytes().split(b"\n"), 1):
        col = 0
        while col < len(line):
            byte = line[col]
            if byte < 0x80:
                col += 1
                continue
            width = 1
            while col + width < len(line) and width < 4 and 0x80 <= line[col + width] < 0xC0:
                width += 1
            out.append((number, col + 1, bytes(line[col:col + width])))
            col += width
    return out


def load_debt(path: Path = DEBT) -> dict[str, int]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return dict(data.get("debt", {}).get("PKT-496", {}))


def check(root: Path = ROOT, debt: dict[str, int] | None = None):
    """(refusals, debt lines seen, problems with the debt list)."""
    debt = load_debt() if debt is None else debt
    refusals, owed, problems = [], {}, []
    for path in tracked(root):
        rel = path.relative_to(root).as_posix()
        found = findings(path)
        lines = sorted({n for n, _, _ in found})
        if rel in debt:
            owed[rel] = len(lines)
            if len(lines) != debt[rel]:
                problems.append("%s: %d non-ASCII line(s), the debt list says %d%s" % (
                    rel, len(lines), debt[rel],
                    "" if len(lines) > debt[rel] else ": lower or remove its entry"))
                if len(lines) > debt[rel]:
                    refusals += [(rel, n, c, raw) for n, c, raw in found]
            continue
        refusals += [(rel, n, c, raw) for n, c, raw in found]
    for rel in sorted(set(debt) - set(owed)):
        problems.append("%s: listed as debt but not a tracked file under %s" % (
            rel, " or ".join(TREES)))
    return refusals, owed, problems


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--strict", action="store_true", help="fail on any refusal (make check)")
    parser.add_argument("--list", action="store_true", help="print every debt line too")
    args = parser.parse_args(argv)
    refusals, owed, problems = check()
    for rel, number, col, raw in refusals:
        print("REFUSED %s:%d:%d: byte%s %s (%s): books/ and host/ are ASCII (PKT-379)" % (
            rel, number, col, "s" if len(raw) > 1 else "",
            " ".join("0x%02X" % b for b in raw), describe(raw)))
    for problem in problems:
        print("DEBT " + problem)
    if args.list:
        for rel in sorted(owed):
            for number, col, raw in findings(ROOT / rel):
                print("debt %s:%d:%d: %s" % (rel, number, col, describe(raw)))
    print("ascii_check: %d refused, %d debt line(s) in %d file(s) (PKT-496), %d debt-list "
          "problem(s)" % (len(refusals), sum(owed.values()), len(owed), len(problems)))
    return 1 if args.strict and (refusals or problems) else 0


if __name__ == "__main__":
    sys.exit(main())
