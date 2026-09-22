#!/usr/bin/env python3
"""Which books open a codec theory at the top, for every proof in the book.

Finding F3 of planning/review-2026-09-22-proof-engineering.md.  A top-level
`(local (in-theory (enable fn-record-codec-vocabulary ...)))` puts the record,
statement or CBOR codec into every proof in the book; a goal that only
dispatches on a record kind then carries the whole codec, and when the bounded
CBOR profile made the codecs larger on 2026-09-21 proofs across the tree
stopped returning instead of failing.  Every repair in the two freeze records
of that day is "close the recognizer where the proof only dispatches on a
kind".  The rule (AGENTS.md): open a codec in the hint of the theorem that
decodes, never at the top of a book.

    python3 tools/theory_check.py --summary   # the line `make check` prints
    python3 tools/theory_check.py --table     # every top-level opening, codec first
    python3 tools/theory_check.py --json
    python3 tools/theory_check.py --strict    # exit 1 on a codec opening

WHAT IT READS.  Every `books/*.lisp`, as top-level forms.  A form `(local X)`
is unwrapped.  A form `(in-theory (enable a b ...))` or `(in-theory (e/d (a b
...) (...)))` opens `a`, `b`, ...; an entry `(:d f)` or `(:definition f)`
opens `f`; other runes are not theory names and are ignored.  A name is a
codec theory when it is a `deftheory` in one of the codec books below, or
its name says `codec`.  Everything else opened at the top of a book is
reported as a plain opening: allowed, counted, not flagged.

WHAT IT DOES NOT DECIDE.  Whether the proofs in the book reach the codec
through what they opened: that is what the prover measures, at 1800 s a
book.  This is a static reader of one habit with a measured cost.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
BOOKS = ROOT / "books"

# The books whose theories are "the codec": the CBOR codec and its
# invariants, the record and statement codecs, the frame codec.
CODEC_BOOKS = {
    "cbor", "cbor-invariants", "records", "records-canonicality",
    "statement", "statement-invariants", "frame", "frame-fields",
    "frame-octets", "frame-trailer", "frame-journal", "config",
    "bp-primary-cbor", "checkpoint-codec", "bp-node-machine-codec",
}

TOKEN = re.compile(r'''
    (?P<comment>;[^\n]*)              |
    (?P<block>\#\|.*?\|\#)            |
    (?P<string>"(?:\\.|[^"\\])*")     |
    (?P<open>\()                      |
    (?P<close>\))                     |
    (?P<quote>'|`|,@|,|\#\.)          |
    (?P<atom>[^\s()"';]+)
''', re.VERBOSE | re.DOTALL)


def forms(text: str) -> list:
    """The top-level forms of a book as nested lists of strings.

    Strings come back as their source spelling; atoms as lowercase text.
    Quote marks are dropped: `'(a b)` reads as `(a b)`, which is what a
    theory expression needs and nothing here cares about more.
    """
    stack: list[list] = [[]]
    for match in TOKEN.finditer(text):
        kind = match.lastgroup
        if kind in ("comment", "block", "quote"):
            continue
        if kind == "open":
            stack.append([])
        elif kind == "close":
            if len(stack) == 1:
                raise ValueError("unbalanced close paren")
            done = stack.pop()
            stack[-1].append(done)
        elif kind == "string":
            stack[-1].append(match.group())
        else:
            stack[-1].append(match.group().lower())
    if len(stack) != 1:
        raise ValueError("unbalanced open paren")
    return stack[0]


def opened_names(expression) -> list[str]:
    """The names a theory expression opens: enable's or e/d's first list."""
    if not isinstance(expression, list) or not expression:
        return []
    head = expression[0]
    entries: list = []
    if head == "enable":
        entries = expression[1:]
    elif head == "e/d" and len(expression) > 1 and isinstance(expression[1], list):
        entries = expression[1]
    elif head in ("union-theories", "set-difference-theories") and len(expression) > 1:
        return opened_names(expression[1])
    names = []
    for entry in entries:
        if isinstance(entry, str):
            names.append(entry)
        elif isinstance(entry, list) and len(entry) == 2 and entry[0] in (":d", ":definition"):
            names.append(entry[1])
    return names


def top_level_openings(text: str) -> list[list[str]]:
    """Each top-level in-theory form's opened names, local or not."""
    found = []
    for form in forms(text):
        if isinstance(form, list) and form and form[0] == "local" and len(form) > 1:
            form = form[1]
        if isinstance(form, list) and len(form) > 1 and form[0] == "in-theory":
            names = opened_names(form[1])
            if names:
                found.append(names)
    return found


def theories(books_dir: Path = BOOKS) -> dict[str, str]:
    """Every deftheory name to the book that defines it."""
    defined: dict[str, str] = {}
    for path in sorted(books_dir.glob("*.lisp")):
        for match in re.finditer(r"\(deftheory\s+([^\s()]+)", path.read_text(encoding="utf-8")):
            defined[match.group(1).lower()] = path.stem
    return defined


def is_codec(name: str, defined: dict[str, str]) -> bool:
    return "codec" in name or defined.get(name) in CODEC_BOOKS


def audit(books_dir: Path = BOOKS) -> dict:
    defined = theories(books_dir)
    rows = []
    for path in sorted(books_dir.glob("*.lisp")):
        try:
            openings = top_level_openings(path.read_text(encoding="utf-8"))
        except ValueError as error:
            rows.append({"book": f"books/{path.stem}", "unreadable": str(error),
                         "opened": [], "codec": []})
            continue
        opened = sorted({name for names in openings for name in names})
        if not opened:
            continue
        codec = [name for name in opened if is_codec(name, defined)]
        rows.append({"book": f"books/{path.stem}", "opened": opened, "codec": codec})
    rows.sort(key=lambda row: (not row["codec"], row["book"]))
    return {
        "schema": "fn-theory-check-v1",
        "books_read": sum(1 for _ in books_dir.glob("*.lisp")),
        "books_with_top_level_openings": len(rows),
        "books_opening_a_codec": sum(1 for row in rows if row["codec"]),
        "codec_theories": sorted({name for row in rows for name in row["codec"]}),
        "rows": rows,
    }


def summary(report: dict) -> str:
    return (f"theory-check: {report['books_with_top_level_openings']} of "
            f"{report['books_read']} books open a theory at the top for every "
            f"proof in them; {report['books_opening_a_codec']} open a CODEC "
            f"theory there ({len(report['codec_theories'])} distinct), which is "
            f"the habit the 2026-09-22 freeze paid for; --table names them.")


def table(report: dict) -> list[str]:
    width = max((len(row["book"]) for row in report["rows"]), default=4)
    lines = [f"{'CODEC':5}  {'BOOK':{width}}  OPENED AT TOP LEVEL"]
    for row in report["rows"]:
        flag = "codec" if row["codec"] else ""
        names = " ".join(row["codec"]) if row["codec"] else " ".join(row["opened"][:6])
        lines.append(f"{flag:5}  {row['book']:{width}}  {names}")
    return lines


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Codec theories opened book-wide.")
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--table", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 when any book opens a codec theory at the top")
    args = parser.parse_args(argv)
    report = audit()
    if args.json:
        print(json.dumps(report, indent=1, sort_keys=True))
    elif args.table:
        print("\n".join(table(report)))
    if args.summary or not (args.json or args.table):
        print(summary(report))
    return 1 if args.strict and report["books_opening_a_codec"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
