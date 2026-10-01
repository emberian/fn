#!/usr/bin/env python3
"""The tests that pin each protocol row's literal text (obstructions-6 item 55).

compress-7's merge reds were literal expectations of the served command table
(a HELP line, a CAPABILITIES line, the dispatch term's keyword tests) that a
REPL load never reaches: a lane that touches a row runs exactly the tests
that spell it, before the farm.

A ROW is one of
  help        a row of *fn-nntp-served-command-table* (books/nntp-help.lisp),
              whose HELP line is its keywords joined by one space;
  capability  a literal `(fn-nntp-string-octets "...")' line of a book
              function whose name says capabilit (books/*.lisp);
  keyword     each keyword of the table.
A PIN is a file under tests/ spelling the row's text: a HELP line whole; a
CAPABILITIES line as the string literal "LINE" in a file that also speaks of
capabilities (or "VERSION 2"); a keyword as the quoted token "KW" -- or, for a
keyword, a book spelling the dispatch term `(fn-nntp-keywordp K "KW")'.

    python3 tools/protocol_rows.py                    # every row and its pins
    python3 tools/protocol_rows.py --keyword COMPRESS # the rows naming COMPRESS
    python3 tools/protocol_rows.py --changed [BASE]   # rows whose text differs from
                                                      # BASE (default origin/dev):
                                                      # the old text's pins + the new's
    python3 tools/protocol_rows.py --roots ...        # only the runnable names, one a line

A test's runnable name: tests/acl2/X.lisp -> tests/acl2/X (a farm root);
tests/test_X.py -> tests.test_X (a unittest module); other files under tests/
(fixtures, fake nodes) and books are named as they are.  Reads the tree only
(git grep); runs nothing.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
TABLE_BOOK = "books/nntp-help.lisp"
TABLE_NAME = "*fn-nntp-served-command-table*"
OCTETS_LINE = re.compile(r'\(fn-nntp-string-octets\s+"([^"\\]*)"\)')
DEFUN = re.compile(r"^\(defun\s+(\S+)", re.MULTILINE)


def _git(*words: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *words], capture_output=True,
                          text=True, check=False).stdout


def _read(relative: str, base: str | None) -> str:
    if base:
        return _git("show", f"{base}:{relative}")
    path = ROOT / relative
    return path.read_text(encoding="utf-8") if path.exists() else ""


def table_rows(text: str) -> list[list[str]]:
    """The served command table's rows, from the defconst's source text."""
    start = text.find(f"(defconst {TABLE_NAME}")
    if start < 0:
        return []
    depth, end = 0, None
    for position in range(start, len(text)):
        if text[position] == "(":
            depth += 1
        elif text[position] == ")":
            depth -= 1
            if depth == 0:
                end = position
                break
    body = text[start:end]
    return [re.findall(r'"([^"\\]*)"', row)
            for row in re.findall(r'\(("[^()]*")\)', body)]


def capability_lines(texts: dict[str, str]) -> list[tuple[str, str]]:
    """(book, line) for each literal octet line inside a function whose name
    says capabilit, in each book's order."""
    found: list[tuple[str, str]] = []
    for relative, text in texts.items():
        import callgraph
        for definition in callgraph.collect(callgraph.ledger.Reader(text).top_level(), relative):
            if "capabilit" not in definition.name.lower():
                continue
            for line in OCTETS_LINE.findall(callgraph.ledger.source_text(definition.form)):
                if (relative, line) not in found:
                    found.append((relative, line))
    return found


def capability_books(base: str | None) -> dict[str, str]:
    listed = (_git("grep", "-l", "-i", "capabilit", base, "--", "books/*.lisp")
              if base else _git("grep", "-l", "-i", "capabilit", "--", "books/*.lisp"))
    names = [line.split(":", 1)[1] if base else line for line in listed.split()]
    return {relative: _read(relative, base) for relative in names}


def rows(base: str | None = None) -> list[dict]:
    """Every row at BASE (a git revision) or in the working tree."""
    out = []
    table = table_rows(_read(TABLE_BOOK, base))
    for row in table:
        out.append({"kind": "help", "text": " ".join(row), "where": TABLE_BOOK})
    for relative, line in capability_lines(capability_books(base)):
        out.append({"kind": "capability", "text": line, "where": relative})
    for keyword in sorted({k for row in table for k in row}):
        out.append({"kind": "keyword", "text": keyword, "where": TABLE_BOOK})
    return out


def runnable(relative: str) -> str:
    if relative.startswith("tests/acl2/") and relative.endswith(".lisp"):
        return relative[: -len(".lisp")]
    if re.fullmatch(r"tests/test_[A-Za-z0-9_]+\.py", relative):
        return "tests." + relative[len("tests/"): -len(".py")]
    return relative


def pins(row: dict) -> list[str]:
    """The files spelling ROW's text: tests/ for every kind; books for the
    keyword's dispatch term."""
    text = row["kind"] == "help" and row["text"] or '"' + row["text"] + '"'
    found = set(_git("grep", "-l", "-F", "-e", text, "--", "tests").split())
    if row["kind"] == "capability":
        # a one-word line ("POST") is a literal everywhere: a capability pin
        # is a file that also speaks of capabilities
        found &= set(_git("grep", "-l", "-i", "-e", "capabilit", "-e", "VERSION 2",
                          "--", "tests").split())
    elif row["kind"] == "keyword":
        found |= set(_git("grep", "-l", "-E", "-e",
                          r'\(fn-nntp-keywordp [a-z0-9-]+ "' + re.escape(row["text"]) + '"\\)',
                          "--", "books").split())
    return sorted(runnable(relative) for relative in found)


def changed(base: str) -> list[dict]:
    """The rows whose text is at BASE and not here, or here and not at BASE."""
    then = {(row["kind"], row["text"]): row for row in rows(base)}
    now = {(row["kind"], row["text"]): row for row in rows(None)}
    out = []
    for key in sorted(set(then) ^ set(now)):
        row = dict(then.get(key) or now[key])
        row["change"] = "removed" if key in then else "added"
        out.append(row)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--keyword", help="only the rows naming this keyword (any case)")
    parser.add_argument("--changed", nargs="?", const="origin/dev", metavar="BASE",
                        help="only the rows whose text differs from BASE (default origin/dev)")
    parser.add_argument("--roots", action="store_true",
                        help="print only the runnable names, deduplicated, one a line")
    args = parser.parse_args(argv)
    if args.changed:
        selected = changed(args.changed)
    else:
        selected = rows(None)
    if args.keyword:
        word = args.keyword.upper()
        selected = [row for row in selected if word in row["text"].upper().split()]
    if not selected:
        print("protocol_rows: no row" + (" changed" if args.changed else " selected"),
              file=sys.stderr)
        return 0
    everything: set[str] = set()
    for row in selected:
        found = pins(row)
        everything.update(found)
        if not args.roots:
            change = f" [{row['change']}]" if "change" in row else ""
            print(f"{row['kind']:10} {row['text']!r}{change} ({row['where']}): "
                  f"{len(found)} pin(s)")
            for name in found:
                print(f"    {name}")
    if args.roots:
        print("\n".join(sorted(everything)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
