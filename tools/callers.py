#!/usr/bin/env python3
"""Every call site of one function: file:line and the event it sits in.

    python3 tools/callers.py FN [FN ...]          # call sites in books/ host/ tests/
    python3 tools/callers.py FN --mentions        # also non-call uses ('fn, #'fn, runes, hints)
    python3 tools/callers.py FN --in books/x.lisp --in host/
    python3 tools/callers.py FN --json

A lane asked for this instead of grepping the whole tree (paged-history,
2026-09-29): a grep for a name matches comments, strings, longer names and
the definition, and says nothing about which event the use is in.  This reads
the Lisp lexically -- comments (`;`, `#| |#`), strings, characters (`#\\x`)
and `|quoted symbols|` are skipped; names compare case-insensitively with any
package prefix dropped -- and classifies each occurrence of FN:

  call      `(FN ...)` (including `(FN)` and under `mbe`/`ec-call`);
  define    the name position of `defun`/`defund`/`define`/`defmacro`/... ;
  mention   anything else (`'FN`, `#'FN`, `(:definition FN)`, a hint's
            `:in-theory (disable FN)`), shown only with --mentions.

Each line names the enclosing top-level event, `(defthm NAME ...)`, so a
caller is found without opening the book.  Python test files under tests/
are searched as text (whole-word, case-insensitive) and reported as `text`.
The scan never reads the Lisp reader or evaluator and never walks build/.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PLACES = ("books", "host", "tests")

DEFINERS = {
    "defun", "defund", "defun-inline", "defund-inline", "defun-nx", "defund-nx",
    "defun-sk", "defmacro", "define", "defabbrev", "defn", "defnd",
    "defun$", "defstub", "defconst", "defthm", "defthmd", "defrule", "defruled",
}

TOKEN = re.compile(r"""
    (?P<nl>\n)
  | (?P<comment>;[^\n]*)
  | (?P<block>\#\|)
  | (?P<string>"(?:[^"\\]|\\.)*")
  | (?P<char>\#\\(?:[A-Za-z][A-Za-z0-9-]*|.))
  | (?P<open>\()
  | (?P<close>\))
  | (?P<function>\#')
  | (?P<quote>['`]|,@|,)
  | (?P<atom>(?:\|[^|]*\||[^\s()'`,";|])+)
  | (?P<space>[ \t\r\f]+)
  | (?P<other>.)
""", re.VERBOSE | re.DOTALL)


def bare(atom: str) -> str:
    """The symbol's name, lowercased, without its package prefix."""
    name = atom.rsplit("::", 1)[-1]
    if ":" in name and not name.startswith(":"):
        name = name.rsplit(":", 1)[-1]
    return name.replace("|", "").lower()


def skip_block(text: str, start: int) -> int:
    """The index just past the `|#` closing the block comment opened before
    START, honouring nesting as the Common Lisp reader does."""
    depth, index = 1, start
    while depth and index < len(text):
        if text.startswith("#|", index):
            depth, index = depth + 1, index + 2
        elif text.startswith("|#", index):
            depth, index = depth - 1, index + 2
        else:
            index += 1
    return index


def lisp_sites(text: str, names: set[str]) -> list[dict]:
    """Occurrences of NAMES in one Lisp source, classified."""
    sites: list[dict] = []
    line, index, depth = 1, 0, 0
    after_open = False          # the previous significant token was `(`
    top: list[str] = []         # the current top-level form's head and name
    head_stack: list[str | None] = []   # each open list's head symbol
    position = 0                # the index of the current atom in its list
    positions: list[int] = []
    while index < len(text):
        match = TOKEN.match(text, index)
        kind = match.lastgroup
        value = match.group()
        index = match.end()
        if kind == "nl":
            line += 1
            continue
        if kind in ("comment", "space", "other"):
            continue
        if kind == "block":
            end = skip_block(text, index)
            line += text.count("\n", index, end)
            index = end
            continue
        if kind in ("string", "char"):
            line += value.count("\n")
            after_open = False
            position += 1
            continue
        if kind == "open":
            if depth == 0:
                top = []
            depth += 1
            head_stack.append(None)
            positions.append(position)
            position = 0
            after_open = True
            continue
        if kind == "close":
            if depth:
                depth -= 1
                head_stack.pop()
                position = positions.pop() + 1
            after_open = False
            continue
        if kind in ("quote", "function"):
            continue
        # an atom
        name = bare(value)
        if depth and position == 0:
            head_stack[-1] = name
        if depth == 1 and len(top) < 2:
            top.append(name)
        if name in names:
            previous = text[match.start() - 2:match.start()]
            quoted = previous.endswith("'") or previous == "#'"
            if after_open and not quoted:
                site_kind = "call"
            elif (depth and position == 1 and head_stack[-1] in DEFINERS
                  and not quoted):
                site_kind = "define"
            else:
                site_kind = "mention"
            sites.append({"line": line, "kind": site_kind, "name": name,
                          "event": " ".join(top[:2]) if top else ""})
        after_open = False
        position += 1
    return sites


def text_sites(text: str, names: set[str]) -> list[dict]:
    """Whole-word, case-insensitive occurrences in a non-Lisp file."""
    pattern = re.compile(
        r"(?<![\w-])(" + "|".join(re.escape(name) for name in sorted(names))
        + r")(?![\w-])", re.IGNORECASE)
    sites = []
    for number, text_line in enumerate(text.splitlines(), 1):
        for found in pattern.finditer(text_line):
            sites.append({"line": number, "kind": "text",
                          "name": found.group(1).lower(), "event": ""})
    return sites


def candidate_files(root: Path, places: list[str]) -> list[Path]:
    files: list[Path] = []
    for place in places:
        path = (root / place)
        if path.is_file():
            files.append(path)
        elif path.is_dir():
            files.extend(sorted(p for p in path.rglob("*")
                                if p.suffix in (".lisp", ".lsp", ".acl2", ".py")
                                and p.is_file()))
    return files


def scan(root: Path, names: list[str], places: list[str]) -> list[dict]:
    wanted = {bare(name) for name in names}
    needles = [name.encode() for name in wanted]
    results: list[dict] = []
    for path in candidate_files(root, places):
        raw = path.read_bytes()
        lowered = raw.lower()
        if not any(needle in lowered for needle in needles):
            continue
        text = raw.decode("utf-8", errors="replace")
        sites = (text_sites(text, wanted) if path.suffix == ".py"
                 else lisp_sites(text, wanted))
        relative = str(path.relative_to(root))
        for site in sites:
            results.append({"file": relative, **site})
    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="file:line of every call site of FN across books/, host/ "
                    "and tests/ (see the module docstring).")
    parser.add_argument("names", nargs="+", metavar="FN")
    parser.add_argument("--in", dest="places", action="append", default=None,
                        help="a file or directory under the root to search "
                             "(repeatable; default books/ host/ tests/)")
    parser.add_argument("--mentions", action="store_true",
                        help="also print non-call occurrences")
    parser.add_argument("--no-text", action="store_true",
                        help="skip Python files (the text search)")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    places = args.places or list(DEFAULT_PLACES)
    sites = scan(args.root.resolve(), args.names, places)
    if args.no_text:
        sites = [site for site in sites if site["kind"] != "text"]
    shown = [site for site in sites
             if args.mentions or site["kind"] in ("call", "define", "text")]
    counts: dict[str, int] = {}
    for site in sites:
        counts[site["kind"]] = counts.get(site["kind"], 0) + 1
    if args.json:
        print(json.dumps({"names": args.names, "places": places,
                          "counts": counts, "sites": shown}, indent=2))
    else:
        for site in shown:
            event = f"  in ({site['event']} ...)" if site["event"] else ""
            label = site["kind"] if len(args.names) == 1 else \
                f"{site['kind']} {site['name']}"
            print(f"{site['file']}:{site['line']}: {label}{event}")
        summary = ", ".join(f"{kind} {counts.get(kind, 0)}"
                            for kind in ("define", "call", "mention", "text"))
        hidden = "" if args.mentions else " (mentions with --mentions)"
        print(f"{' '.join(args.names)}: {summary}{hidden}")
    return 0 if any(site["kind"] in ("call", "define") for site in sites) else 1


if __name__ == "__main__":
    sys.exit(main())
