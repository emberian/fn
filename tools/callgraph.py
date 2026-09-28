#!/usr/bin/env python3
"""The call graph of a function, through `defun' AND `defmacro' bodies.

    python3 tools/callgraph.py FN              # everything FN reaches, one per line
    python3 tools/callgraph.py FN --macros     # ... with the macros it went through
    python3 tools/callgraph.py FN --depth 2    # only two edges out
    python3 tools/callgraph.py FN --callers    # who reaches FN instead
    python3 tools/callgraph.py FN --json

Lane defprotocol's ask (2026-09-27): once host-lints turned the NNTP
dispatcher into a macro (`fn-nntp-command-dispatch', books/nntp.lisp), a
closure that followed only `defun' bodies saw a shallow graph -- the arms the
macro expands into were invisible, and so were the reply codes they return.
Nothing in tools/ answered "what does the host-called function reach".

HOW IT READS.  Every book (`books/', `tests/acl2/') and host file
(`tools/ledger.py''s `host_paths') is read with the ledger's non-evaluating
reader (`ledger.Reader'): nothing is interned, evaluated or expanded, and a
book is never loaded.  A DEFINITION is a `defun', `defund', `defun-nx',
`defun-inline', `define', `defun-sk', `defmacro' or `defabbrev' found anywhere
in a file's forms (inside `local', `encapsulate', `mutual-recursion',
`progn', `defsection', `when' ... ), except inside another definition (a
macro's template that writes `(defun ...)' is the macro's body, not a
definition) and except under `quote'.  `fn-defrecord' forms contribute the
functions the ledger's own expansion generates (books/defrecord.lisp).

AN EDGE is a MENTION: A -> B when the symbol B occurs anywhere in A's
definition and B is itself defined somewhere in the tree.  That is
deliberately wider than "B in function position": a macro builds its calls
in a backquoted template or from quoted symbols (`(list 'fn-foo x)'), and
reading only function positions is exactly how the dispatcher's arms went
missing.  The price is that a quoted symbol used as data (a table key that
happens to name a function) is an edge too.  A macro USE is an edge to the
macro, and the macro's body continues the walk, so a function that calls a
macro reaches whatever the macro's template names.  `tools/reach_check.py'
builds its graph from these definitions and edges.

WHAT IT CANNOT SEE.  A call built from a computed name (`intern', a
`make-event' that concatenates), an `apply$' of a symbol held in a variable,
and anything the reader cannot read (reported on stderr, and the file then
contributes nothing).  Two definitions of one name (a book and a test book,
or a local helper) are merged: the node's edges are the union.
"""
from __future__ import annotations

import argparse
import collections
from dataclasses import dataclass, field
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402
from ledger import Sym, head  # noqa: E402

ROOT = ledger.ROOT

FUNCTION_HEADS = {"defun", "defund", "defun-nx", "defun-inline", "defund-inline",
                  "define", "defun-sk"}
MACRO_HEADS = {"defmacro", "defabbrev"}
DEFINITION_HEADS = FUNCTION_HEADS | MACRO_HEADS
RECORD_HEADS = {"fn-defrecord", "fn-defrecord-export"}


@dataclass
class Definition:
    name: str
    kind: str  # "function" | "macro" | "record"
    path: str
    line: int
    form: object


@dataclass
class Graph:
    definitions: dict[str, list[Definition]] = field(default_factory=dict)
    edges: dict[str, set[str]] = field(default_factory=dict)
    unreadable: dict[str, str] = field(default_factory=dict)

    def kind(self, name: str) -> str:
        kinds = {d.kind for d in self.definitions.get(name, ())}
        return "macro" if kinds == {"macro"} else ("function" if kinds else "unknown")

    def reach(self, start: str, depth: int | None = None) -> dict[str, int]:
        """name -> edges from START, for everything START reaches."""
        return _walk(self.edges, start, depth)

    def callers(self, target: str, depth: int | None = None) -> dict[str, int]:
        backwards: dict[str, set[str]] = collections.defaultdict(set)
        for source, targets in self.edges.items():
            for one in targets:
                backwards[one].add(source)
        return _walk(backwards, target, depth)


def _walk(edges, start: str, depth: int | None) -> dict[str, int]:
    seen = {start: 0}
    frontier = [start]
    while frontier:
        following = []
        for name in frontier:
            distance = seen[name] + 1
            if depth is not None and distance > depth:
                continue
            for one in sorted(edges.get(name, ())):
                if one not in seen:
                    seen[one] = distance
                    following.append(one)
        frontier = following
    del seen[start]
    return seen


def symbols(form: object, found: set[str] | None = None) -> set[str]:
    """Every symbol anywhere in FORM (quoted and backquoted included)."""
    found = set() if found is None else found
    stack = [form]
    while stack:
        item = stack.pop()
        if isinstance(item, Sym):
            found.add(str(item))
        elif isinstance(item, list):
            stack.extend(item)
    return found


def definition_name(form: list) -> str | None:
    if len(form) < 2:
        return None
    target = form[1]
    if isinstance(target, list):  # (define (name ...) ...) spellings
        target = target[0] if target and isinstance(target[0], Sym) else None
    return str(target) if isinstance(target, Sym) else None


def collect(forms: list[tuple[object, int]], path: str, records: bool = True) -> list[Definition]:
    """Every definition in FORMS (top-level forms with their lines)."""
    found: list[Definition] = []

    def visit(form: object, line: int) -> None:
        if not isinstance(form, list) or not form:
            return
        name = head(form)
        if name in ("quote", "quasiquote"):
            return
        if name in DEFINITION_HEADS:
            defined = definition_name(form)
            if defined is not None:
                found.append(Definition(defined, "macro" if name in MACRO_HEADS else "function",
                                        path, line, form))
                return
        if records and name in RECORD_HEADS:
            try:
                expansion = (ledger.defrecord_expansion(form) if name == "fn-defrecord"
                             else ledger.defrecord_export_expansion(form))
            except Exception:  # an unusual spelling: the record adds nothing
                expansion = []
            for item in expansion:
                defined = definition_name(item) if head(item) in DEFINITION_HEADS else None
                if defined is not None:
                    found.append(Definition(defined, "record", path, line, item))
            return
        for item in form:
            visit(item, line)

    for form, line in forms:
        visit(form, line)
    return found


def read_file(path: Path, relative: str, records: bool = True) -> tuple[list[Definition], str | None]:
    try:
        forms = ledger.Reader(path.read_text(encoding="utf-8", errors="replace")).top_level()
    except ledger.ReadError as exc:
        return [], str(exc)
    return collect(forms, relative, records), None


def build(files: list[tuple[Path, str]], records: bool = True) -> Graph:
    """The graph over FILES ((path, repository-relative name) pairs)."""
    graph = Graph()
    for path, relative in files:
        found, error = read_file(path, relative, records)
        if error is not None:
            graph.unreadable[relative] = error
        for definition in found:
            graph.definitions.setdefault(definition.name, []).append(definition)
    known = set(graph.definitions)
    for name, definitions in graph.definitions.items():
        mentioned: set[str] = set()
        for definition in definitions:
            symbols(definition.form[2:], mentioned)
        graph.edges[name] = (mentioned & known) - {name}
    return graph


def tree_files() -> list[tuple[Path, str]]:
    return ledger.book_paths() + ledger.host_paths()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("function", help="the function (or macro) to start from")
    parser.add_argument("--macros", action="store_true",
                        help="list the macros the walk went through too (they are always followed)")
    parser.add_argument("--callers", action="store_true",
                        help="walk the graph backwards: who reaches FUNCTION")
    parser.add_argument("--depth", type=int, default=None, help="at most this many edges")
    parser.add_argument("--books-only", action="store_true",
                        help="books/ and tests/acl2/ only, no host files")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args(argv)

    files = ledger.book_paths() if arguments.books_only else tree_files()
    graph = build(files)
    for relative, error in sorted(graph.unreadable.items()):
        print(f"callgraph: {relative}: unreadable, contributes nothing: {error}", file=sys.stderr)
    start = arguments.function.lower()
    if start not in graph.definitions:
        print(f"callgraph: {start}: no definition in the tree", file=sys.stderr)
        return 2
    found = (graph.callers(start, arguments.depth) if arguments.callers
             else graph.reach(start, arguments.depth))
    rows = []
    for name, distance in sorted(found.items(), key=lambda item: (item[1], item[0])):
        kind = graph.kind(name)
        if kind == "macro" and not arguments.macros:
            continue
        where = graph.definitions[name][0]
        rows.append({"name": name, "kind": kind, "distance": distance,
                     "path": where.path, "line": where.line})
    if arguments.json:
        print(json.dumps({"function": start, "callers": arguments.callers,
                          "reached": rows}, indent=2))
        return 0
    for row in rows:
        mark = " [macro]" if row["kind"] == "macro" else ""
        print(f"{row['distance']:3d} {row['name']}{mark}  {row['path']}:{row['line']}")
    print(f"callgraph: {start} {'is reached by' if arguments.callers else 'reaches'} "
          f"{len(rows)} definition(s)" + ("" if arguments.macros else " (macros followed, not listed)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
