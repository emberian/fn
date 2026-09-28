#!/usr/bin/env python3
"""Who calls each host definition: the table behind deleting a dead one.

    python3 tools/host_callers.py                 # every host definition, one row each
    python3 tools/host_callers.py --status zero   # only the ones nothing reaches
    python3 tools/host_callers.py --name FN       # one row, its callers listed
    python3 tools/host_callers.py --json
    python3 tools/host_callers.py --check         # the make-check lint (warn-only)

THE SUBJECTS are the `defun' / `defmacro' (every head tools/callgraph.py
counts as a definition) found in `host/*.lisp' and `host/native/*.lisp'.

A MENTION of a subject is any of:
  lisp    the symbol, package prefix stripped, anywhere in a Lisp form of a
          tracked `.lisp'/`.lsp' file (quoted, backquoted and `#''d
          included, so `(fnn-call 'fn-x ...)', `fnn-core', `defattach' and a
          macro template's calls all count), attributed to the outermost
          definition that holds it, or to the top-level form if none does;
  string  the name inside a Lisp string literal (a `find-symbol' list, a
          `--eval' argument a Lisp driver builds);
  script  the name, case-insensitive, at symbol boundaries, in any tracked
          Python, shell, Scheme, C, Makefile, `packaging/' or `bin/' file
          (tools/run_store.py's calls, the launchers, the systemd units);
  registry  the same in `planning/*.json' (not the generated ledger);
  doc     the same in Markdown/text, in planning/evidence/ and in the
          generated ledger files: reported, never a caller.
A mention from inside the subject's own definition is not counted.

STATUS is reachability, not a direct count: the ROOTS are every mention
from outside the subjects (a book, a top-level form, a script, a registry
entry); a subject is `called' when a non-test root reaches it through
subject-to-subject mentions, `test-only' when only a root under tests/
does, and `zero' otherwise -- including a cluster of subjects that mention
only each other (their `callers' column is non-empty, the row says
`cluster').  A raw `acl2_*1*_acl2::' definition (an executable counterpart
ACL2 itself runs) is a root.  A name defined twice is one row.

WHAT IT CANNOT SEE.  A call through a name computed at run time (`intern' of
a concatenation, a `do-symbols' walk by prefix), and a caller outside the
tracked tree (an operator typing at the REPL).  So a `zero' row is a
candidate, never a verdict: read the function before deleting it, and
delete one per commit quoting the row (build/coordinator/queue/
uncalled-host-defuns.txt; flip-cleanup nearly deleted a function
tools/run_store.py calls).

--check prints the zero rows that are not in tools/host_callers_baseline.json
(each baseline entry names why it stays uncalled) and exits 0: warn-only
until a later lane turns it into a refusal.
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
import callgraph  # noqa: E402
import ledger  # noqa: E402
from ledger import Sym, head  # noqa: E402

ROOT = ledger.ROOT
BASELINE = ROOT / "tools" / "host_callers_baseline.json"
HOST_PREFIXES = ("host/",)
LISP_SUFFIXES = (".lisp", ".lsp")
SCRIPT_SUFFIXES = (".py", ".sh", ".scm", ".c", ".h", ".mjs", ".in", ".service", ".toml")
GENERATED = {"planning/ledger.json", "planning/ledger.md", "planning/current.md",
             "planning/current-view.json"}
TOKEN = re.compile(r"[A-Za-z0-9*+<>=/!?%&$^~_.-]+")


def tracked(root: Path = ROOT) -> list[str]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=root, check=True,
                         capture_output=True).stdout.decode()
    return [p for p in out.split("\0") if p]


def bare(name: str) -> str:
    """A symbol without its package prefix (`acl2::fn-x', `sb-ext:quit')."""
    return name.rsplit(":", 1)[-1] if ":" in name.lstrip(":") else name.lstrip(":")


def category(relative: str) -> str:
    """The kind of mention a file makes (lisp files get lisp/string first)."""
    if relative in GENERATED or relative.startswith("planning/evidence/"):
        return "doc"
    if relative.endswith((".md", ".txt")):
        return "doc"
    if relative.startswith("planning/") and relative.endswith(".json"):
        return "registry"
    name = relative.rsplit("/", 1)[-1]
    if (relative.endswith(SCRIPT_SUFFIXES) or name == "Makefile"
            or relative.startswith(("packaging/", "bin/"))):
        return "script"
    return ""


def is_test(relative: str) -> bool:
    return relative.startswith("tests/")


class Mentions:
    """name -> list of (category, where, owner-or-None, is_test)."""

    def __init__(self, names: set[str]) -> None:
        self.names = names
        self.rows: dict[str, list[tuple[str, str, str | None, bool]]] = collections.defaultdict(list)
        self.unreadable: dict[str, str] = {}

    def text(self, text: str, cat: str, where: str, owner: str | None, test: bool) -> None:
        for match in set(token.lower().rstrip(".") for token in TOKEN.findall(text)):
            if match in self.names and match != owner:
                self.rows[match].append((cat, where, owner, test))

    def lisp(self, relative: str, source: str) -> None:
        test = is_test(relative)
        try:
            forms = ledger.Reader(source).top_level()
        except ledger.ReadError as exc:
            self.unreadable[relative] = str(exc)
            self.text(source, "string", relative, None, test)  # never lose a mention
            return
        for form, line in forms:
            self.form(form, None, f"{relative}:{line}", test)

    def form(self, form: object, owner: str | None, where: str, test: bool) -> None:
        """Attribute FORM's mentions to OWNER, or find the definitions inside it."""
        if owner is None and isinstance(form, list) and form and head(form) not in ("quote", "quasiquote"):
            if head(form) in callgraph.DEFINITION_HEADS and callgraph.definition_name(form):
                owner = callgraph.definition_name(form)
            else:
                for item in form:
                    self.form(item, None, where, test)
                return
        seen_symbols: set[str] = set()
        strings: list[str] = []
        walk(form, seen_symbols, strings)
        for symbol in seen_symbols:
            name = bare(symbol)
            if name in self.names and name != owner:
                self.rows[name].append(("lisp", where, owner, test))
        for literal in strings:
            self.text(literal, "string", where, owner, test)


def walk(form: object, symbols: set[str], strings: list[str]) -> None:
    stack = [form]
    while stack:
        item = stack.pop()
        if isinstance(item, Sym):
            symbols.add(str(item))
        elif isinstance(item, str):
            strings.append(item)
        elif isinstance(item, list):
            stack.extend(item)


def subjects(root: Path, files: list[str]) -> dict[str, list[callgraph.Definition]]:
    found: dict[str, list[callgraph.Definition]] = {}
    for relative in files:
        if not (relative.startswith(HOST_PREFIXES) and relative.endswith(LISP_SUFFIXES)):
            continue
        path = root / relative
        definitions, _error = callgraph.read_file(path, relative, records=False)
        for d in definitions:
            found.setdefault(d.name, []).append(d)
    return found


def table(root: Path = ROOT, files: list[str] | None = None) -> tuple[list[dict], dict[str, str]]:
    """(one row per host definition, unreadable Lisp files) over ROOT's FILES
    (repository-relative; default: every tracked file)."""
    files = tracked(root) if files is None else files
    subject = subjects(root, files)
    names = set(subject)
    mentions = Mentions(names)
    for relative in files:
        path = root / relative
        if relative.startswith("build/"):
            continue
        try:
            data = path.read_bytes()
        except OSError:
            continue
        if b"\0" in data[:4096]:
            continue
        text = data.decode("utf-8", errors="replace")
        if relative.endswith(LISP_SUFFIXES) and not relative.startswith("planning/evidence/"):
            mentions.lisp(relative, text)
            continue
        cat = category(relative)
        if cat:
            mentions.text(text, cat, relative, None, is_test(relative))

    edges: dict[str, set[str]] = collections.defaultdict(set)  # owner -> subjects it mentions
    live_roots: set[str] = set()
    test_roots: set[str] = set()
    for name, rows in mentions.rows.items():
        for cat, where, owner, test in rows:
            if cat == "doc":
                continue
            host_owner = (owner in names and where.startswith(HOST_PREFIXES))
            if host_owner:
                edges[owner].add(name)
            elif test:
                test_roots.add(name)
            else:
                live_roots.add(name)

    def closure(start: set[str]) -> set[str]:
        seen, frontier = set(start), list(start)
        while frontier:
            one = frontier.pop()
            for other in edges.get(one, ()):
                if other not in seen:
                    seen.add(other)
                    frontier.append(other)
        return seen

    # A raw definition of an executable counterpart (`acl2_*1*_acl2::fn-x',
    # host/native/extent.lisp) replaces what ACL2 runs for fn-x: it is called
    # whenever fn-x is, and ACL2 is its caller.
    live_roots |= {n for n in names if n.startswith("acl2_*1*_")}
    called = closure(live_roots)
    test_only = closure(test_roots) - called
    result = []
    for name in sorted(names):
        rows = mentions.rows.get(name, [])
        counts = collections.Counter(cat for cat, *_ in rows)
        callers = sorted({(owner or "<top-level>") + " @ " + where
                          for cat, where, owner, _t in rows if cat != "doc"})
        docs = sorted({where for cat, where, *_ in rows if cat == "doc"})
        status = "called" if name in called else "test-only" if name in test_only else "zero"
        first = subject[name][0]
        result.append({
            "name": name, "kind": first.kind, "path": first.path, "line": first.line,
            "definitions": len(subject[name]), "status": status,
            "cluster": status == "zero" and bool(callers),
            "lisp": counts["lisp"], "string": counts["string"], "script": counts["script"],
            "registry": counts["registry"], "doc": counts["doc"],
            "callers": callers, "docs": docs,
        })
    return result, mentions.unreadable


def row_line(row: dict) -> str:
    status = row["status"] + (" (cluster)" if row["cluster"] else "")
    return ("{name:<48} {kind:<8} {status:<16} lisp={lisp} string={string} script={script} "
            "registry={registry} doc={doc}  {path}:{line}").format(**{**row, "status": status})


def load_baseline() -> dict[str, str]:
    try:
        return json.loads(BASELINE.read_text())["uncalled"]
    except (OSError, ValueError, KeyError):
        return {}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--status", choices=("called", "test-only", "zero"))
    parser.add_argument("--name", help="one subject, with every caller and doc mention")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--check", action="store_true",
                        help="warn (exit 0) on zero-caller definitions outside the baseline")
    arguments = parser.parse_args(argv)
    rows, unreadable = table()
    for relative, error in sorted(unreadable.items()):
        print(f"host_callers: {relative}: unreadable, scanned as text: {error}", file=sys.stderr)
    counts = collections.Counter(r["status"] for r in rows)
    summary = "host_callers: {} host definition(s): {} called, {} test-only, {} zero".format(
        len(rows), counts["called"], counts["test-only"], counts["zero"])
    if arguments.check:
        baseline = load_baseline()
        new = [r for r in rows if r["status"] == "zero" and r["name"] not in baseline]
        stale = sorted(n for n in baseline if n not in {r["name"] for r in rows if r["status"] == "zero"})
        for row in new:
            print("host_callers: WARN no caller: " + row_line(row))
        for name in stale:
            print(f"host_callers: WARN baseline entry {name} is no longer an uncalled host definition: remove it")
        print(summary + f"; {len(new)} not in the baseline (warn-only)")
        return 0
    if arguments.name:
        rows = [r for r in rows if r["name"] == arguments.name.lower()]
        if not rows:
            print(f"host_callers: {arguments.name}: not a host definition", file=sys.stderr)
            return 2
    if arguments.status:
        rows = [r for r in rows if r["status"] == arguments.status]
    if arguments.json:
        print(json.dumps({"summary": dict(counts), "rows": rows}, indent=1))
        return 0
    for row in rows:
        print(row_line(row))
        if arguments.name:
            for caller in row["callers"]:
                print("    caller " + caller)
            for doc in row["docs"]:
                print("    doc    " + doc)
    print(summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
