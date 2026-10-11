#!/usr/bin/env python3
"""The shrink line: what a train adds to or removes from the tree it ships.

One line per train (printed by `tools/train.py push` and `status`): the book
count and the executable book lines at HEAD, their change against the fork
point, and the net changed lines per top directory from `git diff --numstat`.

Executable (the method of build/coordinator/ANATOMY-20261009.md): the
transitive call closure, over book definitions (books/*.lisp), of every book
function the host names -- any symbol in host/*.lisp or host/native/*.lisp,
quoted or not, that a book defines.  Its lines are the source lines of those
defining forms.  The measure is static and errs upward: a host symbol that
names a book function counts that function reached.  Sources are read from
git blobs (never a checkout) with tools/ledger.py's non-evaluating Reader, and
each revision's measure is cached under build/cache/shrink-line by the tree
ids of books/ and host/, so the fork point is read once.

    python3 tools/shrink_line.py                     # HEAD against origin/dev
    python3 tools/shrink_line.py --base REV --head REV
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402

DEFINING = {"defun", "defund", "defun-inline", "defund-inline", "defun-nx",
            "defund-nx", "def-loop"}
CACHE = Path("build/cache/shrink-line")
FORMAT = 2


def git(root: Path, *args: str, data: bytes | None = None) -> bytes:
    return subprocess.run(["git", "-C", str(root), *args], input=data,
                          capture_output=True, check=True).stdout


def blobs(root: Path, rev: str) -> dict[str, str]:
    """{path: text} for books/*.lisp, host/*.lisp and host/native/*.lisp at REV."""
    listing = git(root, "ls-tree", "-r", rev, "--", "books", "host").decode()
    wanted = []
    for row in listing.splitlines():
        meta, path = row.split("\t", 1)
        parts = path.split("/")
        if not path.endswith(".lisp") or meta.split()[1] != "blob":
            continue
        if (parts[0] == "books" and len(parts) == 2) or \
                (parts[0] == "host" and (len(parts) == 2 or (len(parts) == 3 and parts[1] == "native"))):
            wanted.append((path, meta.split()[2]))
    out = git(root, "cat-file", "--batch", data="".join(f"{sha}\n" for _, sha in wanted).encode())
    texts, at = {}, 0
    for path, _ in wanted:
        header_end = out.index(b"\n", at)
        size = int(out[at:header_end].split()[2])
        start = header_end + 1
        texts[path] = out[start:start + size].decode("utf-8", errors="replace")
        at = start + size + 1
    return texts


def forms_with_spans(text: str) -> list[tuple[object, int, int, int]]:
    """Every top-level form with its first and last source line and its
    offset."""
    reader, found = ledger.Reader(text), []
    while True:
        reader.skip_space()
        if reader.pos >= len(text):
            return found
        at = reader.pos
        first = reader.line(at)
        form = reader.form()
        found.append((form, first, reader.line(reader.pos - 1), at))


def nested_span(text: str, start: int, form: list) -> int:
    """The source lines of FORM, a definition nested in the top-level form
    at START: found by its head and name, then read alone."""
    needle = f"({ledger.head(form)} {form[1]}".lower()
    at = text.lower().find(needle, start)
    if at < 0:
        return 0
    reader = ledger.Reader(text)
    reader.pos = at
    reader.form()
    return reader.line(reader.pos - 1) - reader.line(at) + 1


def symbols(form: object, found: set[str]) -> set[str]:
    """Every symbol in FORM, quoted ones included (the host calls books by name)."""
    stack = [form]
    while stack:
        item = stack.pop()
        if isinstance(item, list):
            stack.extend(item)
        elif isinstance(item, ledger.Sym):
            found.add(str(item).lower())
    return found


def definitions(form: object) -> list:
    """FORM's defining forms: itself, or the non-local ones an encapsulate or
    progn carries (a local definition does not outlive its book)."""
    if not isinstance(form, list) or not form:
        return []
    h = ledger.head(form)
    if h in DEFINING or h == "defabsstobj":
        return [form]
    if h == "progn":
        return [d for item in form[1:] for d in definitions(item)]
    if h == "encapsulate":
        return [d for item in form[2:] for d in definitions(item)]
    return []


def define(defs: dict, form: list, lines: int) -> None:
    """Enter FORM's names with its LINES.  A defun-inline also answers to
    NAME$inline; a defabsstobj export NAME is an edge, of no lines of its
    own, to its :exec and :logic functions."""
    h = ledger.head(form)
    if h == "defabsstobj":
        for item in form[2:]:
            if isinstance(item, list):
                for export in item:
                    if isinstance(export, list) and export and isinstance(export[0], ledger.Sym):
                        targets = {str(x).lower() for x in export[1:] if isinstance(x, ledger.Sym)
                                   and not str(x).startswith(":")}
                        defs.setdefault(str(export[0]).lower(), (0, targets))
        return
    if len(form) < 2 or not isinstance(form[1], ledger.Sym):
        return
    name = str(form[1]).lower()
    entry = (lines, {c.lower() for c in ledger.calls(form)})
    defs[name] = entry
    if h in ("defun-inline", "defund-inline"):
        defs[name + "$inline"] = (0, {name})


def measure_texts(texts: dict[str, str]) -> dict:
    """{books, functions, executable_functions, executable_lines} of one tree."""
    defs: dict[str, tuple[int, set[str]]] = {}
    named: set[str] = set()
    books = 0
    for path, text in texts.items():
        try:
            forms = forms_with_spans(text)
        except ledger.ReadError as error:
            raise SystemExit(f"shrink_line: {path}: unreadable: {error}")
        if path.startswith("books/"):
            books += 1
            for form, first, last, at in forms:
                for inner in definitions(form):
                    define(defs, inner, last - first + 1 if inner is form
                           else nested_span(text, at, inner))
        else:
            for form, _, _, _ in forms:
                symbols(form, named)
    reached = set(named) & set(defs)
    stack = list(reached)
    while stack:
        for callee in defs[stack.pop()][1]:
            if callee in defs and callee not in reached:
                reached.add(callee)
                stack.append(callee)
    return {"books": books, "functions": len(defs), "executable_functions": len(reached),
            "executable_lines": sum(defs[name][0] for name in reached)}


def measure(root: Path, rev: str) -> dict:
    key = "-".join(git(root, "rev-parse", f"{rev}:{part}").decode().strip()[:16]
                   for part in ("books", "host"))
    cache = root / CACHE / f"{FORMAT}-{key}.json"
    if cache.is_file():
        return json.loads(cache.read_text(encoding="utf-8"))
    result = measure_texts(blobs(root, rev))
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps(result, sort_keys=True) + "\n", encoding="utf-8")
    return result


def numstat(root: Path, base: str, head: str) -> dict[str, int]:
    """Net changed lines (added - deleted) per top directory, BASE..HEAD."""
    net: dict[str, int] = {}
    for row in git(root, "diff", "--numstat", f"{base}..{head}").decode().splitlines():
        added, deleted, path = row.split("\t", 2)
        if added == "-":
            continue  # binary
        top = path.split("/", 1)[0] if "/" in path else "."
        net[top] = net.get(top, 0) + int(added) - int(deleted)
    return net


def signed(n: int) -> str:
    return f"{n:+,}"


def line(root: Path, base: str, head: str) -> str:
    before, after = measure(root, base), measure(root, head)
    net = numstat(root, base, head)
    dirs = " ".join(f"{d} {signed(net[d])}" for d in ("books", "host", "tools", "tests") if d in net)
    other = sum(v for d, v in net.items() if d not in ("books", "host", "tools", "tests"))
    if other:
        dirs += f" other {signed(other)}"
    return (f"shrink vs {git(root, 'rev-parse', '--short=9', base).decode().strip()}: "
            f"books {after['books']:,} ({signed(after['books'] - before['books'])}), "
            f"executable {after['executable_lines']:,} lines "
            f"({signed(after['executable_lines'] - before['executable_lines'])}) in "
            f"{after['executable_functions']:,} functions "
            f"({signed(after['executable_functions'] - before['executable_functions'])}); "
            f"net lines {dirs or 'none'}")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base", default="origin/dev")
    ap.add_argument("--head", default="HEAD")
    ap.add_argument("--root", default=str(Path(__file__).resolve().parents[1]))
    args = ap.parse_args(argv)
    print(line(Path(args.root), args.base, args.head))
    return 0


if __name__ == "__main__":
    sys.exit(main())
