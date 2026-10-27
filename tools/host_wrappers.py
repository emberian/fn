#!/usr/bin/env python3
"""The host's one-call wrappers, read from the source and sorted by what each is for.

A *thin* host defun has a body that is a single call (after its docstring and
declare forms).  Every thin defun of host/ is exactly one of

  kept       a definterface row declares it, or something outside host/ names it
             (a test, a tool, a document): it is a seam the tree depends on
  emitted    an exact alias of a BOOK function (same arguments, same order) in an
             ACL2-mode host file: tools/interface_entries.py generates it
  inlined    an exact alias of another HOST function, named only by host code:
             its callers name the callee and it is deleted
  unwired    nothing names it: deleted

The classes are computed from the call closure over the tracked tree, never listed
by hand.  `--check` fails when a host file holds a thin defun that is inlined or
unwired (a deleted wrapper does not grow back) or an emitted alias that still sits in
its host file.

    python3 tools/host_wrappers.py            # report
    python3 tools/host_wrappers.py --check
    python3 tools/host_wrappers.py --write    # delete unwired, inline host->host, in place
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

TOKEN = re.compile(r"[^\s()'`,\"|;]+")
CODE_SUFFIX = (".lisp", ".py", ".sh", ".c", ".json", ".mk", ".acl2", ".lsp", ".cert")
# Trees whose mention of a name is history or prose, not use.
PROSE = ("planning/", "third_party/", "build/", ".spw/", "docs/", "specs/", "site/",
         "swarmguide/", "packaging/")
PROSE_SUFFIX = (".md", ".txt", ".html")


def blank(text: str) -> str:
    """TEXT with comments, strings, character literals and |symbols| replaced by
    spaces of the same length, so offsets and line numbers survive."""
    out = list(text)
    i, n = 0, len(text)

    def wipe(a: int, b: int) -> None:
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = text[i]
        if c == ";":
            j = text.find("\n", i)
            j = n if j < 0 else j
            wipe(i, j)
            i = j
        elif c == "#" and text.startswith("#|", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("#|", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("|#", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            wipe(i, j)
            i = j
        elif c == "#" and text.startswith("#\\", i):
            j = i + 3
            while j < n and (text[j].isalnum() or text[j] in "-_") and text[i + 2].isalnum():
                j += 1
            wipe(i, j)
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            wipe(i, j + 1)
            i = j + 1
        elif c == "|":
            j = text.find("|", i + 1)
            j = n - 1 if j < 0 else j
            wipe(i, j + 1)
            i = j + 1
        else:
            i += 1
    return "".join(out)


def children(blanked: str, start: int, end: int) -> list[tuple[int, int]]:
    """Spans of the elements of the list at [START, END) (parens included)."""
    spans, i, depth, atom = [], start + 1, 0, None
    stop = end - 1
    while i < stop:
        c = blanked[i]
        if depth == 0 and atom is not None and (c.isspace() or c in "()"):
            spans.append((atom, i))
            atom = None
        if c == "(":
            if depth == 0:
                lst = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                spans.append((lst, i + 1))
        elif depth == 0 and not c.isspace() and atom is None:
            atom = i
        i += 1
    if atom is not None:
        spans.append((atom, stop))
    return spans


def top_forms(blanked: str) -> list[tuple[int, int]]:
    spans, depth, start = [], 0, 0
    for i, c in enumerate(blanked):
        if c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")" and depth:
            depth -= 1
            if depth == 0:
                spans.append((start, i + 1))
    return spans


@dataclass
class Thin:
    file: str
    name: str
    start: int
    end: int
    formals: list[str]
    callee: str
    args: list[str]
    exact: bool
    prefix: list[str]  # declare forms and docstring, source text


def thin_defuns(rel: str, text: str) -> list[Thin]:
    blanked = blank(text)
    found = []
    for start, end in top_forms(blanked):
        kids = children(blanked, start, end)
        if len(kids) < 4 or blanked[kids[0][0]:kids[0][1]].lower() != "defun":
            continue
        name = text[kids[1][0]:kids[1][1]].lower()
        fa, fb = kids[2]
        if blanked[fa] != "(":
            continue
        formals = [text[a:b].lower() for a, b in children(blanked, fa, fb)]
        body = kids[3:]
        prefix = []
        # a docstring is blank in BLANKED, so it is simply not a child; recover it
        # from the gap between the formals and the first child
        gap = text[fb:body[0][0]] if body else ""
        for m in re.finditer(r'"(?:[^"\\]|\\.)*"', gap):
            prefix.append(m.group(0))
        while body and blanked[body[0][0]:body[0][1]].lower().startswith("(declare"):
            prefix.append(text[body[0][0]:body[0][1]])
            body = body[1:]
        if len(body) != 1 or blanked[body[0][0]] != "(":
            continue
        # a docstring between declares, or after them, is not a plain prefix
        if '"' in text[body[0][1]:end - 1]:
            continue
        call = children(blanked, *body[0])
        if not call or blanked[call[0][0]] == "(":
            continue
        callee = text[call[0][0]:call[0][1]].lower()
        if not re.match(r"(fnn?-|create-fn-|values$|list$)", callee):
            continue
        if any(blanked[a] == "(" or ":" in text[a:a + 6] for a, _ in call[1:]):
            continue
        args = [text[a:b].lower() for a, b in call[1:]]
        has_text_arg = '"' in text[body[0][0]:body[0][1]] or "#\\" in text[body[0][0]:body[0][1]]
        exact = (args == formals and not has_text_arg
                 and not any(f.startswith("&") for f in formals)
                 and "#'" not in text[body[0][0]:body[0][1]])
        found.append(Thin(rel, name, start, end, formals, callee, args, exact, prefix))
    return found


def tracked_files(root: Path) -> list[str]:
    out = subprocess.run(["git", "ls-files"], cwd=root, capture_output=True, text=True,
                         check=True).stdout.split("\n")
    seen = [f for f in out if f and (root / f).is_file()]
    # files the worktree holds that git does not yet (a generated book)
    return seen


def host_lisp(root: Path) -> list[str]:
    return sorted(f for f in tracked_files(root) if f.startswith("host/") and f.endswith(".lisp"))


def mentions(root: Path, names: set[str]) -> dict[str, dict[str, int]]:
    """name -> {file: occurrences} over the tracked code (comments stripped from Lisp)."""
    table: dict[str, dict[str, int]] = {}
    for rel in tracked_files(root):
        if rel.endswith(PROSE_SUFFIX) or rel.startswith(PROSE):
            continue
        if not (rel.endswith(CODE_SUFFIX) or rel == "Makefile"):
            continue
        try:
            text = (root / rel).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if rel.endswith((".lisp", ".lsp", ".acl2")):
            text = _blank_comments(text)
        for m in TOKEN.finditer(text.lower()):
            word = m.group(0)
            if word in names:
                table.setdefault(word, {})
                table[word][rel] = table[word].get(rel, 0) + 1
    return table


def _blank_comments(text: str) -> str:
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif c == "#" and text.startswith("#\\", i):
            i += 3
        elif c == "#" and text.startswith("#|", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("#|", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("|#", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif c == ";":
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


@dataclass
class Census:
    thin: list[Thin]
    declared: set[str]
    host_defs: dict[str, str]
    refs: dict[str, dict[str, int]]


def declared_names(root: Path) -> set[str]:
    names = set()
    for rel in host_lisp(root):
        text = _blank_comments((root / rel).read_text(encoding="utf-8", errors="replace"))
        names.update(m.group(1).lower() for m in re.finditer(r"\(definterface\s+([^\s()]+)", text))
    return names


def census(root: Path = ROOT) -> Census:
    thin, host_defs = [], {}
    for rel in host_lisp(root):
        text = (root / rel).read_text(encoding="utf-8", errors="replace")
        thin.extend(thin_defuns(rel, text))
        for m in re.finditer(r"(?m)^\((?:defun|defmacro|defstruct|defgeneric|defvar|defparameter)\s+\(?([^\s()]+)",
                             blank(text)):
            host_defs.setdefault(m.group(1).lower(), rel)
    names = {t.name for t in thin}
    return Census(thin, declared_names(root), host_defs, mentions(root, names))


FUNCTION_HEADS = ("defun", "defund", "defun-inline", "defund-inline", "defun-notinline",
                  "defun-nx", "defund-nx", "defmacro", "defstobj", "defabsstobj", "define",
                  "defun-sk", "defabbrev", "defconst", "defund-notinline", "defmacro-last")
DEF = re.compile(r"(?m)^\(\s*(" + "|".join(map(re.escape, FUNCTION_HEADS)) + r")\s+\(?([^\s()]+)",
                 re.I)


def book_index(root: Path) -> dict[str, list[str]]:
    """name -> the books/*.lisp files that define it (functions, macros, stobjs)."""
    index: dict[str, list[str]] = {}
    for path in sorted((root / "books").glob("*.lisp")):
        text = _blank_comments(path.read_text(encoding="utf-8", errors="replace"))
        rel = path.relative_to(root).as_posix()
        for m in DEF.finditer(text):
            books = index.setdefault(m.group(2).lower(), [])
            if rel not in books:
                books.append(rel)
    return index


def defining_book(index: dict[str, list[str]], token: str) -> str | None:
    books = index.get(token)
    return books[0] if books else None


INCLUDE = re.compile(r'(?m)^\(include-book\s+"([^"]+)"[^)\n]*\)')


def closure_before(root: Path, rel: str, text: str, limit: int) -> set[str]:
    """The non-local include closure of the include-books at top level of REL before
    offset LIMIT (and REL itself)."""
    import os
    from tools import interfaces_relocate
    stub = []
    for m in INCLUDE.finditer(_blank_comments(text)):
        if m.start() >= limit:
            break
        stub.append(os.path.normpath(os.path.join(os.path.dirname(rel), m.group(1) + ".lisp")))
    return interfaces_relocate.include_closure(root, stub)


def acl2_mode(rel: str, text: str) -> bool:
    """A top-level host/*.lisp ACL2 file with no :program section."""
    code = blank(text)
    return (rel.count("/") == 1 and '(in-package "ACL2")' in text
            and not re.search(r"(?m)^\(program\)", code))


# Held for the M2 branch that rewrites the extent arms (Route A): not touched here.
HELD = ("host/native/extent.lisp",)


def _norm(text: str) -> str:
    return re.sub(r"\s+", " ", text).replace("( ", "(").replace(" )", ")").lower()


def rebuilt(t: Thin) -> str:
    """The defun a row generates (tools/interface_entries.py render), as one string."""
    args = " ".join(t.formals)
    return "(defun {} ({}) {} ({}{}))".format(
        t.name, args, " ".join(t.prefix), t.callee, " " + args if args else "")


@dataclass
class Plan:
    adopt: dict[str, list[Thin]]
    unwired: list[Thin]
    inlined: list[Thin]
    skipped: dict[str, int]


def make_plan(root: Path, c: Census | None = None) -> Plan:
    c = c or census(root)
    index = book_index(root)
    texts = {rel: (root / rel).read_text(encoding="utf-8") for rel in host_lisp(root)}
    skipped: dict[str, int] = {}

    def skip(reason: str) -> None:
        skipped[reason] = skipped.get(reason, 0) + 1

    adopt: dict[str, list[Thin]] = {}
    unwired, inlined = [], []
    for t in c.thin:
        if t.file in HELD or "*1*" in t.name:
            skip("held")
            continue
        uses = dict(c.refs.get(t.name, {}))
        uses[t.file] = uses.get(t.file, 0) - 1 - (1 if t.name in c.declared else 0)
        uses = {f: n for f, n in uses.items() if n > 0}
        declared = t.name in c.declared
        if not declared and not uses:
            unwired.append(t)
            continue
        if not declared and t.exact and t.callee in c.host_defs and t.callee != t.name \
                and all(f.startswith("host/native/") for f in uses):
            # a quoted name is dispatched by name (an interface entry): never renamed
            quoted = re.compile(r"(?<!#)'" + re.escape(t.name) + r"(?![^\s()])", re.I)
            if any(quoted.search(texts[f]) for f in uses):
                skip("named by a quoted dispatch")
                continue
            inlined.append(t)
            continue
        text = texts[t.file]
        if _blank_comments(text[t.start:t.end]) != text[t.start:t.end]:
            skip("a comment inside the defun")
            continue
        if t.exact and _norm(text[t.start:t.end]) != _norm(rebuilt(t)):
            skip("not reproduced by its row")
            continue
        if not (t.exact and acl2_mode(t.file, text) and t.callee in index
                and t.callee not in c.host_defs and t.callee != t.name):
            skip("not an exact book alias in an ACL2-mode host file")
            continue
        names = set(TOKEN.findall(blank(" ".join(t.prefix)).lower())) - set(t.formals)
        if any(n in c.host_defs and n != t.name for n in names):
            skip("prefix names a host function")
            continue
        adopt.setdefault(t.file, []).append(t)
    # an alias is emitted only if every book it needs is already in the host file's
    # include closure at the point the first emitted alias used to sit
    for rel in list(adopt):
        rows = adopt[rel]
        while rows:
            first = min(t.start for t in rows)
            held = closure_before(root, rel, texts[rel], first)
            keep = []
            for t in rows:
                tokens = set(TOKEN.findall(blank(" ".join([t.callee, *t.prefix])).lower())) \
                    - set(t.formals) - {t.name}
                books = [defining_book(index, tok) for tok in sorted(tokens)]
                if all(b is None or b in held for b in books):
                    keep.append(t)
                else:
                    skip("book not included before the first alias")
            if len(keep) == len(rows):
                break
            rows = keep
        if rows:
            adopt[rel] = rows
        else:
            del adopt[rel]
    return Plan(adopt, unwired, inlined, skipped)


def _line_span(text: str, start: int, end: int, comments: bool) -> tuple[int, int]:
    """START..END widened over its whole lines, the comment lines directly above (when
    COMMENTS) and one blank line, so a deletion leaves no double blank."""
    a = text.rfind("\n", 0, start) + 1
    if text[a:start].strip():
        return start, end
    if comments:
        while a > 0:
            prev = text.rfind("\n", 0, a - 1) + 1
            if text[prev:a - 1].lstrip().startswith(";"):
                a = prev
            else:
                break
    b = text.find("\n", end)
    b = len(text) if b < 0 else b + 1
    if text[end:b].strip():
        return start, end
    before_blank = a == 0 or text[text.rfind("\n", 0, a - 1) + 1:a - 1].strip() == ""
    after_blank = b < len(text) and text[b:text.find("\n", b) if text.find("\n", b) >= 0 else len(text)].strip() == ""
    if before_blank and after_blank:
        b = text.find("\n", b) + 1
    return a, b


def apply(root: Path, plan: Plan) -> dict[str, str]:
    """The new text of every host file the plan touches."""
    from tools import interface_entries
    edits: dict[str, list[tuple[int, int, str]]] = {}
    table = interface_entries.load_table(root)
    for rel, rows in plan.adopt.items():
        table[rel] = [[t.name, "(" + " ".join(t.formals) + ")", t.prefix, t.callee]
                      for t in sorted(rows, key=lambda t: t.start)]
        ordered = sorted(rows, key=lambda t: t.start)
        for k, t in enumerate(ordered):
            if k == 0:
                edits.setdefault(rel, []).append((t.start, t.end, interface_entries.include_form(rel)))
            else:
                edits.setdefault(rel, []).append((t.start, t.end, ""))
    interface_entries.save_table(table, root)
    dead = {t.start: t for t in plan.unwired + plan.inlined}
    for t in plan.unwired + plan.inlined:
        edits.setdefault(t.file, []).append((t.start, t.end, ""))
    renames = {t.name: t.callee for t in plan.inlined}
    out: dict[str, str] = {}
    files = set(edits)
    if renames:
        files |= set(host_lisp(root))
    for rel in sorted(files):
        text = (root / rel).read_text(encoding="utf-8")
        for start, end, replacement in sorted(edits.get(rel, []), reverse=True):
            comments = replacement == ""
            if replacement == "":
                a, b = _line_span(text, start, end, comments=_is_deletion_of_unwired(plan, rel, start))
                text = text[:a] + text[b:]
            else:
                text = text[:start] + replacement + text[end:]
        if renames:
            pattern = re.compile(r"(?<![^\s()'`,#])(" + "|".join(map(re.escape, renames)) + r")(?![^\s()'`,\"])",
                                 re.I)
            text = pattern.sub(lambda m: renames[m.group(1).lower()], text)
        if text != (root / rel).read_text(encoding="utf-8"):
            out[rel] = text
    return out


def _is_deletion_of_unwired(plan: Plan, rel: str, start: int) -> bool:
    return any(t.file == rel and t.start == start for t in plan.unwired + plan.inlined)


def findings(root: Path = ROOT) -> list[str]:
    plan = make_plan(root)
    out = []
    for t in plan.unwired:
        out.append("{} defines {}, which nothing names; delete it".format(t.file, t.name))
    for t in plan.inlined:
        out.append("{} defines {}, an alias of host function {}; name {} instead".format(
            t.file, t.name, t.callee, t.callee))
    for rel, rows in sorted(plan.adopt.items()):
        for t in rows:
            out.append("{} defines {}, an exact alias of book function {}; "
                       "tools/interface_entries.py emits it".format(rel, t.name, t.callee))
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--root", default=str(ROOT))
    args = ap.parse_args(argv)
    root = Path(args.root)
    plan = make_plan(root)
    lines = lambda ts: sum((root / t.file).read_text().count("\n", t.start, t.end) + 1 for t in ts)
    adopted = [t for rows in plan.adopt.values() for t in rows]
    print("emit     {:4d} defuns {:5d} lines in {} host files".format(
        len(adopted), lines(adopted), len(plan.adopt)))
    print("unwired  {:4d} defuns {:5d} lines".format(len(plan.unwired), lines(plan.unwired)))
    print("inlined  {:4d} defuns {:5d} lines".format(len(plan.inlined), lines(plan.inlined)))
    for reason, n in sorted(plan.skipped.items()):
        print("kept     {:4d} {}".format(n, reason))
    if args.write:
        from tools import interface_entries
        for rel, text in apply(root, plan).items():
            (root / rel).write_text(text, encoding="utf-8")
        for rel in interface_entries.write(root):
            print("wrote", rel)
    if args.check:
        found = findings(root)
        for line in found:
            print(line)
        return 1 if found else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
