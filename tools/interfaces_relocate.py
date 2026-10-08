#!/usr/bin/env python3
"""tools/interfaces_relocate.py -- declare each host entry where it is defined (ruling 18, option B).

host/interfaces.lisp declared every host-called entry, so it could not certify
without the host files that define most of them.  This tool moves each
`definterface` (with the comment lines directly above it) out of
host/interfaces.lisp to just after the form that completes its entry's
definition in the host file that defines it; host/interfaces.lisp keeps the
book-defined entries and certifies over books alone.

PLACEMENT.  A definterface checks its entry against the world when the host
file is loaded (books/definterface.lisp fn-di-problem), so it goes AFTER the
last top-level form of that file that the check needs: the entry's definition
(`defun'/`mutual-recursion'/...), a `verify-guards' of it (its symbol class),
and every symbol the declaration names (:keystones, :delegates, :raw-with,
:operation, :raw-guarded) that the same file defines.  A named symbol defined
in a host file loaded LATER than the entry's moves the declaration to that
later file (the latest-loaded one it needs), after the symbol.  A symbol a book defines is in the image world already (books/image-world).

A FORM IS LEFT IN host/interfaces.lisp, with its reason printed, when it is
  book-defined       the entry is defined in books/ and its declaration names no
                     host-defined symbol (the file's purpose)
  no-definition      no top-level def form in host/ or books/ names it (a
                     macro or a stobj generates it: the tool does not expand)
  several-hosts      defined in more than one host file
  host-and-book      defined in both
  not-loaded         its host file, or a host file defining a symbol it names, is neither
                     ld'd by host/native/build.lisp nor include-book'd (a host book is
                     taken as loaded before every ld'd file)
  no-in-package      its host file does not open with (in-package "ACL2")
  not-at-line-start  the form shares a line with something else
  guards-elsewhere   the entry's verify-guards is in another file
  certified-book     the target host file is include-book'd (a certified book, not just ld'd)
  not-in-image       a symbol it names is in a book an image that loads the target
                     file (build.lisp, build-dtn.lisp) does not include
Only book-defined is expected; the rest is the residual to work.

    python3 tools/interfaces_relocate.py            # report, change nothing
    python3 tools/interfaces_relocate.py --write    # rewrite the files in place
    python3 tools/interfaces_relocate.py --root DIR # another tree (the tests')
"""
from __future__ import annotations

import argparse
import collections
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lisp_rewrite as lr  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SOURCE = "host/interfaces.lisp"
BUILD = "host/native/build.lisp"
FUNCTION_HEADS = {"defun", "defund", "defun-nx", "defund-nx", "defun-inline", "defund-inline",
                  "defun-notinline", "defun-sk", "define", "defstub", "defabbrev"}
# Forms that annotate or check a function a book defines; they do not define it.
NOT_DEFINITIONS = {"def-cost", "def-cost-check", "def-operation-check"}
WRAPPERS = {"progn", "mutual-recursion", "encapsulate", "progn!", "with-output"}
DEPENDENT_KEYS = {":keystones", ":delegates", ":raw-with", ":operation", ":raw-guarded"}


LD = re.compile(r'^\(ld "(host/[^"]+\.lisp)"', re.M)


def load_order(root: Path, build: str = BUILD) -> dict[str, int]:
    """host file -> position among a build file's `(ld "host/...lisp"' lines (an ld'd
    ACL2 file under host/native/, such as reader-model-host, counts like one in host/)."""
    text = (root / build).read_text(encoding="utf-8")
    order: dict[str, int] = {}
    for m in LD.finditer(text):
        order.setdefault(m.group(1), len(order))
    return order


def host_files(root: Path) -> list[str]:
    """The host files that can define or declare an entry: host/*.lisp and every file a
    build file (host/native/build.lisp, build-dtn.lisp) ld's from a subdirectory of host/."""
    found = {p.relative_to(root).as_posix() for p in (root / "host").glob("*.lisp")}
    for build_rel in (BUILD, "host/native/build-dtn.lisp"):
        if (root / build_rel).is_file():
            found |= {rel for rel in load_order(root, build_rel) if (root / rel).is_file()}
    return sorted(found)


INCLUDE = re.compile(r'^[ \t]*\(include-book\s+"([^"]+)"([^)\n]*)', re.M)


def image_books(root: Path, build_rel: str) -> set[str] | None:
    """The books an image's world holds: the include closure of the build file and
    its ld'd host files; None when there is no such build file."""
    build = root / build_rel
    if not build.is_file():
        return None
    loaded = LD.findall(build.read_text(encoding="utf-8"))
    return include_closure(root, [build_rel, *loaded])


def included_files(root: Path) -> dict[str, str]:
    """host file -> a file that include-books it: such a host file is a certified
    book, whose world is its own include closure, not the image's."""
    found: dict[str, str] = {}
    for pattern in ("host/*.lisp", "books/*.lisp", "tests/acl2/*.lisp"):
        for path in sorted(root.glob(pattern)):
            text = re.sub(r"(?m);.*$", "", path.read_text(encoding="utf-8", errors="replace"))
            for target, _rest in INCLUDE.findall(text):
                rel = os.path.normpath((path.parent / (target + ".lisp")).relative_to(root)).replace(os.sep, "/")
                if rel.startswith("host/"):
                    found.setdefault(rel, path.relative_to(root).as_posix())
    return found


def include_closure(root: Path, rels) -> set[str]:
    """The non-local include-book closure (textual) of the given files."""
    stack, seen = list(rels), set()
    while stack:
        rel = stack.pop()
        if rel in seen:
            continue
        seen.add(rel)
        if not (root / rel).is_file():
            continue
        text = re.sub(r"\(local\s+\(include-book[^)]*\)\)", "",
                      re.sub(r"(?m);.*$", "", (root / rel).read_text(encoding="utf-8", errors="replace")))
        for target, rest in INCLUDE.findall(text):
            if ":dir" not in rest.lower():
                stack.append(os.path.normpath(os.path.join(os.path.dirname(rel), target + ".lisp")))
    return seen


class Index:
    """Where every top-level def and verify-guards is, in host_files and books/."""

    def __init__(self, root: Path):
        self.defs: dict[str, list[tuple[str, str, int]]] = collections.defaultdict(list)
        self.guards: dict[str, list[tuple[str, int]]] = collections.defaultdict(list)
        self.parsed: dict[str, lr.Parsed] = {}
        rels = host_files(root) + sorted(p.relative_to(root).as_posix() for p in (root / "books").glob("*.lisp"))
        for rel in rels:
            parsed = lr.parse(root / rel)
            self.parsed[rel] = parsed
            for top in parsed.forms:
                self._walk(rel, top, top.end)

    def _walk(self, rel, node, end):
        if not isinstance(node, lr.Lst) or len(node.items) < 2 or not isinstance(node.items[0], lr.Atom):
            return
        head = node.items[0].low
        if head in WRAPPERS:
            for item in node.items[1:]:
                self._walk(rel, item, end)
            return
        second = node.items[1]
        if not isinstance(second, lr.Atom) or head == "definterface":
            return
        if head == "verify-guards":
            self.guards[second.low].append((rel, end))
        elif (head.startswith("def") or head == "define") and head not in NOT_DEFINITIONS:
            self.defs[second.low].append((rel, head, end))


def attached_start(text: str, form_start: int) -> int | None:
    """Start of the comment lines directly above the form (no blank line between),
    or the form's own line start; None when the form shares its line."""
    line_start = text.rfind("\n", 0, form_start) + 1
    if text[line_start:form_start].strip():
        return None
    start = line_start
    while start > 0:
        prev_start = text.rfind("\n", 0, start - 1) + 1
        if not text[prev_start:start - 1].lstrip().startswith(";"):
            break
        start = prev_start
    return start


def named_symbols(form: lr.Lst) -> set[str]:
    """Symbols in the dependent keyword values of a definterface form."""
    out: set[str] = set()

    def atoms(node):
        if isinstance(node, lr.Atom) and not isinstance(node, lr.Str) and node.kind == "symbol":
            if not node.text.startswith(":"):
                out.add(node.low)
        elif isinstance(node, lr.Pre):
            atoms(node.node)
        elif isinstance(node, lr.Lst):
            for item in node.items:
                atoms(item)
    items = form.items[2:]
    for i, item in enumerate(items):
        if isinstance(item, lr.Atom) and item.low in DEPENDENT_KEYS and i + 1 < len(items):
            atoms(items[i + 1])
    return out


def plan(root: Path):
    """-> (moves, left): moves[file] = [(insert_at, order, text)]; left = [(name, reason, detail)];
    removals = [(start, end)] in host/interfaces.lisp."""
    order = load_order(root)
    index = Index(root)
    certified = included_files(root)
    closures: dict[str, set[str]] = {}
    images = {rel: image_books(root, rel) for rel in (BUILD, "host/native/build-dtn.lisp")}
    dtn_files = set(load_order(root, "host/native/build-dtn.lisp")) if images["host/native/build-dtn.lisp"] is not None else set()
    parsed = index.parsed[SOURCE]
    source = parsed.text
    moves: dict[str, list] = collections.defaultdict(list)
    removals: list[tuple[int, int]] = []
    left: list[tuple[str, str, str]] = []
    for n, form in enumerate(parsed.forms):
        if not (isinstance(form, lr.Lst) and isinstance(form.items[0], lr.Atom)
                and form.items[0].low == "definterface"):
            continue
        name = form.items[1].low
        defs = [d for d in index.defs.get(name, ()) if d[1] in FUNCTION_HEADS or d[1] == "defmacro"]
        hosts = sorted({d[0] for d in defs if d[0].startswith("host/")})
        books = sorted({d[0] for d in defs if d[0].startswith("books/")})
        if not defs:
            left.append((name, "no-definition", "")); continue
        if len(hosts) > 1:
            left.append((name, "several-hosts", " ".join(hosts))); continue
        # A book-defined entry stays here unless its declaration names a symbol
        # a host file defines (a :raw-with carried invariant, a keystone): the
        # books-only world of host/interfaces lacks it, so the declaration goes
        # after that symbol in its host file.
        named_hosts = {d[0] for s in named_symbols(form) for d in index.defs.get(s, ())
                       if d[0].startswith("host/")}
        if not hosts and not named_hosts:
            left.append((name, "book-defined", books[0] + ("+" if len(books) > 1 else ""))); continue
        if hosts and books:
            left.append((name, "host-and-book", hosts[0] + " " + " ".join(books))); continue
        if hosts and hosts[0] not in order and hosts[0] not in certified:
            left.append((name, "not-loaded", hosts[0])); continue
        guard_files = {g[0] for g in index.guards.get(name, ())}
        if hosts and guard_files - {hosts[0]}:
            left.append((name, "guards-elsewhere", " ".join(sorted(guard_files)))); continue
        start = attached_start(source, form.start)
        if start is None:
            left.append((name, "not-at-line-start", "")); continue
        # Everything the check needs must exist when it runs: the target is the
        # latest-loaded host file among the entry's and the files defining
        # symbols the declaration names, placed after the last such form in it.
        needs = ([(hosts[0], max(d[2] for d in defs))] + list(index.guards.get(name, ()))) if hosts else []
        bad = None
        for symbol in sorted(named_symbols(form)):
            for d_file, _head, d_end in index.defs.get(symbol, ()):
                if d_file.startswith("host/"):
                    if d_file not in order and d_file not in certified:
                        bad = ("not-loaded", f"{symbol} in {d_file}")
                    needs.append((d_file, d_end))
        if bad:
            left.append((name, *bad)); continue
        target = max((f for f, _ in needs), key=lambda f: order.get(f, -1))
        if target in certified:
            # Its world is its own include closure: every book a named symbol
            # comes from must be in it; books/definterface is added to the file.
            if target not in closures:
                closures[target] = include_closure(root, [target])
            held = closures[target]
            lacking = sorted({sorted(h)[0] for sym in named_symbols(form)
                              if (h := {d[0] for d in index.defs.get(sym, ()) if d[0].startswith("books/")})
                              and not h & held})
            if lacking:
                left.append((name, "certified-book", f"{target} (included by {certified[target]}) lacks {lacking[0]}")); continue
        # An image that loads the target file checks the declaration there, so
        # every book a named symbol comes from must be in that image's world.
        for build_rel, held in images.items():
            if held is None or target not in (order if build_rel == BUILD else dtn_files):
                continue
            for symbol in sorted(named_symbols(form)):
                homes = {d[0] for d in index.defs.get(symbol, ()) if d[0].startswith("books/")}
                if homes and not homes & held:
                    bad = ("not-in-image", f"{symbol} is in {sorted(homes)[0]}, not in {build_rel}'s world")
        if bad:
            left.append((name, *bad)); continue
        anchor = max(e for f, e in needs if f == target)
        first = index.parsed[target].forms[0] if index.parsed[target].forms else None
        if not (isinstance(first, lr.Lst) and isinstance(first.items[0], lr.Atom)
                and first.items[0].low == "in-package" and len(first.items) > 1
                and lr.flat(first.items[1]).strip('"').upper() == "ACL2"):
            left.append((name, "no-in-package", target)); continue
        text = index.parsed[target].text
        eol = text.find("\n", anchor)
        insert_at = len(text) if eol < 0 else eol
        end = form.end
        eol_src = source.find("\n", end)
        removals.append((start, len(source) if eol_src < 0 else eol_src + 1))
        moves[target].append((insert_at, n, source[start:end]))
    return moves, left, removals, index, source


def apply(root: Path, moves, removals, index, source):
    """-> {relative path: new text}."""
    out = {}
    for target, items in moves.items():
        text = index.parsed[target].text
        edits = []
        for at in sorted({m[0] for m in items}):
            group = sorted((m for m in items if m[0] == at), key=lambda m: m[1])
            edits.append((at, at, "".join("\n\n" + m[2] for m in group)))
        out[target] = lr.write(text, edits)
    out[SOURCE] = lr.write(source, [(a, b, "") for a, b in removals])
    return out


KINDS_BOOK = "books/payload-kinds.lisp"


def include_edits(root: Path) -> dict[str, str]:
    """For each file holding definterface forms and certified standalone (host/interfaces.lisp
    and every include-book'd host file), the include-books its world lacks for the forms it
    holds: books/definterface, books/payload-kinds when a form has :kinds (the host entry
    guard's kind table, *fn-entry-guard-kinds*), a book defining each entry and each
    symbol a declaration names, and a book verifying an entry's guards apart from its
    definition (the :class check reads the guard status).  Books already in the include closure are not added."""
    index = Index(root)
    certified = included_files(root)
    out = {}
    for rel in [SOURCE] + sorted(f for f in certified if f != SOURCE):
        parsed = index.parsed.get(rel)
        if parsed is None:
            continue
        forms = [f for f in parsed.forms if isinstance(f, lr.Lst) and isinstance(f.items[0], lr.Atom)
                 and f.items[0].low == "definterface"]
        if not forms:
            continue
        held = include_closure(root, [rel])
        want = ["books/definterface.lisp"]
        if any(isinstance(i, lr.Atom) and i.low == ":kinds" for f in forms for i in f.items):
            want.append(KINDS_BOOK)
        for f in forms:
            for sym in [f.items[1].low, *sorted(named_symbols(f))]:
                homes = sorted({d[0] for d in index.defs.get(sym, ()) if d[0].startswith("books/")})
                if homes and not set(homes) & held and not (set(homes) & set(want)):
                    want.append(homes[0])
            # The entry's :class is checked against its guard status, so a book
            # that verifies its guards apart from its definition is needed too.
            guards = sorted({g[0] for g in index.guards.get(f.items[1].low, ()) if g[0].startswith("books/")})
            if guards and not set(guards) & held and not (set(guards) & set(want)):
                want.append(guards[0])
        add = []
        for book in want:
            if book not in held:
                add.append(book)
                held |= include_closure(root, [book])
        if add:
            last = None
            for form in parsed.forms:
                if isinstance(form, lr.Lst) and isinstance(form.items[0], lr.Atom) \
                        and form.items[0].low in ("in-package", "include-book"):
                    last = form
                else:
                    break
            eol = parsed.text.find("\n", last.end)
            at = len(parsed.text) if eol < 0 else eol
            text = "".join('\n(include-book "../{}")'.format(b[:-5]) for b in add)
            out[rel] = lr.write(parsed.text, [(at, at, text)])
    return out


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true", help="rewrite the files in place")
    parser.add_argument("--root", type=Path, default=ROOT)
    arguments = parser.parse_args(argv)
    root = arguments.root
    moves, left, removals, index, source = plan(root)
    refused = [x for x in left if x[1] != "book-defined"]
    if arguments.write:
        for relative, text in apply(root, moves, removals, index, source).items():
            (root / relative).write_bytes(text.encode("utf-8", "surrogateescape"))
    added = include_edits(root)
    if arguments.write:
        for relative, text in added.items():
            (root / relative).write_bytes(text.encode("utf-8", "surrogateescape"))
    print("interfaces_relocate: include-books added to {} file(s)".format(len(added)))
    counts = collections.Counter(x[1] for x in left)
    print("interfaces_relocate: {} moved into {} host file(s); left in {}: {}".format(
        sum(len(v) for v in moves.values()), len(moves), SOURCE,
        ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) or "none"))
    for name, reason, detail in refused:
        print(f"  REFUSED {reason}: {name} {detail}".rstrip())
    return 1 if refused else 0


if __name__ == "__main__":
    sys.exit(main())
