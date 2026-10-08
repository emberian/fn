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
    python3 tools/theory_check.py --books books/replay books/store-node   # one cluster
    python3 tools/theory_check.py --book-order [--books ...]  # guard order, mv-nth opened
    python3 tools/theory_check.py --restore-table  # include-order export census

Label-restore exports are also checked on every normal run (including without
--strict).  A source comment declares each export's own-family; shared
dependencies outside it must precede its snapshot or declare a hidden-shared
exception backed by a non-local *-exported theory in that dependency.  --restore-table
reports each region's first-loaded repository books and external includes.
This recursive books/ check ignores scratch files named _*.lisp and does not
traverse ACL2 system books or expand event-generating macros.

THE CODEC LAYER.  A codec's own books -- its definitions, the proofs of its
round trips, and the seam and attachment books of plan 2026-09-22 §4.1 --
open the codec because they are the codec; they are listed, marked `layer',
and never counted.  Everything else is above the codec.  Above it, a book
counts when it opens a codec theory at the top, and also when it names an
implementation behind a seam (`fn-record-encode-impl', ...): the seam's
constrained function is what a book above the codec reasons about, and a
book that calls the implementation has stepped under it.

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
from fnmatch import fnmatchcase
import json
from pathlib import Path
import posixpath
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import lisp_source  # noqa: E402
BOOKS = ROOT / "books"

# The books whose theories are "the codec": the CBOR codec and its
# invariants, the record and statement codecs, the frame codec.
CODEC_BOOKS = {
    "cbor", "cbor-invariants", "records", "records-canonicality",
    "statement", "statement-invariants", "frame", "frame-fields",
    "frame-octets", "frame-trailer", "frame-journal", "config",
    "bp-primary-cbor", "checkpoint-codec", "bp-node-machine-codec",
}

# The codec layer: the codec books, the proof books of their round trips,
# and each seam's seam and attachment books.  These are the codec.
CODEC_LAYER = CODEC_BOOKS | {
    "records-invariants", "frame-invariants",
    "records-seam", "records-attach",
    "statement-codec", "statement-seam", "statement-attach",
    "codec-attach",
}

# An implementation hidden behind a seam: a `defun' in a codec-layer book
# whose name ends in `-impl'.
IMPL = re.compile(r"\(defun\s+(fn-[^\s()]*-impl)\b", re.IGNORECASE)

def forms(text: str) -> list:
    """The top-level forms of a book as nested lists of strings.

    Strings come back as their source spelling; atoms as lowercase text.
    Quote marks are dropped: `'(a b)` reads as `(a b)`, which is what a
    theory expression needs and nothing here cares about more.  Raises
    ValueError on unbalanced parentheses.
    """
    def convert(node):
        if isinstance(node, lisp_source.List):
            return [convert(child) for child in node.items]
        return node.text if isinstance(node, lisp_source.Str) else node.text.lower()

    try:
        return [convert(node) for node in lisp_source.read_all(text, strict=True)]
    except lisp_source.ReadError as error:
        raise ValueError(f"unbalanced {error.kind} paren") from None


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


def implementations(books_dir: Path = BOOKS) -> set[str]:
    """Every `-impl' function a codec-layer book defines."""
    found: set[str] = set()
    for stem in CODEC_LAYER:
        path = books_dir / f"{stem}.lisp"
        if path.is_file():
            found.update(m.group(1).lower() for m in IMPL.finditer(path.read_text(encoding="utf-8")))
    return found


def named_implementations(text: str, impls: set[str]) -> list[str]:
    """The implementation names a book's code mentions, outside comments and strings."""
    named: set[str] = set()

    def walk(node) -> None:
        if isinstance(node, list):
            for item in node:
                walk(item)
        elif isinstance(node, str) and node in impls:
            named.add(node)

    walk(forms(text))
    return sorted(named)


def audit(books_dir: Path = BOOKS, only: set[str] | None = None) -> dict:
    defined = theories(books_dir)
    impls = implementations(books_dir)
    rows = []
    for path in sorted(books_dir.glob("*.lisp")):
        book = f"books/{path.stem}"
        if only is not None and book not in only:
            continue
        layer = path.stem in CODEC_LAYER
        try:
            text = path.read_text(encoding="utf-8")
            openings = top_level_openings(text)
            impl = [] if layer else named_implementations(text, impls)
        except ValueError as error:
            rows.append({"book": book, "unreadable": str(error),
                         "opened": [], "codec": [], "impl": [], "layer": layer})
            continue
        opened = sorted({name for names in openings for name in names})
        if not opened and not impl:
            continue
        codec = [] if layer else [name for name in opened if is_codec(name, defined)]
        rows.append({"book": book, "opened": opened, "codec": codec, "impl": impl,
                     "layer": layer})
    rows.sort(key=lambda row: (not (row["codec"] or row["impl"]), row["layer"], row["book"]))
    counted = [row for row in rows if row["codec"] or row["impl"]]
    return {
        "schema": "fn-theory-check-v2",
        "books_read": sum(1 for _ in books_dir.glob("*.lisp")) if only is None else len(only),
        "books_with_top_level_openings": sum(1 for row in rows if row["opened"]),
        "books_opening_a_codec": len(counted),
        "codec_layer_books": sorted(row["book"] for row in rows if row["layer"]),
        "codec_theories": sorted({name for row in rows for name in row["codec"]}),
        "implementations_named": sorted({name for row in rows for name in row["impl"]}),
        "rows": rows,
    }


def summary(report: dict) -> str:
    return (f"theory-check: {report['books_with_top_level_openings']} of "
            f"{report['books_read']} books open a theory at the top for every "
            f"proof in them; {report['books_opening_a_codec']} above the codec "
            f"layer open a CODEC theory there or name a seam's implementation "
            f"({len(report['codec_theories'])} theories, "
            f"{len(report.get('implementations_named', []))} implementations), "
            f"which is the habit the 2026-09-22 freeze paid for; --table names them.")


def table(report: dict) -> list[str]:
    width = max((len(row["book"]) for row in report["rows"]), default=4)
    lines = [f"{'CODEC':5}  {'BOOK':{width}}  OPENED AT TOP LEVEL"]
    for row in report["rows"]:
        counted = row["codec"] or row.get("impl")
        flag = "codec" if counted else ("layer" if row.get("layer") else "")
        if counted:
            names = " ".join(row["codec"] + row.get("impl", []))
        else:
            names = " ".join(row["opened"][:6])
        lines.append(f"{flag:5}  {row['book']:{width}}  {names}")
    return lines


# --- BOOK-ORDER LINTS (obstructions-7 items 56 and 65) --------------------
#
# GUARD ORDER.  A guard verification (a `verify-guards' event, or a defun
# verified at its definition) of F that calls G fails at certify when G's
# own guards are verified only LATER in the same book, and passes in a world
# session where everything is verified already (depth-debt-5 lost two
# rounds).  `--guard-order' walks each book's forms in order.
#
# MV-NTH OPEN.  `mv-nth' enabled in a book's theory (a top-level in-theory)
# rewrites every multiple-value accessor in every goal of the book into
# car/cdr nests.  `--mv-nth' names the books.

def _ledger():
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import ledger  # noqa: PLC0415
    return ledger


def _low(x) -> str:
    return str(x).lower()


def _unlocal(form):
    while isinstance(form, list) and len(form) == 2 and _low(form[0]) == "local":
        form = form[1]
    return form


def _declares(form) -> tuple[dict[str, object], bool]:
    xargs: dict[str, object] = {}
    typed = False
    for item in form[3:]:
        if isinstance(item, list) and item and _low(item[0]) == "declare":
            for decl in item[1:]:
                if isinstance(decl, list) and decl and _low(decl[0]) == "xargs":
                    rest = decl[1:]
                    for key, value in zip(rest[::2], rest[1::2]):
                        xargs[_low(key).lstrip(":")] = value
                elif isinstance(decl, list) and decl and _low(decl[0]) == "type":
                    typed = True
    return xargs, typed


def _executed_symbols(term, out: set[str]) -> None:
    """Symbols of TERM a guard proof needs verified: an mbe's :logic is not."""
    if isinstance(term, list):
        if not term:
            return
        head = _low(term[0])
        if head in ("quote", "declare"):
            return
        if head == "mbe":
            rest = term[1:]
            for key, value in zip(rest[::2], rest[1::2]):
                if _low(key) != ":logic":
                    _executed_symbols(value, out)
            return
        for item in term:
            _executed_symbols(item, out)
    elif not isinstance(term, (str, int, float)) or type(term).__name__ == "Sym":
        out.add(_low(term))


DEFUNS = ("defun", "defund", "defun-inline", "defund-inline", "define")


def guard_events(text: str) -> list[tuple[int, str, list[tuple[str, int]]]]:
    """Each guard verification in the book, in order: (form number, the
    function, [(a callee of the same book, the form its guards are verified
    at)]).  Form numbers count top-level forms from 1, as proof_repl's do."""
    forms = [_unlocal(form) for form in _ledger().read_forms(text)]
    eager = False
    verified_at: dict[str, int] = {}
    events: list[tuple[int, str, object]] = []
    defs: dict[str, object] = {}
    for form, index in _ledger().source_events((f, i) for i, f in enumerate(forms, 1)):
        if not isinstance(form, list) or not form:
            continue
        head = _low(form[0])
        if head == "set-verify-guards-eagerness" and len(form) > 1 and _low(form[1]) == "2":
            eager = True
        elif head in DEFUNS and len(form) >= 4:
            name = _low(form[1])
            defs[name] = form
            xargs, typed = _declares(form)
            if _low(xargs.get("mode", "")).lstrip(":") == "program":
                continue
            flag = _low(xargs.get("verify-guards", ""))
            if flag == "nil":
                continue
            if (flag == "t" or head == "define" or eager or typed
                    or any(k in xargs for k in ("guard", "stobjs", "guard-hints"))):
                verified_at.setdefault(name, index)
                events.append((index, name, form[3:]))
        elif head == "verify-guards" and len(form) > 1:
            name = _low(form[1])
            verified_at.setdefault(name, index)
            if name in defs:
                events.append((index, name, defs[name][3:]))
    out = []
    for index, name, body in events:
        called: set[str] = set()
        _executed_symbols(body, called)
        callees = [(callee, verified_at[callee]) for callee in sorted(called - {name})
                   if callee in defs and callee in verified_at]
        out.append((index, name, callees))
    return out


def guard_order(text: str) -> list[str]:
    """Each guard verification of F calling a G of the same book whose guards
    are verified only later: 'form #I (F) calls G, verified at form #J'."""
    found = []
    for index, name, callees in guard_events(text):
        for callee, later in callees:
            if later > index:
                found.append(f"form #{index} verifies the guards of {name}, which calls "
                             f"{callee}, whose guards are verified only at form #{later}: "
                             f"certify fails here (a world session passes)")
    return found


def mv_nth_opened(text: str) -> bool:
    """Whether a top-level in-theory of the book enables mv-nth."""
    for form in _ledger().read_forms(text):
        form = _unlocal(form)
        if isinstance(form, list) and form and _low(form[0]) == "in-theory":
            symbols: set[str] = set()
            spec = form[1] if len(form) > 1 else None
            if isinstance(spec, list) and spec and _low(spec[0]) in ("enable", "e/d", "enable*"):
                target = spec[1] if _low(spec[0]) == "e/d" and len(spec) > 1 else spec[1:]
                _executed_symbols(target, symbols)
                if "mv-nth" in symbols:
                    return True
    return False


def book_lints(paths: list[Path], root: Path) -> list[str]:
    lines = []
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        relative = path.relative_to(root) if path.is_relative_to(root) else path
        for one in guard_order(text):
            lines.append(f"{relative}: guard-order: {one}")
        if mv_nth_opened(text):
            lines.append(f"{relative}: mv-nth: enabled in the book's theory (open it in a hint)")
    return lines


# A restore exports the theory at an earlier label after including books.
# A shared dependency first loaded inside that interval can lose all its
# rules: including it again above the exporter is redundant.  Declare the
# private family beside the snapshot, using books-relative globs:
#   ; theory-restore-own-family LABEL: private-* another-private-book
# Family members are intentionally hidden; dependencies outside that family
# must precede the snapshot when an outside book also includes them, unless
# their consumers explicitly restore a named exported theory. Such exceptions
# require a reason and a non-local *-exported deftheory in every matched book:
#   ; theory-restore-hidden-shared LABEL: shared-* -- restored by consumers
RESTORE_FAMILY = re.compile(
    r"^\s*;+\s*theory-restore-own-family\s+(\S+):\s*(.*?)\s*$", re.MULTILINE)

RESTORE_HIDDEN_SHARED = re.compile(
    r"^[ \t]*;+[ \t]*theory-restore-hidden-shared[ \t]+(\S+):[ \t]*(.*?)[ \t]+--[ \t]+(\S[^\n]*)$",
    re.MULTILINE)


def _events(fs, local=False):
    """Literal events, retaining local scope; never descend into proofs/macros."""
    for f in fs:
        if not isinstance(f, list) or not f:
            continue
        if f[0] == "local":
            yield from _events(f[1:], True)
        elif f[0] in ("progn", "encapsulate"):
            yield from _events(f[2:] if f[0] == "encapsulate" else f[1:], local)
        else:
            yield f, local


def _theory_refs(expr):
    if not isinstance(expr, list) or not expr:
        return set()
    names = set()
    if (expr[0] in ("theory", "current-theory", "universal-theory")
            and len(expr) == 2 and isinstance(expr[1], str)):
        names.add(expr[1])
    for child in expr:
        names.update(_theory_refs(child))
    return names


def restore_audit(books_dir: Path = BOOKS, only: set[str] | None = None) -> dict:
    """Census of literal label/include/restore regions and their shared leaks.

    Includes are resolved relative to each book, recursively under books/.
    Included books replay non-local events only.  Local includes in the book
    being audited still affect its proof world, and local includes anywhere
    count as evidence of an outside consumer.  System books are reported by
    name, not traversed.  Scratch books (_*) are not repository consumers.
    """
    events, families, graph, consumers = {}, {}, {}, {}
    hidden_shared, exported = {}, {}
    findings = []

    def target(book, f):
        if f[0] != "include-book" or len(f) < 2:
            return None
        if ":dir" in f[2:]:
            return None
        return posixpath.normpath(posixpath.join(posixpath.dirname(book),
                                               f[1].strip('"'))).removesuffix(".lisp")

    for path in sorted(books_dir.rglob("*.lisp")):
        if path.name.startswith("_"):
            continue
        book = path.relative_to(books_dir).with_suffix("").as_posix()
        text = path.read_text(encoding="utf-8")
        try:
            events[book] = list(_events(forms(text)))
        except ValueError as error:
            findings.append(f"books/{book}: theory-restore: unreadable: {error}")
            continue
        families[book] = {name.lower(): pats.split()
                          for name, pats in RESTORE_FAMILY.findall(text)}
        hidden_shared[book] = {
            name.lower(): {"patterns": pats.split(), "reason": reason.strip()}
            for name, pats, reason in RESTORE_HIDDEN_SHARED.findall(text)}
        exported[book] = sorted(f[1] for f, local in events[book]
                                if not local and f[0] == "deftheory"
                                and len(f) >= 3 and f[1].endswith("-exported"))
        graph[book] = []
        for f, local in events[book]:
            dep = target(book, f)
            if dep is not None:
                consumers.setdefault(dep, set()).add(book)
                if not local:
                    graph[book].append(dep)

    def closure(roots):
        seen, pending = set(), list(roots)
        while pending:
            book = pending.pop()
            if book in seen:
                continue
            seen.add(book)
            pending.extend(graph.get(book, []))
        return seen

    regions = []
    for book, es in events.items():
        if only is not None and f"books/{book}" not in only:
            continue
        labels, includes = {}, []
        for i, (f, local) in enumerate(es):
            if f[0] in ("deftheory", "deflabel"):
                labels[f[1]] = i
            elif f[0] == "include-book":
                includes.append((i, f))
            elif f[0] == "in-theory":
                refs = _theory_refs(f) & labels.keys()
                if not refs:
                    continue
                start = min(labels[name] for name in refs)
                end = max(labels[name] for name in refs)
                end = i if end == start else end
                inside = [(j, inc) for j, inc in includes if start < j < end]
                if not inside:
                    continue
                label = next(name for name in refs if labels[name] == start)
                before = closure(target(book, inc) for j, inc in includes
                                 if j < start and target(book, inc) is not None)
                added = closure(target(book, inc) for _, inc in inside
                                if target(book, inc) is not None) - before
                own = families[book].get(label, [])
                hidden = hidden_shared[book].get(label, {"patterns": [], "reason": ""})
                row = {"book": f"books/{book}", "label": label, "local": local,
                       "own_family": own, "hidden_shared": hidden,
                       "first_loads": sorted(added),
                       "external_includes": [inc[1:] for _, inc in inside
                                             if target(book, inc) is None]}
                regions.append(row)
                if local:
                    continue  # A local theory event exports no disabled rules.
                prefix = f"books/{book}: theory-restore {label}"
                if not own:
                    findings.append(f"{prefix}: missing theory-restore-own-family declaration")
                for dep in sorted(added):
                    if any(fnmatchcase(dep, pat) for pat in hidden["patterns"]):
                        if exported.get(dep):
                            continue
                        findings.append(f"{prefix}: hidden-shared books/{dep} has no "
                                        "non-local *-exported deftheory")
                        continue
                    if any(fnmatchcase(dep, pat) for pat in own):
                        continue
                    outside = sorted(user for user in consumers.get(dep, set())
                                     if user != book and
                                     not any(fnmatchcase(user, pat) for pat in own))
                    if outside:
                        findings.append(f"{prefix}: first-loads shared books/{dep}; "
                                        f"outside includer books/{outside[0]}; include it "
                                        "before the snapshot")
    return {"regions": regions, "findings": findings}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Codec theories opened book-wide.")
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--table", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 when any book above the codec layer opens a codec "
                             "theory at the top or names a seam's implementation")
    parser.add_argument("--books", nargs="+", default=None,
                        help="restrict the report to these books (books/NAME)")
    parser.add_argument("--book-order", action="store_true",
                        help="warn-only: guard verifications ahead of a callee's, and "
                             "mv-nth enabled in a book's theory (--books to restrict)")
    parser.add_argument("--restore-table", action="store_true",
                        help="list label-restore regions and their first-loaded books")
    args = parser.parse_args(argv)
    if args.book_order:
        root = Path(__file__).resolve().parents[1]
        paths = ([root / (name.removesuffix(".lisp") + ".lisp") for name in args.books]
                 if args.books else sorted((root / "books").glob("*.lisp"))
                 + sorted((root / "tests" / "acl2").glob("*.lisp")))
        lines = book_lints(paths, root)
        print("\n".join(lines + [f"theory_check --book-order: {len(lines)} warning(s) over "
                                  f"{len(paths)} book(s)"]))
        return 0
    only = None
    if args.books:
        only = {name.removesuffix(".lisp") for name in args.books}
    report = audit(only=only)
    restores = restore_audit(only=only)
    report["theory_restores"] = restores
    if args.json:
        print(json.dumps(report, indent=1, sort_keys=True))
    elif args.table:
        print("\n".join(table(report)))
    if args.summary or not (args.json or args.table):
        print(summary(report))
    if not args.json:
        if args.restore_table:
            for row in restores["regions"]:
                print(f"{row['book']} {row['label']} "
                      f"({'local' if row['local'] else 'export'}): "
                      + ", ".join(row["first_loads"]) +
                      (f"; external {row['external_includes']}" if row["external_includes"] else ""))
        for finding in restores["findings"]:
            print(finding)
        print(f"theory-restore: {len(restores['regions'])} region(s), "
              f"{len(restores['findings'])} finding(s)")
    return 1 if restores["findings"] or (args.strict and report["books_opening_a_codec"]) else 0


if __name__ == "__main__":
    raise SystemExit(main())
