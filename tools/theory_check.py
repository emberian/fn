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
import json
from pathlib import Path
import re
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import lisp_source  # noqa: E402
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


