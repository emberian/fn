#!/usr/bin/env python3
"""Find the witnesses in `tests/acl2/` that do not bite.

`AGENTS.md` says a keystone ships with "a reachable non-degenerate witness and
one `must-fail` case per hypothesis showing the conclusion fails without it",
and that "a separating witness must separate predicates by more than their
weakest clause".  Nothing enforced that, and on 2026-09-20 three lanes each
found, by accident, a test that passed while proving nothing:

* `tests/acl2/owner-tests` asserted a durable outcome leaves the connection
  list UNCHANGED.  True only because `fn-own-conn-boundedp` was false of every
  connection, so the test pinned the defect and passed for as long as it lived.
* The S4-1 and S5-1 hostile-batch witnesses of `tests/acl2/stx-transit-tests`
  built both carriers with a prose body, so `fn-stx-delta` was `NIL` and every
  assertion held of an EMPTY delta.
* `fn-served-submission-of-append` and `fn-cpp-find-of-append` were false and
  had counterexamples, found only when a neighbouring proof reached them.

None of the three is visible to a reader of the source: each needs the VALUE.
So this tool evaluates.  `tools/ledger.py` is deliberately the other thing --
its docstring promises that "nothing is interned, evaluated, or macro-expanded,
so reading a book cannot run a book", and its teeth-form lint is a shape test
on `must-fail` bodies.  Putting an ACL2-running check inside it would break
that promise for every caller of `make check`.  This is a separate tool that
imports the ledger's reader and adds the evaluation the ledger may not do.

    python3 tools/teeth_check.py                  # static pass, no ACL2
    python3 tools/teeth_check.py --evaluate       # one ACL2 per test book
    python3 tools/teeth_check.py --evaluate tests/acl2/owner-tests.lisp
    python3 tools/teeth_check.py --report         # static + the saved values
    python3 tools/teeth_check.py --summary        # the counts `make check` prints
    python3 tools/teeth_check.py --table          # macro-generated teeth, marked apart

MACRO-GENERATED TEETH.  A book may write its witnesses through a `defmacro`
that expands to one `defthm` -- `feed-connection-teeth-tests.lisp` admits a
keystone once through such a macro and then calls it again under `must-fail`,
once per hypothesis, so a must-fail that fails for the wrong reason is caught
by the same hints that prove the keystone.  A reader of the SOURCE alone
cannot see this: the sixteen must-fails of that book are sixteen calls of
three macros, and none of them is the literal text `must-fail` at the call
site for thirteen of them.  This tool reads each book's own top-level
`defmacro` forms and, for a macro whose template either submits a `must-fail`
itself or is wrapped in one at the call site, counts each call as one tooth,
attributed to the theorem name the call gives it -- never to a macro defined
in a DIFFERENT book, and never to a `must-fail` a macro only mentions inside
a comment or a string, since neither reaches the reader as a form.  `--table`
lists them, and the book's own literal (non-macro) `must-fail` forms beside
them, marked apart.

The static pass needs no ACL2 and is what `make check` runs.  `--evaluate`
writes `build/teeth/values.json`; `--report` reads it back, so the expensive
half runs when a lane asks for it and its findings survive in one file.

WHAT IT CANNOT SEE.  A flag is a question for a human, never a verdict.

* It evaluates witnesses in the world the book itself builds.  A book whose
  `include-book` fails evaluates nothing, and is reported `prefix-failed`
  rather than clean.
* "Degenerate" is a property of the printed value, not of the intent.  A
  refusal test SHOULD assert `NIL`; the tool cannot tell an asserted refusal
  from an accidental one, so it reports the pair (the claim, the value) and
  leaves the reading to the reader.
* It says nothing about whether a theorem is TRUE, whether a hypothesis is
  necessary, or whether a witness is the RIGHT witness for its keystone.
* `assert-event` bodies are ground, so every probe is ground.  A property
  under a quantifier, or a `defthm` in a test book, is out of scope.
"""

from __future__ import annotations

import argparse
import collections
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402
from ledger import Sym, head  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT / "tests/acl2"
VALUES = ROOT / "build/teeth/values.json"
PROOFS = ROOT / "planning/proofs.json"

# Forms that contain other events rather than being one.
TRANSPARENT = {"local", "progn", "progn!", "with-output", "defsection",
               "defsection-progn", "encapsulate", "make-event", "must-succeed",
               "must-succeed*", "value-triple"}
# A body naming any of these is asking the world about a symbol, not
# exercising a function on a value: the guard-world audit of proof-style
# section 6.  It is evidence, but it is not a witness and has no teeth.
WORLD = {"w", "state", "symbol-class", "guard", "formals", "arity",
         "stobjs-out", "body", "macro-args", "getprop", "fgetprop"}
# Logical connectives and equalities: transparent for the purpose of finding
# the claim a witness is making.
STRIP = {"not", "null"}
SPLIT = {"and"}
EQUALITIES = {"equal", "eq", "eql", "equalp", "iff", "=", "string-equal"}
# Forms whose first argument is a binding list rather than a term.
BINDERS = {"let", "let*", "mv-let", "mv?-let", "b*", "cond", "case", "lambda"}
# Claims that hold of an empty collection whatever else is true.  The
# collection is the argument named by the index.
VACUOUS_OVER_EMPTY = {
    "member-equal": 1, "member": 1, "assoc-equal": 1, "assoc": 1,
    "subsetp-equal": 0, "subsetp": 0, "fn-subsetp": 0,
    "no-duplicatesp-equal": 0, "no-duplicatesp": 0, "fn-no-duplicatesp": 0,
    "intersectp-equal": 0, "intersectp": 0,
}
# Values a witness evaluates to when the thing it meant to exercise did not
# happen.  NOT `0`, and NOT a tag-only record: measured on this corpus, `0` is
# a real minimum time (`*anchor-mint*`), a real shared txid and a real
# `fn-nntp-group-low`, and `(:RESTART)` is a real nullary event -- treating
# either as empty produced eight false flags and no true one.
DEGENERATE = {"NIL", '""', "()"}

MARK = re.compile(r"<FNT ([^>]+)>\n?(.*?)</FNT>", re.S)
INCLUDE_FAILED = re.compile(r"ACL2 Error in \( INCLUDE-BOOK")
# `ACL2 Error [Translate] in ( DEFCONST *FF2* ...)`: the form did not run at
# all, which is a different defect from an assertion that ran and did not
# bite.  The survey counts them separately and the report keeps them apart.
ACL2_ERROR = re.compile(
    r"^ACL2 Error(?: \[(\w+)\])? in (?:\( ?([A-Z0-9!*-]+)[^)]*\)|([A-Z-]+)):", re.M)


# --------------------------------------------------------------------------
# rendering a read form back to Lisp text
# --------------------------------------------------------------------------


def render(form: object) -> str:
    """Lisp text for a form the ledger's reader produced.

    The reader loses the distinction between a string literal and the text it
    keeps for an exact rational, and it lower-cases symbols (harmless: the
    ACL2 reader upper-cases them again).  Every rendering is round-tripped by
    `renderable` before it reaches a driver, so a form this cannot reproduce
    is dropped rather than mis-evaluated.
    """
    if isinstance(form, Sym):
        return str(form)
    if isinstance(form, bool):  # not produced by the reader; guard anyway
        return "t" if form else "nil"
    if isinstance(form, (int, float)):
        return repr(form)
    if isinstance(form, str):
        return '"' + form.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(form, list):
        if head(form) == "quote" and len(form) == 2:
            return "'" + render(form[1])
        return "(" + " ".join(render(item) for item in form) + ")"
    raise ValueError(f"cannot render {form!r}")


RATIONAL = re.compile(r"[+-]?\d+/\d+\Z")


def ambiguous(form: object) -> bool:
    """Does this form contain an atom the ledger's reader cannot round-trip?

    `ledger.number` keeps an exact rational as its TEXT, and a Lisp string
    literal is also a Python `str`, so `1/2` and `"1/2"` read identically.
    Rendering the first as the second changes the term: the scheduler's
    `(< (fn-sched-pos ...) 1/2)` came back as a comparison against a STRING
    and the tool called a true assertion false.  A term this cannot tell
    apart is not probed.
    """
    if isinstance(form, Sym):
        return False
    if isinstance(form, str):
        return bool(RATIONAL.match(form))
    if isinstance(form, list):
        return any(ambiguous(item) for item in form)
    return False


def renderable(form: object) -> str | None:
    """`render(form)`, but only when reading it back gives `form` again."""
    if ambiguous(form):
        return None
    try:
        text = render(form)
        back = ledger.read_forms(text)
    except Exception:
        return None
    return text if len(back) == 1 and back[0] == form else None


# --------------------------------------------------------------------------
# what a book asserts
# --------------------------------------------------------------------------


@dataclass
class Claim:
    """One conjunct of one `assert-event`, with the polarity it is asserted at."""

    book: str
    line: int
    index: int      # which assert-event in the book
    clause: int     # which conjunct of it
    positive: bool  # asserted true, rather than under a `not`
    term: object    # the conjunct, with `not`/`with-guard-checking` stripped
    predicate: str | None


@dataclass
class Assertion:
    book: str
    line: int
    index: int
    top: int                    # which top-level form of the book holds it
    body: object
    audit: bool                 # a guard-world audit, not a witness
    # `assert-event` or `defconst`: a defconst body is translated for
    # evaluation too, so it is read for the multi-valued check, but it
    # asserts nothing and is neither counted nor probed.
    kind: str = "assert-event"
    claims: list[Claim] = field(default_factory=list)


@dataclass
class Probe:
    """A ground term whose value decides whether a claim bites."""

    key: str
    book: str
    line: int
    text: str
    role: str       # whole | subject | hypothesis | anchor
    claim: int      # index into the book's claim list, or -1
    note: str = ""


def strip_wrappers(form: object) -> tuple[object, bool]:
    """(the claim inside `not`/`with-guard-checking`/`null`, its polarity)."""
    positive = True
    while isinstance(form, list) and form:
        name = head(form)
        if name == "with-guard-checking" and len(form) == 3:
            form = form[2]
        elif name in STRIP and len(form) == 2:
            positive, form = not positive, form[1]
        else:
            break
    return form, positive


def conjuncts(form: object) -> list[object]:
    if head(form) in SPLIT:
        out: list[object] = []
        for item in form[1:]:
            out.extend(conjuncts(item))
        return out
    return [form]


def mentions_any(form: object, names: set[str]) -> bool:
    if isinstance(form, Sym):
        return str(form) in names
    if isinstance(form, list):
        return any(mentions_any(item, names) for item in form)
    return False


def defconst_name(form: object) -> bool:
    return (isinstance(form, Sym) and len(form) > 2
            and form.startswith("*") and form.endswith("*"))


def subjects(term: object) -> list[tuple[object, str]]:
    """The terms whose value decides this claim, with a note on each.

    The subject of `(not (fn-statep *forged*))` is `*forged*`: the witness the
    claim is about.  The subject of `(equal (fn-delta a b) nil)` is
    `(fn-delta a b)`, and `nil` is the expectation, not a subject.  So: every
    argument of the claim that is a call or a defconst, plus, for an equality,
    each side that is not a literal.
    """
    if not isinstance(term, list) or not term or head(term) in BINDERS:
        # A binder's first argument is a BINDING LIST, not a term: probing
        # `((s (fn-sn-test-... )))` hands ACL2 a list in function position
        # and it refuses the form.  The claim as a whole is still probed.
        return []
    out: list[tuple[object, str]] = []
    for position, argument in enumerate(term[1:]):
        if not isinstance(argument, list):
            if defconst_name(argument):
                out.append((argument, f"arg{position}"))
            continue
        if head(argument) is None or head(argument) == "quote":
            continue  # quoted or bare data, not a call
        note = "side" if head(term) in EQUALITIES else f"arg{position}"
        out.append((argument, note))
    return out


def book_text(path: Path) -> list[str]:
    """The book's source, one string per top-level form, in order."""
    source = path.read_text(encoding="utf-8")
    forms = ledger.Reader(source).top_level()
    lines = source.splitlines(keepends=True)
    out = []
    for index, (_form, line) in enumerate(forms):
        end = (forms[index + 1][1] - 1) if index + 1 < len(forms) else len(lines)
        out.append("".join(lines[line - 1:end]))
    return out


def read_book(path: Path) -> tuple[list[Assertion], list[str], str | None]:
    """Every `assert-event` in a test book, its defconsts, and a read error."""
    try:
        forms = ledger.Reader(path.read_text(encoding="utf-8")).top_level()
    except Exception as error:  # a book we cannot read is a finding of its own
        return [], [], str(error)
    book = path.relative_to(ROOT).as_posix()
    assertions: list[Assertion] = []
    constants: list[str] = []

    top = 0

    def walk(form: object, line: int) -> None:
        name = head(form)
        if name == "defconst" and len(form) > 1 and isinstance(form[1], Sym):
            constants.append(str(form[1]))
            # A defconst body is translated for evaluation too, so it is
            # subject to the multi-valued check; it is not a witness, so it
            # is recorded as an audit and no probe is built for it.
            if len(form) > 2:
                assertions.append(Assertion(
                    book=book, line=line, index=len(assertions), top=top,
                    body=form[2], audit=True, kind="defconst"))
            return
        if name == "assert-event" and len(form) > 1:
            body = form[1]
            index = len(assertions)
            record = Assertion(book=book, line=line, index=index, top=top,
                               body=body, audit=mentions_any(body, WORLD))
            inner, positive = strip_wrappers(body)
            for clause, part in enumerate(conjuncts(inner)):
                claim, polarity = strip_wrappers(part)
                record.claims.append(Claim(
                    book=book, line=line, index=index, clause=clause,
                    positive=positive == polarity, term=claim,
                    predicate=head(claim)))
            assertions.append(record)
            return
        if name in TRANSPARENT and isinstance(form, list):
            for item in form[1:]:
                walk(item, line)

    for top, (form, line) in enumerate(forms):
        walk(form, line)
    return assertions, constants, None


# --------------------------------------------------------------------------
# macro-generated teeth
# --------------------------------------------------------------------------
#
# A macro-generated tooth is not an `assert-event`: it is a `defthm` a
# `defmacro` in the SAME book produces, admitted once (a witness) and
# resubmitted under `must-fail` with one hypothesis dropped (a must-fail).
# It has no ground value to evaluate -- ACL2's own prover is the check -- so
# it is read here, never fed to `probes_for`/`evaluate`, and it is counted
# separately from the `assert-event` witnesses `counts()` reports.

DEFTHM_NAMES = {"defthm", "defthmd"}


def _is_must_fail_name(name: object) -> bool:
    """Is this a `must-fail`-family head?  `ledger.py`'s own convention:
    the family shares a prefix (`must-fail`, `must-fail!`,
    `must-fail-with-error`, ...), not a fixed set."""
    return isinstance(name, str) and name.startswith("must-fail")


def contains_must_fail(form: object) -> bool:
    """Does this template structurally submit a `must-fail` form?

    Walks the read s-expression, so a `must-fail` written inside a COMMENT
    or a STRING literal -- neither of which the reader keeps as a form --
    can never make this true."""
    if isinstance(form, list) and form:
        if _is_must_fail_name(head(form)):
            return True
        return any(contains_must_fail(item) for item in form)
    return False


def find_defthm(form: object) -> object | None:
    """The first `defthm`/`defthmd` this template admits outright, or None.

    Does not look inside a `must-fail`-family form: a `defthm` there is
    asked to FAIL, not admitted, so it is not "the template admits the
    keystone."""
    if not isinstance(form, list) or not form:
        return None
    name = head(form)
    if name in DEFTHM_NAMES:
        return form
    if _is_must_fail_name(name):
        return None
    for item in form:
        found = find_defthm(item)
        if found is not None:
            return found
    return None


def formal_names(formals_form: object) -> list[str]:
    """A `defmacro` lambda-list's plain names: lambda-list keywords
    (`&optional`, `&rest`, ...) and each entry's default value are dropped,
    keeping just the name a `,name` in the template can refer to."""
    if not isinstance(formals_form, list):
        return []
    out = []
    for item in formals_form:
        if isinstance(item, Sym) and not str(item).startswith("&"):
            out.append(str(item))
        elif isinstance(item, list) and item and isinstance(item[0], Sym):
            out.append(str(item[0]))
    return out


@dataclass
class MacroInfo:
    """One `defmacro` this book defines, and what its template does."""

    name: str
    line: int
    formals: list[str]
    has_must_fail: bool   # the template itself submits a must-fail
    has_defthm: bool      # the template admits a defthm outright
    name_index: int | None  # which formal fills the produced defthm's name


def macro_info(form: list, line: int) -> MacroInfo | None:
    """Read one top-level `defmacro`, or None if its shape is not this one."""
    if head(form) != "defmacro" or len(form) < 4 or not isinstance(form[1], Sym):
        return None
    name = str(form[1])
    formals = formal_names(form[2])
    body = form[-1]
    template = body[1] if head(body) == "quasiquote" and len(body) == 2 else body
    defthm = find_defthm(template)
    name_index = None
    if defthm is not None and len(defthm) > 1:
        name_arg = defthm[1]
        if (isinstance(name_arg, list) and len(name_arg) == 2
                and head(name_arg) == "unquote" and isinstance(name_arg[1], Sym)
                and str(name_arg[1]) in formals):
            name_index = formals.index(str(name_arg[1]))
    return MacroInfo(name=name, line=line, formals=formals,
                     has_must_fail=contains_must_fail(template),
                     has_defthm=defthm is not None, name_index=name_index)


@dataclass
class MacroTooth:
    """One theorem a book-local macro's call produced: a must-fail or a
    witness.  `theorem` is the name the CALL gives it -- read from the
    macro's own name parameter, filled in from the call's argument at that
    position -- not a registry keystone; nothing here claims the two are
    the same theorem."""

    book: str
    line: int
    macro: str
    theorem: str | None
    kind: str  # "must-fail" | "witness"


def unwrap_call(form: object) -> tuple[object | None, bool]:
    """Peel `local`, a `must-fail`-family wrapper, `make-event` and a
    quasiquote off a top-level form, down to the call underneath.

    A book writes its teeth as `(local (must-fail (MACRO name hyps)))` and,
    when the hypotheses are assembled at read time, `(local (must-fail
    (make-event `(MACRO name (,h1 ,h2 ...)))))`.  `local` and a `must-fail`
    wrapper are transparent to the call inside them; `make-event`'s argument
    is the form it submits; a backquoted form's head is unaffected by the
    unquotes in its tail.  Returns (the call form, or None; whether a
    `must-fail`-family wrapper was crossed to reach it)."""
    node = form
    wrapped = False
    while isinstance(node, list) and node:
        name = head(node)
        if name == "local" and len(node) == 2:
            node = node[1]
        elif _is_must_fail_name(name) and len(node) >= 2:
            wrapped = True
            node = node[1]
        elif name == "make-event" and len(node) == 2:
            node = node[1]
        elif name == "quasiquote" and len(node) == 2:
            node = node[1]
        else:
            break
    return (node if isinstance(node, list) and node else None), wrapped


def macro_teeth_for_book(path: Path) -> tuple[list[MacroTooth], dict[str, MacroInfo]]:
    """This book's macro-generated teeth, and the macros that produced them.

    Only a `defmacro` READ FROM THIS SAME BOOK is ever attributed: a call of
    a macro this book merely includes is invisible here, same as it always
    was, rather than guessed at from a definition this reader never saw."""
    try:
        forms = ledger.Reader(path.read_text(encoding="utf-8")).top_level()
    except Exception:
        return [], {}
    book = path.relative_to(ROOT).as_posix()
    macros: dict[str, MacroInfo] = {}
    for form, line in forms:
        if head(form) == "defmacro":
            info = macro_info(form, line)
            if info is not None:
                macros[info.name] = info
    teeth: list[MacroTooth] = []
    for form, line in forms:
        if head(form) == "defmacro":
            continue
        call, wrapped = unwrap_call(form)
        info = macros.get(head(call))
        if info is None or call is None:
            continue
        name = head(call)
        index = info.name_index if info.name_index is not None else 0
        theorem = (str(call[index + 1]) if len(call) > index + 1
                  and isinstance(call[index + 1], Sym) else None)
        if wrapped or info.has_must_fail:
            teeth.append(MacroTooth(book=book, line=line, macro=name,
                                    theorem=theorem, kind="must-fail"))
        if info.has_defthm and not wrapped:
            teeth.append(MacroTooth(book=book, line=line, macro=name,
                                    theorem=theorem, kind="witness"))
    return teeth, macros


_MACRO_TEETH: dict[str, list[MacroTooth]] | None = None


def macro_teeth_for_paths(paths: list[Path]) -> dict[str, list[MacroTooth]]:
    found: dict[str, list[MacroTooth]] = {}
    for path in paths:
        teeth, _macros = macro_teeth_for_book(path)
        if teeth:
            found[path.relative_to(ROOT).as_posix()] = teeth
    return found


def macro_teeth_by_book() -> dict[str, list[MacroTooth]]:
    """Every test book's macro-generated teeth, corpus-wide and cached."""
    global _MACRO_TEETH
    if _MACRO_TEETH is None:
        _MACRO_TEETH = macro_teeth_for_paths(sorted(TESTS.glob("*.lisp")))
    return _MACRO_TEETH


def macro_teeth_totals(macro_teeth: dict[str, list[MacroTooth]]) -> dict[str, int]:
    must_fails = sum(1 for teeth in macro_teeth.values()
                     for tooth in teeth if tooth.kind == "must-fail")
    witnesses = sum(1 for teeth in macro_teeth.values()
                    for tooth in teeth if tooth.kind == "witness")
    macros = len({(book, tooth.macro) for book, teeth in macro_teeth.items()
                 for tooth in teeth})
    return {"must_fails": must_fails, "witnesses": witnesses,
            "macros": macros, "books": len(macro_teeth)}


def literal_must_fails(book: str, generated_lines: set[int]) -> list[tuple[int, str]]:
    """This book's own top-level `must-fail` forms that no local macro
    produced, for `--table` to set beside the macro-generated ones."""
    tree = ledger.load_tree()
    info = tree.books.get(book)
    if info is None:
        return []
    out = []
    for line, arguments in info.must_fail_forms:
        if line in generated_lines:
            continue
        text = renderable(arguments[0]) if arguments else None
        out.append((line, (text or "<unrenderable>")[:48]))
    return out


def macro_table(macro_teeth: dict[str, list[MacroTooth]]) -> list[str]:
    """Every macro-generated tooth, and each book's literal must-fails
    beside them, GEN marking which is which."""
    rows: list[tuple[str, str, str, int, str, str]] = []
    for book, teeth in sorted(macro_teeth.items()):
        generated_lines = {tooth.line for tooth in teeth}
        for tooth in sorted(teeth, key=lambda t: t.line):
            rows.append(("macro", tooth.kind, book, tooth.line,
                        tooth.theorem or "?", tooth.macro))
        for line, description in literal_must_fails(book, generated_lines):
            rows.append(("literal", "must-fail", book, line, description, ""))
    if not rows:
        return ["teeth: no macro-generated must-fail or witness in the "
                "selected books"]
    rows.sort(key=lambda r: (r[2], r[3]))
    width_book = max(len(r[2]) for r in rows)
    width_theorem = max(len(r[4]) for r in rows)
    header = (f"{'GEN':7}  {'KIND':9}  {'BOOK':{width_book}}  {'LINE':>5}  "
             f"{'THEOREM':{width_theorem}}  MACRO")
    lines = [header]
    for origin, kind, book, line, theorem, macro in rows:
        lines.append(f"{origin:7}  {kind:9}  {book:{width_book}}  {line:5d}  "
                     f"{theorem:{width_theorem}}  {macro}")
    return lines


# --------------------------------------------------------------------------
# probes
# --------------------------------------------------------------------------


def probes_for(assertions: list[Assertion]) -> list[Probe]:
    """The ground terms to evaluate for one book."""
    out: list[Probe] = []
    for record in assertions:
        if record.audit or record.kind != "assert-event":
            continue
        text = renderable(record.body)
        if text is not None:
            out.append(Probe(key=f"a{record.index}", book=record.book,
                             line=record.line, text=text, role="whole",
                             claim=-1))
        for claim in record.claims:
            term = renderable(claim.term)
            if term is not None and isinstance(claim.term, list):
                out.append(Probe(
                    key=f"a{record.index}c{claim.clause}t", book=record.book,
                    line=record.line, text=term, role="claim",
                    claim=claim.clause,
                    note=("positive" if claim.positive else "negative")))
            if claim.predicate == "implies" and len(claim.term) >= 2:
                hypothesis = renderable(claim.term[1])
                if hypothesis is not None:
                    out.append(Probe(
                        key=f"a{record.index}c{claim.clause}h", book=record.book,
                        line=record.line, text=hypothesis, role="hypothesis",
                        claim=claim.clause))
            for position, (term, note) in enumerate(subjects(claim.term)):
                subject = renderable(term)
                if subject is None:
                    continue
                out.append(Probe(
                    key=f"a{record.index}c{claim.clause}s{position}",
                    book=record.book, line=record.line, text=subject,
                    role="subject", claim=claim.clause, note=note))
    return out


def probe_form(probe: Probe) -> str:
    return (f'(cw "~%<FNT {probe.key}>~%~X01~%</FNT>~%" '
            f'(with-guard-checking :none {probe.text}) (evisc-tuple 5 14 nil nil))')


def driver(book: Path, probe_list: list[Probe],
           forms: list[str] | None = None,
           where: dict[str, int] | None = None) -> str:
    """An ACL2 driver: the book's own source with the probes spliced in.

    The probes go IMMEDIATELY AFTER the top-level form that holds the
    assertion, not at the end of the book.  A book changes the world as it
    goes -- `tests/acl2/crypto-seam-tests.lisp` runs the same assertions
    under `fn-toy-length-digest` and then under `fn-toy-mix-digest`, five
    `defattach` forms in one file -- so a value read at the end of the book
    is a value from the wrong world.  Measured: evaluating at the end
    reported four assertions of that book false that hold where they stand.

    The book's `include-book` forms are relative to the BOOK's directory, so
    the caller runs this there.  `tools/proof_profile.py` reported over an
    empty world for its whole life because it did not (found 2026-09-20).
    """
    if forms is not None and where is not None:
        lines = ["(set-ld-error-action :continue state)"]
        after: dict[int, list[Probe]] = collections.defaultdict(list)
        for probe in probe_list:
            after[where[probe.key]].append(probe)
        for index, text in enumerate(forms):
            lines.append(text.rstrip("\n"))
            lines.extend(probe_form(probe) for probe in after.get(index, ()))
        lines.append('(cw "~%<FNT-PREFIX-DONE>~%")')
        lines.append("(good-bye)")
        return "\n".join(lines) + "\n"
    lines = [
        "(set-inhibit-output-lst '(proof-tree prove proof-builder))",
        "(set-ld-error-action :continue state)",
        f'(ld "{book.name}" :ld-error-action :continue :ld-pre-eval-print nil)',
        '(cw "~%<FNT-PREFIX-DONE>~%")',
    ]
    for probe in probe_list:
        lines.append(
            f'(cw "~%<FNT {probe.key}>~%~X01~%</FNT>~%" '
            f'(with-guard-checking :none {probe.text}) (evisc-tuple 5 14 nil nil))')
    lines.append("(good-bye)")
    return "\n".join(lines) + "\n"


def parse_log(text: str) -> dict[str, str]:
    """Each probe's printed value, by key.  A missing key did not evaluate."""
    return {match.group(1).strip(): match.group(2).strip()
            for match in MARK.finditer(text)}


def evaluate(book: Path, probe_list: list[Probe], timeout: int,
             keep: Path | None = None,
             forms: list[str] | None = None,
             where: dict[str, int] | None = None) -> dict:
    """Run one ACL2 over one book and collect the probe values."""
    scratch = Path(os.environ.get("TMPDIR", "/tmp")) / f"fn-teeth-{book.stem}.lsp"
    scratch.write_text(driver(book, probe_list, forms, where), encoding="utf-8")
    with scratch.open("rb") as handle:
        answer = subprocess.run(
            [str(ROOT / "tools/acl2"), "--timeout", str(timeout),
             "--label", f"teeth {book.stem}"],
            cwd=str(book.parent), stdin=handle, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False)
    # A witness is octets, and a book that prints one prints bytes no
    # encoding claims: decode loosely rather than lose the whole run.
    log = (answer.stdout or b"").decode("utf-8", errors="replace")
    if keep is not None:
        keep.parent.mkdir(parents=True, exist_ok=True)
        keep.write_text(log, encoding="utf-8")
    values = parse_log(log)
    errors = [{"kind": m.group(1) or "", "form": m.group(2) or m.group(3) or ""}
              for m in ACL2_ERROR.finditer(log)]
    return {
        "errors": errors,
        "book": book.relative_to(ROOT).as_posix(),
        "exit": answer.returncode,
        "prefix": "ok" if "<FNT-PREFIX-DONE>" in log else "failed",
        "include_failed": bool(INCLUDE_FAILED.search(log)),
        "values": values,
        "probes": {probe.key: probe.text for probe in probe_list},
    }


# --------------------------------------------------------------------------
# reading a value
# --------------------------------------------------------------------------


def degenerate(value: str | None) -> str | None:
    """Why this printed value is degenerate, or None.

    Only emptiness counts.  A record whose fields are all `NIL` is still a
    record and its equality still separates its tag, so `(:WANT NIL)` is not
    degenerate: calling it so flagged five of `peer-inbound-tests`'s
    transfer decisions, every one of them a real claim.
    """
    if value is None:
        return None
    text = value.strip()
    if text in DEGENERATE:
        return "nil" if text in ("NIL", "()") else "empty"
    return None


def tag_only(value: str | None) -> bool:
    """A record with a tag and no members: reported, never called empty."""
    return bool(value) and bool(re.fullmatch(r"\(:[A-Z0-9-]+\)", value.strip()))


def literal(text: str) -> bool:
    """Is this probe's source text a constant rather than a computation?"""
    stripped = text.strip()
    return (stripped in ("nil", "t", "0", '""')
            or stripped.startswith("'") or stripped.startswith("("))


# --------------------------------------------------------------------------
# findings
# --------------------------------------------------------------------------


@dataclass
class Finding:
    check: str
    book: str
    line: int
    detail: str

    def render(self) -> str:
        return f"{self.check}: {self.book}:{self.line}: {self.detail}"


def static_findings(books: dict[str, list[Assertion]],
                    errors: dict[str, str]) -> list[Finding]:
    """What the source alone says, with no ACL2."""
    out: list[Finding] = []
    for book, error in sorted(errors.items()):
        out.append(Finding("unreadable", book, 0, error))

    # A predicate only ever asserted FALSE.  This is the owner-tests shape: a
    # broken recognizer makes every negative assertion pass, and no positive
    # assertion anywhere in the corpus would have noticed.
    positive: set[str] = set()
    negative: dict[str, list[Claim]] = collections.defaultdict(list)
    for assertions in books.values():
        for record in assertions:
            if record.audit:
                continue
            for claim in record.claims:
                name = claim.predicate
                if not recogniser(name):
                    continue
                (positive.add(name) if claim.positive
                 else negative[name].append(claim))
    for name in sorted(negative):
        if name in positive or name in VACUOUS_OVER_EMPTY:
            continue
        uses = negative[name]
        where = ", ".join(sorted({f"{c.book}:{c.line}" for c in uses})[:3])
        out.append(Finding(
            "predicate-never-anchored", uses[0].book, uses[0].line,
            f"`{name}` is asserted FALSE {len(uses)} times across the corpus "
            f"and never asserted TRUE anywhere, so a definition that is "
            f"constantly false satisfies every one of them ({where})"))

    # A form that cannot even be translated: the book does not run.
    names = mv_functions()
    for book, records in sorted(books.items()):
        for record in records:
            calls = multi_valued_calls(record.body, names)
            if calls:
                out.append(Finding(
                    "multi-valued-in-evaluation", book, record.line,
                    f"the body calls {', '.join(sorted(set(calls)))}, which "
                    f"returns an `mv`, outside `mv-list`; an assert-event "
                    f"body is translated for evaluation, so this form does "
                    f"NOT RUN.  Write `(nth n (mv-list k ...))`"))

    # An assertion that mentions nothing the tree defines is not a witness.
    defined = defined_names()
    for book, assertions in sorted(books.items()):
        for position, record in enumerate(assertions):
            if record.audit or mentions_defined(record.body, defined):
                continue
            # The corpus uses a trivially-true assertion as the PREMISE half
            # of a separating pair: `(equal (append '(97 98) '(99)) (append
            # '(97) '(98 99)))` says the two concatenations are the same, so
            # the next assertion -- that their tagged preimages differ --
            # separates something.  An isolated one separates nothing.
            following = assertions[position + 1: position + 2]
            if following and mentions_defined(following[0].body, defined):
                continue
            text = renderable(record.body) or "<unrenderable>"
            out.append(Finding(
                "no-subject", book, record.line,
                f"the body names nothing this tree defines and the next "
                f"assertion does not use it, so it exercises ACL2 and not "
                f"fn: {text[:100]}"))
    return out


_MV: set[str] | None = None


# Forms that legally receive several values, and the tail positions a
# multi-valued body can return from.
MV_CONTEXT = {"mv-list", "mv-let", "mv?-let", "mv-let*", "b*", "mv", "er-let*"}
TAIL = {"if": (2, 3), "prog2$": (2,), "the": (2,)}


def returns_mv(body: object) -> bool:
    """Can this body return several values?  Tail positions only.

    Anything looser flags a function that merely CONTAINS an `mv-let`:
    `fn-bs-fsync-file` binds two values inside and returns two, but
    `fn-bs-fence-file` binds two and returns one."""
    if not isinstance(body, list) or not body:
        return False
    name = head(body)
    if name == "mv":
        return True
    if name == "if":
        return any(returns_mv(item) for item in body[2:4])
    if name in ("let", "let*") and len(body) > 2:
        return returns_mv(body[-1])
    if name == "mv-let" and len(body) > 3:
        return returns_mv(body[-1])
    if name == "cond":
        return any(returns_mv(clause[-1]) for clause in body[1:]
                   if isinstance(clause, list) and clause)
    if name in ("case", "prog2$", "the"):
        return returns_mv(body[-1])
    return False


def mv_functions() -> set[str]:
    """Every `defun` in the tree whose body can return an `mv`, cached."""
    global _MV
    if _MV is None:
        names: set[str] = set()
        for directory in ("books", "tests/acl2"):
            for path in sorted((ROOT / directory).glob("*.lisp")):
                for form in ledger.read_forms(path.read_text(encoding="utf-8")):
                    if head(form) not in ("defun", "defund", "defun-nx"):
                        continue
                    if len(form) > 3 and isinstance(form[1], Sym) \
                            and any(returns_mv(item) for item in form[3:]):
                        names.add(str(form[1]))
        _MV = names
    return _MV


def multi_valued_calls(form: object, names: set[str],
                       parent: object = None) -> list[str]:
    """Calls of a multi-valued function that are not wrapped in `mv-list`.

    A `defconst` or an `assert-event` body is TRANSLATED FOR EVALUATION,
    which is single-valued, so a multi-valued call there is a signature
    mismatch and the form does not run at all.  `tests/acl2/peer-feed-tests`
    carried fifteen `(mv-nth n (fn-feed-...))` of exactly this shape and the
    book had never certified, so nothing had ever reported them (found by
    the feed lane, 2026-09-20).  The idiom that works is
    `(nth n (mv-list 2 ...))`.
    """
    found: list[str] = []
    if not isinstance(form, list) or not form:
        return found
    name = head(form)
    outer = head(parent)
    # A macro expands to something this reader cannot see, and the corpus
    # wraps these calls in one (`bst-res`, `bst-state` in byte-store-tests):
    # only a call whose parent is a FUNCTION is certainly single-valued.
    if (name in names and outer not in MV_CONTEXT
            and outer is not None and outer not in macro_names()
            and (outer == "mv-nth" or outer in defined_names()
                 or outer in ("equal", "not", "null", "car", "cdr", "nth",
                              "len", "append", "list", "consp", "member-equal"))):
        found.append(name)
    for item in form[1:] if name else form:
        found.extend(multi_valued_calls(item, names, form))
    return found


_COMMENTED: dict[str, str] | None = None


def commented_out() -> dict[str, str]:
    """Names that appear only inside a comment in `books/`, and where.

    A book records a theorem it could not close by commenting the event out
    with a reason (`books/bp-fragment-invariants.lisp:246`).  A test book
    that cites such a name is not stale: it is carrying a witness for an
    OPEN theorem, which is a different thing to say and a worse one to leave
    unsaid.
    """
    global _COMMENTED
    if _COMMENTED is None:
        found: dict[str, str] = {}
        token = re.compile(r"\bfn-[a-z0-9-]*[a-z0-9]")
        for path in sorted((ROOT / "books").glob("*.lisp")):
            for number, text in enumerate(
                    path.read_text(encoding="utf-8").splitlines(), 1):
                if ";" not in text:
                    continue
                for name in token.findall(text[text.index(";"):]):
                    found.setdefault(
                        name, f"{path.relative_to(ROOT).as_posix()}:{number}")
        _COMMENTED = found
    return _COMMENTED


_MACROS: set[str] | None = None


def macro_names() -> set[str]:
    """Every `defmacro` name in the tree, cached: a macro hides its shape."""
    global _MACROS
    if _MACROS is None:
        found: set[str] = set()
        for book in ledger.load_tree().books.values():
            found |= book.macros
        _MACROS = found
    return _MACROS


_LITERALS: set[str] | None = None
STRING = re.compile(r'"((?:[^"\\]|\\.)*)"')


def string_literals() -> set[str]:
    """Every string literal in the tree's Lisp sources, cached."""
    global _LITERALS
    if _LITERALS is None:
        found: set[str] = set()
        for directory in ("books", "tests/acl2", "host", "host/native"):
            for path in sorted((ROOT / directory).glob("*.lisp")):
                found |= set(STRING.findall(path.read_text(encoding="utf-8")))
        _LITERALS = found
    return _LITERALS


_DEFINED: set[str] | None = None


def defined_names() -> set[str]:
    """Every name `books/` and `tests/acl2/` bring into a world, cached."""
    global _DEFINED
    if _DEFINED is None:
        tree = ledger.load_tree()
        names: set[str] = set()
        for book in tree.books.values():
            names |= book.definitions
            names |= {theorem.name for theorem in book.theorems}
        _DEFINED = names
    return _DEFINED


CONNECTIVES = {"implies", "let", "let*", "if", "cond", "quote", "or", "and",
               "not", "null", "case", "mv-let", "b*"}


def recogniser(name: str | None) -> bool:
    """Is this name a recogniser of this tree's own?

    The anchoring question is about PREDICATES: a recogniser that is false of
    everything satisfies every negative assertion made of it.  An accessor
    that returns `NIL` (`(null (fn-own-conns o))`) is a different claim and
    reads as a negation only because `null` looks like one, so the check is
    restricted to the tree's `...p` convention.
    """
    return bool(name) and (name.endswith("p") and name not in CONNECTIVES
                           and name not in EQUALITIES
                           and name in defined_names())


def mentions_defined(form: object, defined: set[str]) -> bool:
    """Does this term reach any name this tree defines?

    An assertion over ACL2 primitives alone -- `(natp 0)`, `(not (consp
    nil))`, `(equal (append '(1 2) '(3)) (append '(1) '(2 3)))` -- exercises
    the prover, not fn, so it is a witness for nothing in the registry.
    """
    if isinstance(form, Sym):
        return str(form) in defined or defconst_name(form)
    if isinstance(form, list):
        return any(mentions_defined(item, defined) for item in form)
    return False


def evaluated_findings(books: dict[str, list[Assertion]],
                       saved: dict[str, dict]) -> list[Finding]:
    """What the values say."""
    out: list[Finding] = []
    for book, assertions in sorted(books.items()):
        run = saved.get(book)
        if run is None:
            continue
        # A `TOP-LEVEL` error is one of THIS TOOL's probe forms, not the
        # book's: the book's own forms are named (DEFCONST, ASSERT-EVENT).
        # Counting them made ten clean books look as if they did not run.
        errors = [e for e in run.get("errors", []) if e["form"] != "TOP-LEVEL"]
        if errors:
            first = errors[0]
            kinds = collections.Counter(e["form"] for e in errors)
            out.append(Finding(
                "book-does-not-run", book, 0,
                f"the survey saw ACL2 refuse {len(errors)} form(s); the "
                f"first is {first['kind'] or 'an error'} in "
                f"{first['form'] or '?'}. Everything a refused form defines "
                f"is MISSING below it, so the assertions after it are not "
                f"weak, they are INERT ("
                + ", ".join(f"{n}x {f}" for f, n in kinds.most_common(4)) + ")"))
        if run["prefix"] != "ok" or run["include_failed"]:
            out.append(Finding(
                "prefix-failed", book, 0,
                "the book's own includes did not load, so nothing below was "
                "evaluated and this book is UNSURVEYED"))
            continue
        values = run["values"]
        by_index = {record.index: record for record in assertions}
        for key, text in sorted(run["probes"].items()):
            index = int(re.match(r"a(\d+)", key).group(1))
            record = by_index.get(index)
            if record is None:
                continue
            value = values.get(key)
            if key.endswith("h"):
                if degenerate(value) == "nil":
                    out.append(Finding(
                        "vacuous-implies", book, record.line,
                        f"the hypothesis `{text[:80]}` is NIL, so the "
                        f"implication holds whatever its conclusion says"))
                continue
            if re.fullmatch(r"a\d+", key):
                if value is None:
                    out.append(Finding(
                        "unevaluable", book, record.line,
                        f"the body did not evaluate: {text[:100]}"))
                elif value.strip() == "NIL":
                    out.append(Finding(
                        "assertion-false", book, record.line,
                        f"the body evaluates to NIL in this world: {text[:100]}"))
                continue
            reason = degenerate(value)
            if reason is None or literal(text):
                continue
            out.append(Finding(
                "degenerate-subject", book, record.line,
                f"`{text[:80]}` = {value.strip()[:40]} ({reason}); the claim "
                f"is `{(renderable(record.body) or '')[:90]}`"))

        # Both sides of an equality degenerate: the S4-1 shape, where the
        # delta compared equal to the expectation because both were empty.
        for record in assertions:
            for claim in record.claims:
                if claim.predicate not in EQUALITIES or len(claim.term) != 3:
                    continue
                sides = [values.get(f"a{record.index}c{claim.clause}s{n}")
                         for n in range(len(subjects(claim.term)))]
                if len(sides) == 2 and all(degenerate(s) for s in sides):
                    out.append(Finding(
                        "both-sides-degenerate", book, record.line,
                        f"both sides of the equality are "
                        f"{sides[0].strip()[:30]}; the claim distinguishes "
                        f"nothing: {(renderable(claim.term) or '')[:100]}"))
        # A claim that holds of an empty collection.
        for record in assertions:
            for claim in record.claims:
                position = VACUOUS_OVER_EMPTY.get(claim.predicate or "")
                if position is None:
                    continue
                ordered = subjects(claim.term)
                wanted = [n for n, (term, _) in enumerate(ordered)
                          if term is claim.term[position + 1]]
                if not wanted:
                    continue
                value = values.get(f"a{record.index}c{claim.clause}s{wanted[0]}")
                if degenerate(value) == "nil":
                    out.append(Finding(
                        "empty-collection", book, record.line,
                        f"`{claim.predicate}` is applied to an EMPTY "
                        f"collection, so the claim holds of nothing: "
                        f"{(renderable(claim.term) or '')[:100]}"))

    out += never_true(books, saved)
    return out


def never_true(books: dict[str, list[Assertion]],
               saved: dict[str, dict]) -> list[Finding]:
    """Recognisers that no evaluated claim in the corpus ever made TRUE.

    The static `predicate-never-anchored` check asks whether any test ASSERTS
    the recogniser positively.  This one asks the stronger question the
    owner-tests defect needed: over every claim the corpus evaluates, did the
    recogniser ever come back non-`NIL`?  `fn-own-conn-boundedp` was false of
    every connection for a fortnight and the suite stayed green.
    """
    seen_true: set[str] = set()
    seen_false: dict[str, list[tuple[str, int, str]]] = collections.defaultdict(list)
    for book, assertions in books.items():
        run = saved.get(book)
        if run is None or run["prefix"] != "ok":
            continue
        for record in assertions:
            if record.audit:
                continue
            for claim in record.claims:
                if not recogniser(claim.predicate):
                    continue
                value = run["values"].get(f"a{record.index}c{claim.clause}t")
                if value is None:
                    continue
                if value.strip() == "NIL":
                    seen_false[claim.predicate].append(
                        (book, record.line, renderable(claim.term) or ""))
                else:
                    seen_true.add(claim.predicate)
    out: list[Finding] = []
    for name in sorted(seen_false):
        if name in seen_true:
            continue
        uses = seen_false[name]
        out.append(Finding(
            "recogniser-never-true", uses[0][0], uses[0][1],
            f"`{name}` came back NIL at all {len(uses)} evaluated claims in "
            f"the corpus and non-NIL at none, so a definition that is "
            f"constantly false passes every one: {uses[0][2][:90]}"))
    return out


# --------------------------------------------------------------------------
# the registry cross-check
# --------------------------------------------------------------------------


def hypotheses_of(statement: object) -> list[object]:
    """The hypotheses of `(implies (and h1 ... hn) c)`, or of `(implies h c)`."""
    if head(statement) != "implies" or len(statement) != 3:
        return []
    antecedent = statement[1]
    if head(antecedent) == "and":
        return list(antecedent[1:])
    return [antecedent]


def cited_sections(name: str) -> list[tuple[str, int, int]]:
    """Where a test book cites `name` in a comment, and how many
    `assert-event`s follow before the next citation of another keystone.

    The corpus writes teeth as `; <theorem-name>` and then the witnesses, so
    the assertions between one citation and the next are the teeth for that
    theorem.  This is a CONVENTION, not a declaration: the count below is a
    heuristic and the finding says so.  A macro-generated `must-fail` in the
    same span counts too, on the same line-range convention as a literal
    `(assert-event` -- `macro_teeth_for_book`'s docstring has the shapes.
    """
    out: list[tuple[str, int, int]] = []
    macro_by_book = macro_teeth_by_book()
    for path, lines, marks in _sections():
        teeth = macro_by_book.get(path, [])
        for index, (number, cited) in enumerate(marks):
            if cited != name:
                continue
            stop = marks[index + 1][0] if index + 1 < len(marks) else len(lines)
            body = "\n".join(lines[number:stop])
            macro_musts = sum(1 for tooth in teeth if tooth.kind == "must-fail"
                              and number < tooth.line <= stop)
            out.append((path, number, body.count("(assert-event") + macro_musts))
    return out


_SECTIONS: list | None = None


def _sections() -> list:
    """Every test book as (path, lines, [(line, keystone cited)])."""
    global _SECTIONS
    if _SECTIONS is None:
        keystones = {event for target in json.loads(
            PROOFS.read_text(encoding="utf-8"))["proofs"]
            for event in target.get("events", [])}
        token = re.compile(r"\bfn-[a-z0-9-]*[a-z0-9]")
        found = []
        for path in sorted(TESTS.glob("*.lisp")):
            lines = path.read_text(encoding="utf-8").splitlines()
            marks = []
            for number, text in enumerate(lines, 1):
                if ";" not in text:
                    continue
                for cited in token.findall(text[text.index(";"):]):
                    if cited in keystones:
                        marks.append((number, cited))
                        break
            found.append((path.relative_to(ROOT).as_posix(), lines, marks))
        _SECTIONS = found
    return _SECTIONS


def hypothesis_coverage() -> tuple[int, int]:
    """(keystones with 2+ hypotheses, how many a test book cites by name).

    AGENTS.md wants one violating value per hypothesis for ALL of the first
    number.  The tool can only look where a test book says which keystone it
    is witnessing, which is the second.  The gap is the honest figure and it
    is printed rather than turned into findings nobody can act on one by one.
    """
    tree = ledger.load_tree()
    statements = {theorem.name: theorem.statement
                  for book in tree.books.values() for theorem in book.theorems}
    registry = json.loads(PROOFS.read_text(encoding="utf-8"))
    total = cited = 0
    for target in registry["proofs"]:
        for event in target.get("events", []):
            if len(hypotheses_of(statements.get(event))) < 2:
                continue
            total += 1
            cited += bool(cited_sections(event))
    return total, cited


def hypothesis_teeth() -> list[Finding]:
    """Keystones whose cited section has fewer witnesses than hypotheses.

    AGENTS.md: "one `must-fail` case per hypothesis showing the conclusion
    fails without it".  A hypothesis with no violating value anywhere is a
    hypothesis that is not doing work -- the feed lane deleted one on
    2026-09-20 after finding the tooth asserted the OPPOSITE of what the
    machine does.  This counts; it cannot tell WHICH hypothesis a witness is
    for, so it is a floor and not a verdict.
    """
    tree = ledger.load_tree()
    statements = {theorem.name: theorem.statement
                  for book in tree.books.values() for theorem in book.theorems}
    registry = json.loads(PROOFS.read_text(encoding="utf-8"))
    out: list[Finding] = []
    for target in registry["proofs"]:
        for event in target.get("events", []):
            wanted = len(hypotheses_of(statements.get(event)))
            if wanted < 2:
                continue  # one hypothesis: the negative assertion is the case
            sections = cited_sections(event)
            if not sections:
                continue  # keystone-without-witness already says this
            book, line, witnesses = max(sections, key=lambda s: s[2])
            if witnesses >= wanted:
                continue
            out.append(Finding(
                "hypotheses-without-teeth", book, line,
                f"`{event}` ({target['id']}) has {wanted} hypotheses and the "
                f"section citing it carries {witnesses} assert-event(s); "
                f"AGENTS.md wants one violating value per hypothesis. "
                f"Section boundaries are the `; <name>` convention, so this "
                f"is a floor, not a verdict"))
    return out


def registry_findings(books: dict[str, list[Assertion]]) -> list[Finding]:
    """Keystones with no witness, and cited names the tree no longer defines."""
    out: list[Finding] = []
    tree = ledger.load_tree()
    defined: set[str] = set()
    for book in tree.books.values():
        defined |= book.definitions
        defined |= {theorem.name for theorem in book.theorems}
    # A comment cites a defconst without its stars (`*fn-prov-max-field*' is
    # written `fn-prov-max-field' in prose), and `fn-defrecord' generates
    # `<record>-internals' from the record name.
    for host in tree.hosts.values():
        defined |= host.defines | host.macros
    defined |= {name.strip("*") for name in list(defined)}
    defined |= {name + "-internals" for name in list(defined)}

    # Every `fn-` token a test book's PROSE cites.  The reader drops comments,
    # so this reads the raw text; a citation the tree no longer defines is a
    # witness whose theorem has gone.
    token = re.compile(r"\bfn-[a-z0-9-]*[a-z0-9]")
    for path in sorted(TESTS.glob("*.lisp")):
        book = path.relative_to(ROOT).as_posix()
        lines = path.read_text(encoding="utf-8").splitlines()
        for number, text in enumerate(lines, 1):
            if ";" not in text:
                continue
            comment = text[text.index(";"):]
            for match in token.finditer(comment):
                name = match.group(0)
                if name in defined or name.count("-") < 3:
                    continue
                # Prose abbreviates a family by its shared prefix
                # (`fn-cpc-decode-rejects` for four `-mismatched-*` theorems)
                # and drops a `-by-definition` suffix.  Neither is stale.
                if any(other.startswith(name) for other in defined):
                    continue
                # A format string that reads like a name
                # (`"fn-store-experiment-5"`, the on-disk store format) is
                # not a theorem citation.
                if any(name in text for text in string_literals()):
                    continue
                # A long name broken across two comment lines: the token ends
                # at a hyphen with nothing after it, and the rest is on the
                # next line.  `fn-served-run-is-the-' in owner-tests is one.
                if comment[match.end():].rstrip() == "-":
                    continue
                where = commented_out().get(name)
                if where:
                    # A test book that SAYS the theorem is open has already
                    # done what this check asks for.
                    nearby = "\n".join(lines[number - 1:number + 2])
                    if "OPEN" in nearby:
                        continue
                    out.append(Finding(
                        "witness-for-an-open-theorem", book, number,
                        f"the comment cites `{name}`, which exists only as a "
                        f"COMMENTED-OUT event at {where}: the witness below "
                        f"is evidence for a theorem that is not proved, and "
                        f"the test book does not say so"))
                    continue
                out.append(Finding(
                    "stale-citation", book, number,
                    f"the comment cites `{name}`, which nothing in the tree "
                    f"defines and no comment in `books/` mentions either"))

    out += hypothesis_teeth()

    # A keystone with no witness in any test book.
    mentioned: dict[str, set[str]] = collections.defaultdict(set)
    for path in sorted(TESTS.glob("*.lisp")):
        book = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        for name in set(token.findall(text)):
            mentioned[name].add(book)
    registry = json.loads(PROOFS.read_text(encoding="utf-8"))
    for target in registry["proofs"]:
        missing = [event for event in target.get("events", [])
                   if event not in mentioned]
        if not missing:
            continue
        out.append(Finding(
            "keystone-without-witness", "planning/proofs.json", 0,
            f"{target['id']} ({target['status']}): {len(missing)} of "
            f"{len(target['events'])} events are named in no test book: "
            + ", ".join(sorted(missing)[:6])
            + (" ..." if len(missing) > 6 else "")))
    return out


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------


def load_books(paths: list[Path]) -> tuple[dict[str, list[Assertion]],
                                           dict[str, list[str]], dict[str, str]]:
    assertions: dict[str, list[Assertion]] = {}
    constants: dict[str, list[str]] = {}
    errors: dict[str, str] = {}
    for path in paths:
        book = path.relative_to(ROOT).as_posix()
        found, consts, error = read_book(path)
        if error:
            errors[book] = error
            continue
        assertions[book] = found
        constants[book] = consts
    return assertions, constants, errors


def test_books(selection: list[str]) -> list[Path]:
    if not selection:
        return sorted(TESTS.glob("*.lisp"))
    out = []
    for name in selection:
        path = Path(name)
        if not path.is_absolute():
            path = ROOT / name
        if path.suffix != ".lisp":
            path = path.with_suffix(".lisp")
        out.append(path.resolve())
    return out


def top_of(key: str, assertions: list[Assertion]) -> int:
    """The top-level form a probe's assertion sits in."""
    index = int(re.match(r"a(\d+)", key).group(1))
    return next(r.top for r in assertions if r.index == index)


def counts(assertions: dict[str, list[Assertion]]) -> dict[str, int]:
    every = [record for records in assertions.values() for record in records
             if record.kind == "assert-event"]
    return {
        "books": len(assertions),
        "assertions": len(every),
        "guard_audits": sum(1 for record in every if record.audit),
        "witnesses": sum(1 for record in every if not record.audit),
    }


# --------------------------------------------------------------------------
# suggesting an anchor
# --------------------------------------------------------------------------


def anchor_probes(book: str, assertions: list[Assertion],
                  constants: list[str], wanted: set[str]) -> list[Probe]:
    """`(R c)` for every unary recogniser R flagged in this book and every
    constant c it defines.

    A recogniser the corpus only ever asserts FALSE is satisfied by a
    definition that is false of everything, which is how `owner-tests` pinned
    `fn-own-conn-boundedp` for a fortnight.  The repair is one positive
    assertion, and the constant it names has to be DERIVED, not typed: this
    finds the constants of the book that the recogniser actually accepts.
    """
    out: list[Probe] = []
    for record in assertions:
        if record.kind != "assert-event" or record.audit:
            continue
        for claim in record.claims:
            name = claim.predicate
            if name not in wanted or claim.positive:
                continue
            if not isinstance(claim.term, list) or len(claim.term) != 2:
                continue  # arity 1 only: an n-ary recogniser needs its tuple
            for number, constant in enumerate(constants):
                out.append(Probe(
                    key=f"anchor:{name}:{number}", book=book, line=record.line,
                    text=f"({name} {constant})", role="anchor", claim=-1,
                    note=constant))
    seen: dict[str, Probe] = {}
    for probe in out:
        seen.setdefault(probe.key, probe)
    return list(seen.values())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("books", nargs="*",
                        help="test books to consider (default: all)")
    parser.add_argument("--evaluate", action="store_true",
                        help="run one ACL2 per book and save the probe values")
    parser.add_argument("--report", action="store_true",
                        help="static findings plus the saved probe values")
    parser.add_argument("--summary", action="store_true",
                        help="counts only, one line per check")
    parser.add_argument("--table", action="store_true",
                        help="every macro-generated must-fail/witness, and "
                             "each book's literal must-fails beside them, "
                             "GEN marking which is which")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--values", default=str(VALUES),
                        help=f"where the probe values live (default {VALUES})")
    parser.add_argument("--timeout", type=int, default=600,
                        help="per-book ACL2 timeout in seconds")
    parser.add_argument("--logs", help="keep each book's raw ACL2 log here")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 when there is any finding")
    parser.add_argument("--anchors", action="store_true",
                        help="with --evaluate: also probe every flagged unary "
                             "recogniser against every constant its book "
                             "defines, and print the ones it accepts")
    arguments = parser.parse_args(argv)

    paths = test_books(arguments.books)
    assertions, constants, errors = load_books(paths)
    values_path = Path(arguments.values)

    if arguments.anchors and arguments.evaluate:
        wanted = {f.detail.split("`")[1]
                  for f in static_findings(assertions, errors)
                  if f.check == "predicate-never-anchored"}
        for path in paths:
            book = path.relative_to(ROOT).as_posix()
            probe_list = anchor_probes(book, assertions.get(book, []),
                                       constants.get(book, []), wanted)
            if not probe_list:
                continue
            where = {probe.key: len(book_text(path)) - 1 for probe in probe_list}
            run = evaluate(path, probe_list, arguments.timeout, None,
                           book_text(path), where)
            for probe in probe_list:
                value = run["values"].get(probe.key)
                if value and value.strip() != "NIL":
                    print(f"anchor {book}: {probe.text} = {value.strip()[:40]}")
        return 0

    if arguments.evaluate:
        saved = ({} if not values_path.exists()
                 else json.loads(values_path.read_text(encoding="utf-8")))
        for path in paths:
            book = path.relative_to(ROOT).as_posix()
            if book not in assertions:
                continue
            probe_list = probes_for(assertions[book])
            keep = (Path(arguments.logs) / (path.stem + ".log")
                    if arguments.logs else None)
            where = {probe.key: top_of(probe.key, assertions[book])
                     for probe in probe_list}
            print(f"teeth: {book}: {len(probe_list)} probes", flush=True)
            try:
                run = evaluate(path, probe_list, arguments.timeout, keep,
                               book_text(path), where)
            except Exception as error:  # one book must not end the sweep
                print(f"  ERROR {error!r}", flush=True)
                run = {"book": book, "exit": -1, "prefix": "failed",
                       "include_failed": False, "values": {},
                       "probes": {p.key: p.text for p in probe_list},
                       "error": repr(error)}
            saved[book] = run
            print(f"  prefix {run['prefix']}, exit {run['exit']}, "
                  f"{len(run['values'])} values", flush=True)
            values_path.parent.mkdir(parents=True, exist_ok=True)
            values_path.write_text(json.dumps(saved, indent=1, sort_keys=True),
                                   encoding="utf-8")
        return 0

    findings = static_findings(assertions, errors)
    if not arguments.books:  # the registry checks are corpus-wide by nature
        findings += registry_findings(assertions)
    saved: dict[str, dict] = {}
    if arguments.report and values_path.exists():
        saved = json.loads(values_path.read_text(encoding="utf-8"))
        findings += evaluated_findings(assertions, saved)

    macro_teeth = (macro_teeth_by_book() if not arguments.books
                  else macro_teeth_for_paths(paths))
    totals = counts(assertions)
    by_check = collections.Counter(finding.check for finding in findings)
    if arguments.json:
        print(json.dumps({"counts": totals, "by_check": dict(by_check),
                          "evaluated_books": sorted(saved),
                          "macro_teeth": macro_teeth_totals(macro_teeth),
                          "findings": [vars(f) for f in findings]},
                         indent=1, sort_keys=True))
    elif arguments.table:
        print("\n".join(macro_table(macro_teeth)))
    elif arguments.summary:
        print(f"teeth: {totals['assertions']} assert-events in "
              f"{totals['books']} test books "
              f"({totals['guard_audits']} guard-world audits, "
              f"{totals['witnesses']} witnesses)"
              + (f", {len(saved)} books evaluated" if saved else
                 ", values not evaluated (run --evaluate)"))
        macro_totals = macro_teeth_totals(macro_teeth)
        if macro_totals["must_fails"] or macro_totals["witnesses"]:
            print(f"teeth: {macro_totals['must_fails']} must-fail(s) and "
                  f"{macro_totals['witnesses']} witness(es) come from "
                  f"{macro_totals['macros']} defmacro(s) in "
                  f"{macro_totals['books']} test book(s), invisible to a "
                  f"literal count of `must-fail`; --table marks them apart "
                  f"from literal ones")
        total, cited = hypothesis_coverage()
        print(f"teeth: {total} keystones have two or more hypotheses and a "
              f"test book names {cited} of them, so one-must-fail-per-"
              f"hypothesis is unchecked for {total - cited}")
        for check, number in sorted(by_check.items()):
            print(f"teeth: {number} {check}")
        if not by_check:
            print("teeth: no findings")
    else:
        for finding in findings:
            print(finding.render())
        print()
        print(f"{totals['assertions']} assert-events, "
              f"{totals['witnesses']} witnesses, {len(findings)} findings")
        for check, number in sorted(by_check.items()):
            print(f"  {number:5d}  {check}")
    return 1 if (arguments.strict and findings) else 0


if __name__ == "__main__":
    sys.exit(main())
