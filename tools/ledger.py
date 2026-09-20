#!/usr/bin/env python3
"""Generate fn's assurance ledger from the books, and check the proof registry.

Counts in fn are generated, never typed.  This tool reads ``books/*.lisp``,
``tests/acl2/*.lisp`` and the ``ld``ed host files with the s-expression reader
in this file.  It is not the
Lisp reader: nothing is interned, evaluated, or macro-expanded, so reading a
book cannot run a book.  The books are our own source, but the rule that
parsing never invokes the reader holds for them too.

What it reports per book: every ``defthm``, ``defun``, ``verify-guards``,
``must-fail``, ``assert-event`` and ``include-book``; the guard status of every
function; the theorems whose *shape* disqualifies them as registry evidence;
and, for the host files, every name they use that nothing they load defines.

What it checks (``--check``): that every theorem cited by
``planning/proof-events.json`` exists, is not SUSPECT, and lives in a book
inside the Makefile root closure; that ``planning/proofs.json`` ``events``
match the curated map; and that ``planning/ledger.json`` and
``planning/ledger.md`` are not stale.

Usage:
    python3 tools/ledger.py            # report the ledger on stdout
    python3 tools/ledger.py --write    # regenerate the three generated files
    python3 tools/ledger.py --check    # fail on drift; used by `make check`
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEDGER_JSON = ROOT / "planning/ledger.json"
LEDGER_MD = ROOT / "planning/ledger.md"
PROOF_EVENTS = ROOT / "planning/proof-events.json"
PROOFS = ROOT / "planning/proofs.json"


# --------------------------------------------------------------------------
# s-expression reader
# --------------------------------------------------------------------------


class Sym(str):
    """A symbol.  A Lisp string literal reads as a plain ``str``; this is not."""

    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"Sym({str.__repr__(self)})"


DOT = Sym(".")
DELIMITERS = set("()'\"`,; \t\n\r\f")


class ReadError(ValueError):
    """The source is not readable as s-expressions."""


class Reader:
    """Read s-expressions without interning, evaluating, or expanding."""

    def __init__(self, source: str) -> None:
        self.source = source
        self.pos = 0

    def line(self, position: int) -> int:
        return self.source.count("\n", 0, position) + 1

    def skip_space(self) -> None:
        source, n = self.source, len(self.source)
        while self.pos < n:
            c = source[self.pos]
            if c.isspace():
                self.pos += 1
            elif c == ";":
                newline = source.find("\n", self.pos)
                self.pos = n if newline < 0 else newline + 1
            elif source[self.pos:self.pos + 2] == "#|":
                depth, self.pos = 1, self.pos + 2
                while self.pos < n and depth:
                    pair = source[self.pos:self.pos + 2]
                    if pair == "#|":
                        depth, self.pos = depth + 1, self.pos + 2
                    elif pair == "|#":
                        depth, self.pos = depth - 1, self.pos + 2
                    else:
                        self.pos += 1
                if depth:
                    raise ReadError("unterminated block comment")
            else:
                return

    def top_level(self) -> list[tuple[object, int]]:
        """Every top-level form, paired with the line it starts on."""
        forms: list[tuple[object, int]] = []
        while True:
            self.skip_space()
            if self.pos >= len(self.source):
                return forms
            line = self.line(self.pos)
            forms.append((self.form(), line))

    def form(self) -> object:
        self.skip_space()
        source, n = self.source, len(self.source)
        if self.pos >= n:
            raise ReadError("unexpected end of source")
        c = source[self.pos]
        if c == "(":
            self.pos += 1
            return self.rest_of_list()
        if c == ")":
            raise ReadError(f"unbalanced close parenthesis at line {self.line(self.pos)}")
        if c == '"':
            return self.string()
        if c == "'":
            self.pos += 1
            return [Sym("quote"), self.form()]
        if c == "`":
            self.pos += 1
            return [Sym("quasiquote"), self.form()]
        if c == ",":
            self.pos += 1
            if self.pos < n and source[self.pos] == "@":
                self.pos += 1
                return [Sym("unquote-splicing"), self.form()]
            return [Sym("unquote"), self.form()]
        if source[self.pos:self.pos + 2] == "#'":
            self.pos += 2
            return [Sym("function"), self.form()]
        if source[self.pos:self.pos + 2] == "#\\":
            self.pos += 2
            start = self.pos
            self.pos += 1  # the character itself may be a delimiter
            while self.pos < n and source[self.pos] not in DELIMITERS:
                self.pos += 1
            return Sym("#\\" + source[start:self.pos])
        if source[self.pos:self.pos + 2] == "#(":
            self.pos += 2
            return [Sym("vector")] + self.rest_of_list()
        return self.atom()

    def rest_of_list(self) -> list:
        items: list = []
        while True:
            self.skip_space()
            if self.pos >= len(self.source):
                raise ReadError("unterminated list")
            if self.source[self.pos] == ")":
                self.pos += 1
                return items
            items.append(self.form())

    def string(self) -> str:
        source, n = self.source, len(self.source)
        self.pos += 1
        out: list[str] = []
        while self.pos < n:
            c = source[self.pos]
            if c == "\\":
                if self.pos + 1 >= n:
                    raise ReadError("unterminated string escape")
                out.append(source[self.pos + 1])
                self.pos += 2
            elif c == '"':
                self.pos += 1
                return "".join(out)
            else:
                out.append(c)
                self.pos += 1
        raise ReadError("unterminated string")

    def atom(self) -> object:
        source, n = self.source, len(self.source)
        out: list[str] = []
        bars = False
        while self.pos < n:
            c = source[self.pos]
            if c == "|":
                bars = not bars
                self.pos += 1
                continue
            if c == "\\":
                if self.pos + 1 < n:
                    out.append(source[self.pos + 1])
                self.pos += 2
                continue
            if not bars and (c in DELIMITERS or source[self.pos:self.pos + 2] == "#|"):
                break
            out.append(c)
            self.pos += 1
        text = "".join(out)
        if not text:
            raise ReadError(f"empty atom at line {self.line(self.pos)}")
        return number(text) if is_number(text) else Sym(text.lower())


NUMBER = re.compile(r"[+-]?(?:\d+/\d+|\d*\.\d+(?:[eE][+-]?\d+)?|\d+\.?(?:[eE][+-]?\d+)?)\Z")


def is_number(text: str) -> bool:
    return bool(NUMBER.match(text))


def number(text: str) -> object:
    try:
        return int(text)
    except ValueError:
        pass
    if "/" in text:
        return text  # an exact rational; compared structurally, never evaluated
    try:
        return float(text)
    except ValueError:  # pragma: no cover - NUMBER admits nothing else
        return text


def read_forms(source: str) -> list:
    """Every top-level form of ``source``."""
    return [form for form, _line in Reader(source).top_level()]


# --------------------------------------------------------------------------
# shape helpers
# --------------------------------------------------------------------------


def head(form: object) -> str | None:
    """The symbol at the head of a call, or ``None``."""
    if isinstance(form, list) and form and isinstance(form[0], Sym):
        return str(form[0])
    return None


def keyword_plist(items: list) -> dict[str, object]:
    """Keyword arguments in a tail, first occurrence winning."""
    result: dict[str, object] = {}
    index = 0
    while index + 1 < len(items):
        key = items[index]
        if isinstance(key, Sym) and str(key).startswith(":"):
            result.setdefault(str(key), items[index + 1])
            index += 2
        else:
            index += 1
    return result


def conjuncts(form: object) -> list:
    """Flatten a top-level ``and``."""
    if head(form) == "and":
        out: list = []
        for item in form[1:]:
            out.extend(conjuncts(item))
        return out
    return [form]


def split_implication(statement: object) -> tuple[list, object]:
    """``(implies H C)`` as (hypotheses, conclusion); nested implications merge."""
    hypotheses: list = []
    current = statement
    while head(current) == "implies" and len(current) == 3:
        hypotheses.extend(conjuncts(current[1]))
        current = current[2]
    return hypotheses, current


def calls(form: object, found: set[str] | None = None) -> set[str]:
    """Every symbol in function position, quoted subforms excluded."""
    found = set() if found is None else found
    if not isinstance(form, list) or not form:
        return found
    if head(form) == "quote":
        return found
    if isinstance(form[0], Sym):
        found.add(str(form[0]))
    for item in form[1:] if isinstance(form[0], Sym) else form:
        calls(item, found)
    return found


def substitute(form: object, bindings: dict[str, object]) -> object:
    """Replace free variable occurrences.  Binding forms are not tracked; see
    ``docs/proofs.md`` for what that costs the suspect detector."""
    if isinstance(form, Sym):
        return bindings.get(str(form), form)
    if isinstance(form, list):
        if head(form) == "quote":
            return form
        return [substitute(item, bindings) for item in form]
    return form


def same(left: object, right: object) -> bool:
    """Structural equality that keeps symbols and string literals distinct."""
    if isinstance(left, Sym) != isinstance(right, Sym):
        return False
    if isinstance(left, list) and isinstance(right, list):
        return len(left) == len(right) and all(same(a, b) for a, b in zip(left, right))
    if isinstance(left, list) or isinstance(right, list):
        return False
    return type(left) is type(right) and left == right


REFLEXIVE = {"equal", "iff", "=", "subsetp", "subsetp-equal", "fn-subsetp"}


# --------------------------------------------------------------------------
# book model
# --------------------------------------------------------------------------


@dataclass
class Function:
    name: str
    book: str
    line: int
    formals: list
    body: object
    declared_guard: bool
    verify_guards_decl: str | None
    verified_by_event: bool = False
    local: bool = False
    # `:mode :program`: no definitional axiom, so no rule and nothing to
    # export.  Macro plumbing (`books/defrecord.lisp`) is written this way.
    program: bool = False
    # Emitted by `fn-defrecord`, not written in the file.  The hand-written
    # record lint reads the source, so it must not see the macro's output.
    generated: bool = False

    @property
    def guard_status(self) -> str:
        if self.verified_by_event or self.verify_guards_decl == "t":
            return "verified"
        if self.verify_guards_decl == "nil":
            return "declared-off"
        return "default-guarded" if self.declared_guard else "default-unguarded"


@dataclass
class Theorem:
    name: str
    book: str
    line: int
    statement: object
    hints: object
    rest: list
    local: bool = False
    disabled: bool = False  # defthmd


@dataclass
class Book:
    path: str
    theorems: list[Theorem] = field(default_factory=list)
    functions: list[Function] = field(default_factory=list)
    verify_guards: list[str] = field(default_factory=list)
    includes: list[str] = field(default_factory=list)
    system_includes: list[str] = field(default_factory=list)
    assert_events: int = 0
    must_fails: int = 0
    defconsts: int = 0
    defmacros: int = 0
    encapsulates: int = 0
    read_error: str | None = None
    # Rule names a non-local top-level ``in-theory`` turns off.  A book's
    # export policy is what it leaves enabled, so only these count.
    disabled_rules: set[str] = field(default_factory=set)
    # ``deftheory`` name -> its defining expression, and the non-local
    # top-level ``in-theory`` expressions, both resolved once the whole book
    # has been read: a withdrawal may name a theory defined anywhere above it.
    theories: dict[str, object] = field(default_factory=dict)
    in_theory_forms: list[object] = field(default_factory=list)
    # Each ``must-fail`` as (line, arguments), for the teeth-form lint.
    must_fail_forms: list[tuple[int, list]] = field(default_factory=list)
    # Each non-local ``(include-book "x")`` as (line, reference), for the
    # include-hygiene lint: a local include costs the includer nothing.
    nonlocal_includes: list[tuple[int, str]] = field(default_factory=list)
    # Every name this book brings into a world that includes it, for the
    # host-names lint.  A ``local`` definition is counted too: over-counting
    # here can only silence a warning, and the lint is deliberately quiet.
    definitions: set[str] = field(default_factory=set)
    # The ``defmacro`` subset of ``definitions``: see ``macro_names``.
    macros: set[str] = field(default_factory=set)


TRANSPARENT = {"local", "progn", "progn!", "with-output", "defsection", "defsection-progn"}
SUPPRESSING = {"must-fail", "must-fail!", "must-succeed", "must-succeed*",
               "must-fail-with-error", "must-fail-with-soft-error",
               "must-fail-with-hard-error", "must-not-prove", "must-prove",
               "thm"}


def declared(rest: list) -> tuple[bool, str | None]:
    """``(:guard ...)`` presence and the ``:verify-guards`` setting of a defun."""
    has_guard = False
    setting: str | None = None
    for item in rest:
        if head(item) != "declare":
            continue
        for declaration in item[1:]:
            if head(declaration) == "type":
                has_guard = True
            if head(declaration) != "xargs":
                continue
            options = keyword_plist(declaration[1:])
            if ":guard" in options:
                # Any explicit guard, `t` included: under the default
                # set-verify-guards-eagerness of 1 that is what makes ACL2
                # verify guards at defun time unless :verify-guards says not to.
                has_guard = True
            if ":verify-guards" in options:
                value = options[":verify-guards"]
                setting = str(value) if isinstance(value, Sym) else repr(value)
    return has_guard, setting


def program_mode(rest: list) -> bool:
    """Is this defun `(declare (xargs :mode :program))`?"""
    for item in rest:
        if head(item) != "declare":
            continue
        for declaration in item[1:]:
            if head(declaration) != "xargs":
                continue
            value = keyword_plist(declaration[1:]).get(":mode")
            if isinstance(value, Sym) and str(value) == ":program":
                return True
    return False


def analyze_book(path: Path, relative: str) -> Book:
    book = Book(path=relative)
    try:
        forms = Reader(path.read_text(encoding="utf-8")).top_level()
    except ReadError as exc:
        book.read_error = str(exc)
        return book
    for form, line in forms:
        record(book, form, line, local=False, suppressed=False)
    for expression in book.in_theory_forms:
        collect_disabled(expression, book.disabled_rules, book.theories)
    verified = set(book.verify_guards)
    for function in book.functions:
        if function.name in verified:
            function.verified_by_event = True
    return book


# --------------------------------------------------------------------------
# fn-defrecord
# --------------------------------------------------------------------------
#
# `books/defrecord.lisp` owns the record pattern; this reads its output, the
# way `Reader` reads ACL2's syntax.  Without it a migrated book loses forty
# names from `definitions` (the host-names lint then calls every one of them
# undefined), its recognizers vanish from `disabled_rules` (the
# include-hygiene lint then warns about every includer), and its guard and
# theorem counts fall.  Keep the two in step: the macro is proved by
# `tests/acl2/defrecord-tests.lisp`, and this side is pinned by
# `tests/test_ledger.py`.


def selector_term(index: int, car_fn: str, cdr_fn: str, var: str) -> object:
    """``(car (cdr^index var))`` in the given primitives."""
    term: object = Sym(var)
    for _ in range(index):
        term = [Sym(cdr_fn), term]
    return [Sym(car_fn), term]


def defrecord_fields(value: object) -> list[tuple[str, object]]:
    fields: list[tuple[str, object]] = []
    if not isinstance(value, list):
        return fields
    for entry in value:
        if isinstance(entry, list) and entry and isinstance(entry[0], Sym):
            fields.append((str(entry[0]), entry[1] if len(entry) > 1 else Sym("t")))
    return fields


def defrecord_expansion(form: list) -> list:
    """The events ``(fn-defrecord ...)`` generates, as the ledger sees them."""
    if not (len(form) >= 2 and isinstance(form[1], Sym)):
        return []
    name = str(form[1])
    options = keyword_plist(form[2:])
    constructor = options.get(":constructor")
    if not (isinstance(constructor, list) and constructor
            and isinstance(constructor[0], Sym)):
        return []
    ctor = str(constructor[0])
    formals = [item for item in constructor[1:] if isinstance(item, Sym)]
    fields = defrecord_fields(options.get(":fields"))
    tag = options.get(":tag")
    tagged = isinstance(tag, Sym) and str(tag) != "nil"
    shape = str(options.get(":shape") or Sym(name + "-shapep"))
    recognizer_option = options.get(":recognizer", Sym(name + "p"))
    recognizer = (None if isinstance(recognizer_option, Sym)
                  and str(recognizer_option) == "nil" else str(recognizer_option))
    internals = str(options.get(":internals") or Sym(name + "-internals"))
    car_fn = str(options.get(":car-fn") or Sym("fn-ag-car"))
    cdr_fn = str(options.get(":cdr-fn") or Sym("fn-ag-cdr"))
    offset = 1 if tagged else 0
    width = offset + len(fields)
    guard = [Sym("declare"), [Sym("xargs"), Sym(":guard"), Sym("t")]]
    deferred = [Sym("declare"), [Sym("xargs"), Sym(":guard"), Sym("t"),
                                 Sym(":verify-guards"), Sym("nil")]]
    call: list = [Sym(ctor)] + list(formals)
    shape_body = [Sym("and"), [Sym("true-listp"), Sym("x")],
                  [Sym("equal"), [Sym("len"), Sym("x")], width]]
    if tagged:
        shape_body.append([Sym("equal"), [Sym("car"), Sym("x")], tag])
    events: list = [
        [Sym("defun"), Sym(shape), [Sym("x")], guard, shape_body],
        [Sym("defun"), Sym(ctor), list(formals), guard,
         [Sym("list")] + ([tag] if tagged else []) + list(formals)],
    ]
    for index, (accessor, _type) in enumerate(fields):
        events.append([Sym("defun"), Sym(accessor), [Sym("x")], deferred,
                       [Sym("mbe"), Sym(":logic"),
                        selector_term(index + offset, "car", "cdr", "x"),
                        Sym(":exec"),
                        selector_term(index + offset, car_fn, cdr_fn, "x")]])
        events.append([Sym("verify-guards"), Sym(accessor)])
    events.append([Sym("defthm"), Sym(f"{shape}-of-{ctor}"), [Sym(shape)] + call])
    for accessor, _type in fields:
        events.append([Sym("defthm"), Sym(f"{accessor}-of-{ctor}"),
                       [Sym("equal"), [Sym(accessor)] + call, Sym("field")]])
    events.append([Sym("defthm"), Sym(f"{ctor}-of-accessors"),
                   [Sym("implies"), [Sym(shape), Sym("x")],
                    [Sym("equal"),
                     [Sym(ctor)] + [[Sym(accessor), Sym("x")]
                                    for accessor, _type in fields],
                     Sym("x")]]])
    primed = [Sym(str(formal) + "-2") for formal in formals]
    events.append([Sym("defthm"), Sym(f"{ctor}-injective"),
                   [Sym("equal"),
                    [Sym("equal"), call, [Sym(ctor)] + primed],
                    [Sym("and")] + [[Sym("equal"), left, right]
                                    for left, right in zip(formals, primed)]],
                   Sym(":rule-classes"), Sym("nil")])
    events.append([Sym("defthm"), Sym(f"{shape}-forward-shape"),
                   [Sym("implies"), [Sym(shape), Sym("x")],
                    [Sym("and"), [Sym("consp"), Sym("x")],
                     [Sym("true-listp"), Sym("x")]]],
                   Sym(":rule-classes"), Sym(":forward-chaining")])
    events.append([Sym("defthm"), Sym(f"{name}-accessors-forward-consp"),
                   [Sym("and")] + [[Sym("implies"), [Sym(accessor), Sym("x")],
                                    [Sym("consp"), Sym("x")]]
                                   for accessor, _type in fields],
                   Sym(":rule-classes"), Sym(":forward-chaining")])
    events.append([Sym("deftheory"), Sym(internals),
                   [Sym("quote"), [[Sym(":d"), Sym(rune)]
                                   for rune in [shape, ctor]
                                   + [accessor for accessor, _ in fields]]]])
    events.append([Sym("in-theory"), [Sym("disable"), Sym(internals)]])
    if recognizer is not None:
        conjuncts_ = [[Sym(shape), Sym("x")]]
        for accessor, type_term in fields:
            if isinstance(type_term, Sym):
                if str(type_term) != "t":
                    conjuncts_.append([type_term, [Sym(accessor), Sym("x")]])
            else:
                conjuncts_.append(type_term)
        extra = options.get(":extra")
        if isinstance(extra, list):
            conjuncts_.extend(extra)
        recognizer_formals = options.get(":recognizer-formals")
        leading = ([item for item in recognizer_formals if isinstance(item, Sym)]
                   if isinstance(recognizer_formals, list) else [])
        rguard = options.get(":recognizer-guard", Sym("t"))
        rverify = options.get(":recognizer-verify-guards", Sym("t"))
        rdecl = [Sym("declare"), [Sym("xargs"), Sym(":guard"), rguard]]
        if isinstance(rverify, Sym) and str(rverify) == "nil":
            rdecl[1] = rdecl[1] + [Sym(":verify-guards"), Sym("nil")]
        events.append([Sym("defun"), Sym(recognizer), leading + [Sym("x")], rdecl,
                       [Sym("and")] + conjuncts_])
        events.append([Sym("defthm"), Sym(f"{recognizer}-forward-shape"),
                       [Sym("implies"), [Sym(recognizer)] + leading + [Sym("x")],
                        [Sym("and"), [Sym(shape), Sym("x")],
                         [Sym("consp"), Sym("x")],
                         [Sym("true-listp"), Sym("x")]]],
                       Sym(":rule-classes"), Sym(":forward-chaining")])
    return events


def defrecord_export_expansion(form: list) -> list:
    """The ``deftheory`` and withdrawal ``(fn-defrecord-export ...)`` generates."""
    if not (len(form) >= 2 and isinstance(form[1], Sym)):
        return []
    theory = str(form[1])
    options = keyword_plist(form[2:])
    names: list = []
    records = options.get(":records")
    if isinstance(records, list):
        names += [Sym(str(item) + "p") for item in records if isinstance(item, Sym)]
    for key in (":recognizers", ":also"):
        value = options.get(key)
        if isinstance(value, list):
            names += [item for item in value if isinstance(item, Sym)]
    return [[Sym("deftheory"), Sym(theory), [Sym("quote"), names]],
            [Sym("in-theory"), [Sym("disable"), Sym(theory)]]]


def record(book: Book, form: object, line: int, *, local: bool,
           suppressed: bool, generated: bool = False) -> None:
    name = head(form)
    if name is None:
        return
    if name in TRANSPARENT:
        inner_local = local or name == "local"
        for item in form[1:]:
            record(book, item, line, local=inner_local, suppressed=suppressed,
                   generated=generated)
        return
    if name == "encapsulate":
        if not suppressed:
            book.encapsulates += 1
            if len(form) >= 2:
                book.definitions |= encapsulated_names(form[1])
        for item in form[2:]:
            record(book, item, line, local=local, suppressed=suppressed,
                   generated=generated)
        return
    if name in SUPPRESSING:
        if name.startswith("must-fail") and not suppressed:
            book.must_fails += 1
            book.must_fail_forms.append((line, list(form[1:])))
        for item in form[1:]:
            record(book, item, line, local=local, suppressed=True,
                   generated=generated)
        return
    if name == "make-event":
        return  # not statically readable; reporting it as an event would be a guess
    if name in ("fn-defrecord", "fn-defrecord-export"):
        expansion = (defrecord_expansion(form) if name == "fn-defrecord"
                     else defrecord_export_expansion(form))
        for item in expansion:
            record(book, item, line, local=local, suppressed=suppressed,
                   generated=True)
        return
    if suppressed:
        return
    if name in ("defthm", "defthmd") and len(form) >= 3 and isinstance(form[1], Sym):
        options = keyword_plist(form[3:])
        book.definitions.add(str(form[1]))
        book.theorems.append(Theorem(
            name=str(form[1]), book=book.path, line=line, statement=form[2],
            hints=options.get(":hints"), rest=list(form[3:]), local=local,
            disabled=name == "defthmd"))
        return
    if name in ("defun", "defund", "defun-nx") and len(form) >= 4 and isinstance(form[1], Sym):
        has_guard, setting = declared(form[3:])
        book.definitions.add(str(form[1]))
        book.functions.append(Function(
            name=str(form[1]), book=book.path, line=line,
            formals=form[2] if isinstance(form[2], list) else [],
            body=form[-1], declared_guard=has_guard,
            verify_guards_decl=setting, local=local, generated=generated,
            program=program_mode(form[3:])))
        return
    if name == "verify-guards" and len(form) >= 2 and isinstance(form[1], Sym):
        book.verify_guards.append(str(form[1]))
        return
    if name == "include-book" and len(form) >= 2 and isinstance(form[1], str):
        if ":dir" in keyword_plist(form[2:]):
            book.system_includes.append(form[1])
        else:
            book.includes.append(form[1])
            if not local:
                book.nonlocal_includes.append((line, form[1]))
        return
    if name == "in-theory" and len(form) >= 2:
        if not local:
            # A `local' in-theory does not change what the book exports.
            # Resolution waits for the whole book: see `analyze_book'.
            book.in_theory_forms.append(form[1])
        return
    if name == "deftheory" and len(form) >= 3 and isinstance(form[1], Sym):
        book.theories[str(form[1])] = form[2]
        return
    if name == "assert-event":
        book.assert_events += 1
        return
    if name == "defconst":
        book.defconsts += 1
        if len(form) >= 2 and isinstance(form[1], Sym):
            book.definitions.add(str(form[1]))
        return
    if name == "defmacro":
        book.defmacros += 1
        if len(form) >= 2 and isinstance(form[1], Sym):
            book.definitions.add(str(form[1]))
            book.macros.add(str(form[1]))
        return
    if name in ("defun-sk", "defstobj", "defabbrev") and len(form) >= 2 \
            and isinstance(form[1], Sym):
        book.definitions.add(str(form[1]))
        return


# --------------------------------------------------------------------------
# suspect detection
# --------------------------------------------------------------------------


def hint_clauses(hints: object) -> list[dict[str, object]]:
    """Each goal clause of ``:hints`` as a keyword map."""
    if not isinstance(hints, list):
        return []
    clauses = []
    for clause in hints:
        if isinstance(clause, list) and clause and isinstance(clause[0], str):
            clauses.append(keyword_plist(clause[1:]))
    return clauses


def quoted_theory(value: object) -> list[str] | None:
    """The explicit rule list of ``:in-theory '(a b)``, or ``None``."""
    if head(value) == "quote" and isinstance(value[1], list):
        if all(isinstance(item, Sym) for item in value[1]):
            return [str(item) for item in value[1]]
    return None


def used_instances(value: object) -> list[list]:
    """Every ``(:instance L ...)`` in a ``:use`` hint."""
    if value is None:
        return []
    candidates = value if isinstance(value, list) and head(value) != ":instance" else [value]
    out = []
    for item in candidates:
        if head(item) == ":instance" and len(item) >= 2 and isinstance(item[1], Sym):
            out.append(item)
    return out


class Tree:
    """The whole readable tree: books, functions, theorems, roots."""

    def __init__(self, books: dict[str, Book], roots: list[str],
                 hosts: "dict[str, HostFile] | None" = None) -> None:
        self.books = books
        self.roots = roots
        # The `ld`ed files, which no certification reads: see `host_names`.
        self.hosts: dict[str, HostFile] = {} if hosts is None else hosts
        self.functions: dict[str, Function] = {}
        self.theorems: dict[str, Theorem] = {}
        for book in books.values():
            for function in book.functions:
                # A `local' defun inside an `encapsulate' is a witness, not a
                # definition: outside the encapsulate the function is
                # constrained.  Unfolding a witness to judge an exported
                # constraint would call every assumption trivial.
                if not function.local:
                    self.functions.setdefault(function.name, function)
            for theorem in book.theorems:
                self.theorems.setdefault(theorem.name, theorem)
        self.closure = root_closure(books, roots)
        self.suspects = {name: reasons for name, reasons in
                         ((theorem.name, self.suspect_reasons(theorem))
                          for theorem in self.theorems.values()) if reasons}

    # -- unfolding -------------------------------------------------------

    def unfold(self, form: object, depth: int = 3) -> object:
        """Expand non-recursive local defuns.  Bounded; recursion is left alone."""
        if depth <= 0 or not isinstance(form, list) or not form:
            return form
        if head(form) == "quote":
            return form
        expanded = [form[0]] + [self.unfold(item, depth - 1) for item in form[1:]]
        name = head(expanded)
        function = self.functions.get(name) if name else None
        if function is None or not isinstance(function.formals, list):
            return expanded
        if name in calls(function.body):
            return expanded  # recursive: unfolding would not terminate
        if len(function.formals) != len(expanded) - 1:
            return expanded
        bindings = {str(formal): argument
                    for formal, argument in zip(function.formals, expanded[1:])
                    if isinstance(formal, Sym)}
        # beta first: substituting into a `let` body could otherwise capture.
        return self.unfold(substitute(beta(logic_body(function)), bindings), depth - 1)

    # -- detectors -------------------------------------------------------

    def suspect_reasons(self, theorem: Theorem) -> list[str]:
        reasons: list[str] = []
        hypotheses, conclusion = split_implication(theorem.statement)
        clauses = hint_clauses(theorem.hints)

        # 1. The whole proof is an explicit closed theory of existing theorems:
        #    the statement follows from those lemmas by rewriting alone.
        for clause in clauses:
            if set(clause) - {":in-theory"}:
                continue
            rules = quoted_theory(clause.get(":in-theory"))
            if rules and all(rule in self.theorems for rule in rules):
                reasons.append("closed-theory-corollary: proved only by "
                               + ", ".join(sorted(rules)))

        # 2. The theorem is one existing theorem instantiated: same conclusion,
        #    and every hypothesis of the lemma is already a hypothesis here, so
        #    nothing was discharged.
        for clause in clauses:
            for instance in used_instances(clause.get(":use")):
                lemma = self.theorems.get(str(instance[1]))
                if lemma is None:
                    continue
                bindings = {str(pair[0]): pair[1] for pair in instance[2:]
                            if isinstance(pair, list) and len(pair) == 2
                            and isinstance(pair[0], Sym)}
                lemma_hypotheses, lemma_conclusion = split_implication(lemma.statement)
                if not same(substitute(lemma_conclusion, bindings), conclusion):
                    continue
                discharged = [substitute(h, bindings) for h in lemma_hypotheses]
                if all(any(same(h, given) for given in hypotheses) for h in discharged):
                    reasons.append(f"instance-corollary: the statement is "
                                   f"{lemma.name} instantiated, discharging nothing")

        # 3. A conclusion of the form X R X, possibly after unfolding.
        for conjunct in conjuncts(conclusion) + conjuncts(self.unfold(conclusion)):
            name = head(conjunct)
            if name in REFLEXIVE and isinstance(conjunct, list) and len(conjunct) == 3:
                # `(equal t t)` from propagating a literal argument is trivia,
                # not a vacuous theorem; require the two sides to compute.
                if same(conjunct[1], conjunct[2]) and calls(conjunct[1]):
                    reasons.append(f"reflexive-conclusion: a conjunct is "
                                   f"({name} X X)")
                    break

        # 4. The conclusion restates a definition: it is the body of a function
        #    it calls, the body of a hypothesis's recognizer, or that body with
        #    the conjuncts the hypotheses already assert struck out.
        restated = self.restated_definition(hypotheses, conclusion)
        if restated:
            reasons.append(restated)

        # 5. The theorem is one branch of a definition restated: a hypothesis is
        #    the branch test (or its negation) and the conclusion is exactly the
        #    value of that branch.
        branch = self.branch_of_definition(hypotheses, conclusion)
        if branch:
            reasons.append(branch)

        # 6. A `*-preserves-*` name whose statement never calls its own subject.
        preserves = self.preserves_without_subject(theorem)
        if preserves:
            reasons.append(preserves)

        return sorted(set(reasons))

    def restated_definition(self, hypotheses: list, conclusion: object) -> str | None:
        if head(conclusion) in ("equal", "iff") and len(conclusion) == 3:
            for left, right in ((conclusion[1], conclusion[2]),
                                (conclusion[2], conclusion[1])):
                function = self.functions.get(head(left) or "")
                if function is None or not isinstance(left, list):
                    continue
                if len(function.formals) != len(left) - 1:
                    continue
                bindings = {str(f): a for f, a in zip(function.formals, left[1:])
                            if isinstance(f, Sym)}
                body = substitute(logic_body(function), bindings)
                if same(body, right):
                    return (f"definition-restated: the conclusion is the body of "
                            f"{function.name}")
                remainder = [part for part in conjuncts(body)
                             if not any(same(part, given) for given in hypotheses)]
                if remainder and len(remainder) < len(conjuncts(body)):
                    reduced = remainder[0] if len(remainder) == 1 else [Sym("and")] + remainder
                    if same(reduced, right):
                        return (f"definition-restated: the conclusion is the body "
                                f"of {function.name} with the conjuncts the "
                                f"hypotheses already assert struck out")
        for hypothesis in hypotheses:
            function = self.functions.get(head(hypothesis) or "")
            if function is None or not isinstance(hypothesis, list):
                continue
            if len(function.formals) != len(hypothesis) - 1:
                continue
            bindings = {str(f): a for f, a in zip(function.formals, hypothesis[1:])
                        if isinstance(f, Sym)}
            if same(substitute(logic_body(function), bindings), conclusion):
                return (f"recognizer-body-conclusion: the conclusion is the body "
                        f"of the hypothesis {function.name}")
        return None

    def branch_of_definition(self, hypotheses: list, conclusion: object) -> str | None:
        if head(conclusion) != "equal" or len(conclusion) != 3:
            return None
        for call, value in ((conclusion[1], conclusion[2]),
                            (conclusion[2], conclusion[1])):
            name = head(call)
            function = self.functions.get(name) if name else None
            if function is None or len(function.formals) != len(call) - 1:
                continue
            bindings = {str(f): a for f, a in zip(function.formals, call[1:])
                        if isinstance(f, Sym)}
            body = substitute(beta(logic_body(function)), bindings)
            for test, then, otherwise in if_branches(body):
                for hypothesis in hypotheses:
                    target = negated_form(hypothesis)
                    if target is not None and same(target, test) and same(value, otherwise):
                        return (f"branch-of-definition: the hypothesis negates a "
                                f"branch test of {name} and the conclusion is "
                                f"that branch's value")
                    if same(hypothesis, test) and same(value, then):
                        return (f"branch-of-definition: the hypothesis is a branch "
                                f"test of {name} and the conclusion is that "
                                f"branch's value")
        return None

    def preserves_without_subject(self, theorem: Theorem) -> str | None:
        if "-preserves-" not in theorem.name:
            return None
        subject = theorem.name.split("-preserves-")[0]
        called = calls(theorem.statement)
        if any(name == subject or name.startswith(subject + "-") for name in called):
            return None
        if subject not in self.functions and not any(
                name.startswith(subject + "-") for name in self.functions):
            return None  # the name does not claim a function we know
        return (f"preserves-no-subject-call: the statement never calls "
                f"{subject} or a {subject}- transition")


def logic_body(function: Function) -> object:
    """The logical body: the ``:logic`` branch of a top-level ``mbe``."""
    body = function.body
    if head(body) == "mbe":
        options = keyword_plist(body[1:])
        if ":logic" in options:
            return options[":logic"]
    return body


def negated_form(hypothesis: object) -> object | None:
    """``X`` from ``(not X)``."""
    if head(hypothesis) == "not" and len(hypothesis) == 2:
        return hypothesis[1]
    return None


def beta(form: object) -> object:
    """Inline ``let``, ``let*`` and literal lambda applications.

    ACL2's ``let`` is a lambda application, so this changes no meaning.  It is
    what lets the branch detector see through a definition that names its
    branch test with a local variable.
    """
    if not isinstance(form, list) or not form or head(form) == "quote":
        return form
    name = head(form)
    if name == "let" and len(form) >= 3 and isinstance(form[1], list):
        bindings = {str(pair[0]): beta(pair[1]) for pair in form[1]
                    if isinstance(pair, list) and len(pair) == 2
                    and isinstance(pair[0], Sym)}
        return beta(substitute(strip_declares(form[2:]), bindings))
    if name == "let*" and len(form) >= 3 and isinstance(form[1], list):
        body = strip_declares(form[2:])
        for pair in reversed(form[1]):
            if isinstance(pair, list) and len(pair) == 2 and isinstance(pair[0], Sym):
                body = [Sym("let"), [pair], body]
        return beta(body)
    if isinstance(form[0], list) and head(form[0]) == "lambda" and len(form[0]) >= 3:
        formals = form[0][1] if isinstance(form[0][1], list) else []
        bindings = {str(f): beta(a) for f, a in zip(formals, form[1:])
                    if isinstance(f, Sym)}
        return beta(substitute(form[0][-1], bindings))
    return [beta(item) for item in form]


def strip_declares(body: list) -> object:
    """The value form of a ``let`` body, ignoring declarations."""
    return body[-1] if body else Sym("nil")


def if_branches(form: object, found: list | None = None) -> list:
    """Every ``(if TEST THEN ELSE)`` as a triple."""
    found = [] if found is None else found
    if isinstance(form, list) and head(form) != "quote":
        if head(form) == "if" and len(form) == 4:
            found.append((form[1], form[2], form[3]))
        for item in form:
            if_branches(item, found)
    return found


# --------------------------------------------------------------------------
# export and teeth lints
# --------------------------------------------------------------------------
#
# Six WARN lints, all counted in the generated ledger.  None is a claim
# that a theorem is wrong: the first four name the ways this tree has
# repeatedly made later proofs expensive, the fourth (below, over the host
# files) names the way it has repeatedly made bridges fail to start, and the
# fifth counts the records still written out by hand.
#
# * Export hygiene.  A book's micro discipline (`planning/deputies/BRIEF.md`)
#   is that accessor equalities and `len` backchaining rules stay inside the
#   book that needs them: `:rule-classes nil`, `local`, `defthmd`, or a
#   closing `in-theory (disable ...)`.  One such rule left enabled rewrites
#   every downstream goal out of accessor vocabulary.
# * Enabled projection.  The same hazard seen from the other side: an
#   accessor whose own definition rune ships enabled, while other books state
#   theorems over it.  One `enable` downstream and those theorems stop
#   matching, with no error and no failing book.
# * Teeth form.  A `must-fail` whose body is a bare `thm` over free variables
#   shows only that ACL2 did not prove a general claim, which a typo also
#   achieves.  Teeth are concrete: a specific violating value.
# * Include hygiene.  A non-local ``include-book`` of a book that ends with no
#   withdrawal re-exports every enabled rule of that book into the includer and
#   into everything above it.  `books/bp-ingress.lisp` took a non-local include
#   of `article-properties` for one guard hint and turned a six-minute proof
#   into an 1800 s timeout: 1.92M backchain frames, none of them useful.

# One-argument applications of these are recognizers or arithmetic, not the
# accessor-shaped rewrites the export lint is about.
NON_ACCESSOR = {
    "not", "len", "consp", "atom", "null", "endp", "zp", "true-listp",
    "natp", "posp", "integerp", "rationalp", "acl2-numberp", "stringp",
    "symbolp", "characterp", "booleanp", "quote", "if", "implies",
}


def rule_name(item: object) -> str | None:
    """The name in a theory element: ``foo`` or ``(:rewrite foo)``."""
    if isinstance(item, Sym):
        return str(item)
    if (isinstance(item, list) and len(item) == 2 and isinstance(item[0], Sym)
            and str(item[0]).startswith(":") and isinstance(item[1], Sym)):
        return str(item[1])
    return None


def theory_name_members(name: str, theories: dict[str, object],
                        seen: frozenset[str]) -> set[str]:
    """A name as a set of rules: a ``deftheory`` name expands, a rune does not."""
    if name in theories and name not in seen:
        return theory_members(theories[name], theories, seen | {name})
    return {name}


def theory_members(form: object, theories: dict[str, object],
                   seen: frozenset[str] = frozenset()) -> set[str]:
    """The rules a theory expression denotes, as far as it is literal.

    A book withdraws its helpers by naming them once -- ``(deftheory
    fn-x-vocabulary '(...))`` -- and disabling that name at the end.  Reading
    only the disable would count every one of those rules as exported.  What
    cannot be read literally (``current-theory``, a computed theory)
    contributes nothing, so an unresolvable expression under-approximates the
    withdrawal and the lint warns rather than going quiet.
    """
    if isinstance(form, Sym):
        return theory_name_members(str(form), theories, seen)
    if not isinstance(form, list) or not form:
        return set()
    name = head(form)
    if name == "quote" and len(form) == 2 and isinstance(form[1], list):
        members: set[str] = set()
        for item in form[1]:
            rune = rule_name(item)
            if rune:
                members |= theory_name_members(rune, theories, seen)
        return members
    if name in ("disable", "disable*"):
        return theory_members([Sym("quote"), list(form[1:])], theories, seen)
    if name == "theory" and len(form) == 2:
        inner = form[1]
        if head(inner) == "quote" and len(inner) == 2:
            inner = inner[1]
        return theory_members(inner, theories, seen) if isinstance(inner, Sym) else set()
    if name in ("union-theories", "union-theories-fn") and len(form) == 3:
        return (theory_members(form[1], theories, seen)
                | theory_members(form[2], theories, seen))
    if name in ("set-difference-theories", "set-difference-theories-fn") and len(form) == 3:
        return (theory_members(form[1], theories, seen)
                - theory_members(form[2], theories, seen))
    return set()


def collect_disabled(form: object, out: set[str],
                     theories: dict[str, object] | None = None) -> None:
    """Every rule name an ``in-theory`` expression turns off."""
    theories = {} if theories is None else theories
    if not isinstance(form, list) or not form:
        return
    name = head(form)
    if name in ("disable", "disable*"):
        for item in form[1:]:
            rune = rule_name(item)
            if rune:
                out |= theory_name_members(rune, theories, frozenset())
        return
    if name in ("e/d", "e/d*"):
        # (e/d <enable> <disable> <enable> ...): the odd groups are disables.
        for index, group in enumerate(form[1:]):
            if index % 2 == 1 and isinstance(group, list):
                for item in group:
                    rune = rule_name(item)
                    if rune:
                        out |= theory_name_members(rune, theories, frozenset())
        return
    if name in ("set-difference-theories", "set-difference-theories-fn") and len(form) == 3:
        # (in-theory (set-difference-theories (current-theory :here) X)):
        # whatever X names is what this book withdraws.
        out |= theory_members(form[2], theories, frozenset())
        return
    for item in form[1:]:
        collect_disabled(item, out, theories)


def one_argument_application(form: object) -> bool:
    return (isinstance(form, list) and len(form) == 2
            and isinstance(form[0], Sym)
            and str(form[0]) not in NON_ACCESSOR
            and not str(form[0]).startswith(":"))


def exported(theorem: Theorem, book: Book) -> bool:
    """Is this theorem an enabled rule outside its book?"""
    if theorem.local or theorem.disabled:
        return False
    if theorem.name in book.disabled_rules:
        return False
    classes = keyword_plist(theorem.rest).get(":rule-classes", "absent")
    if isinstance(classes, Sym) and str(classes) == "nil":
        return False
    return not (isinstance(classes, list) and not classes)


def export_hygiene(tree: "Tree") -> list[dict]:
    """Enabled rules whose shape rewrites goals out of accessor vocabulary."""
    findings: list[dict] = []
    for book in sorted(tree.books.values(), key=lambda b: b.path):
        for theorem in book.theorems:
            if not exported(theorem, book):
                continue
            hypotheses, conclusion = split_implication(theorem.statement)
            reason = None
            if (head(conclusion) == "equal" and len(conclusion) == 3
                    and one_argument_application(conclusion[1])
                    and one_argument_application(conclusion[2])
                    and str(conclusion[1][0]) != str(conclusion[2][0])
                    and (str(conclusion[1][0]) in tree.functions
                         or str(conclusion[2][0]) in tree.functions)):
                # Two *different* one-argument heads: the rule rewrites one
                # vocabulary into another, which is what pulls downstream
                # goals out of accessor form.  The same head on both sides is
                # a preservation or congruence lemma, which is the shape the
                # discipline asks for, so it is not a finding.
                reason = ("accessor-equality: an enabled equality between two "
                          "different one-argument applications")
            elif any("len" in calls(hypothesis) for hypothesis in hypotheses):
                if head(conclusion) == "consp":
                    reason = ("len-backchaining: an enabled consp conclusion "
                              "backchained to a len hypothesis")
                elif (head(conclusion) == "equal" and len(conclusion) == 3
                      and any(head(side) == "len" for side in conclusion[1:])):
                    reason = ("len-backchaining: an enabled len equality "
                              "backchained to a len hypothesis")
            if reason:
                findings.append({"theorem": theorem.name, "book": book.path,
                                 "line": theorem.line, "reason": reason})
    return findings


# `logic_body` reaches through `mbe`; these are what is left when an
# accessor is nothing but a walk into a structure.  A body built from only
# these and the function's single formal computes nothing: its whole content
# is WHERE the value is, which is exactly what a caller's lemma is stated
# about and exactly what an unfold destroys.
SELECTORS = {
    "car", "cdr", "caar", "cadr", "cdar", "cddr", "caaar", "caadr", "cadar",
    "caddr", "cdaar", "cdadr", "cddar", "cdddr", "cadddr", "cddddr",
    "nth", "first", "second", "third", "fourth", "fifth", "sixth", "seventh",
    "eighth", "ninth", "tenth", "rest", "assoc", "assoc-equal", "assoc-eq",
    "mbe", "the",
}


def selector_chain(form: object, variable: str) -> bool:
    """Is `form` a walk into `variable` through selectors and nothing else?"""
    if isinstance(form, Sym):
        return str(form) == variable
    if isinstance(form, (int, float, str)):
        return True
    if isinstance(form, list):
        if head(form) == "quote":
            return True
        if head(form) in SELECTORS:
            return all(selector_chain(item, variable) for item in form[1:])
    return False


def projection_shaped(function: Function) -> bool:
    """One formal, and a body that only selects out of it."""
    if (function.local or function.program
            or not isinstance(function.formals, list)
            or len(function.formals) != 1
            or not isinstance(function.formals[0], Sym)):
        return False
    return selector_chain(logic_body(function), str(function.formals[0]))


def enabled_projection(tree: "Tree") -> list[dict]:
    """Accessors a book exports ENABLED that other books state theorems over.

    The hazard is silent and one `enable` away.  A projection whose
    `(:definition)` rune is enabled can be unfolded, and the moment anything
    downstream unfolds it every lemma stated over the accessor stops
    matching: the goal is in selector vocabulary and the rules are in
    accessor vocabulary.  Nothing errors and no book fails; the proofs that
    used to close start splitting, and the cost lands on whoever is next.
    This tree has paid that bill three times in one day through the
    equivalent hazard for whole-state recognizers.

    The criterion is deliberately narrow, so that a finding is a defect and
    not a style note.  All three must hold: the function is a PROJECTION --
    one formal, a body that is only a walk into it, so unfolding replaces a
    name with a `cadr` chain and buys nothing; its own book leaves the name
    out of its closing withdrawal, so the definition rune ships enabled; and
    a theorem in ANOTHER book is stated over it, so there is something for
    the unfold to break.  A projection nothing else mentions costs nobody
    anything, and one its book withdraws is already safe.

    The repair is one name in the book's existing `deftheory`; this lint
    does not make it, and a book is not wrong to export an accessor it means
    to be unfolded -- it is wrong to do so while other books reason over it.
    """
    stated_in: dict[str, set[str]] = {}
    for book in tree.books.values():
        for theorem in book.theorems:
            for name in calls(theorem.statement):
                stated_in.setdefault(name, set()).add(book.path)
    findings: list[dict] = []
    for book in sorted(tree.books.values(), key=lambda b: b.path):
        for function in book.functions:
            if not projection_shaped(function):
                continue
            if function.name in book.disabled_rules:
                continue
            elsewhere = sorted(stated_in.get(function.name, set()) - {book.path})
            if not elsewhere:
                continue
            findings.append({
                "function": function.name, "book": book.path,
                "line": function.line, "stated_in": elsewhere,
                "reason": ("enabled-projection: the definition rune ships "
                           "enabled and {} state{} theorems over it, so one "
                           "downstream unfold stops those theorems matching"
                           .format(
                               "{} books".format(len(elsewhere))
                               if len(elsewhere) != 1 else "1 book",
                               "" if len(elsewhere) != 1 else "s")),
            })
    return findings


def statement_of(body: object) -> object:
    """The claim inside a ``thm``/``defthm``, without its keyword options.

    Scanning the options too would let a ``:rule-classes nil`` supply the
    constant that makes a general claim look like a witness.
    """
    index = 1 if head(body) == "thm" else 2
    return body[index] if isinstance(body, list) and len(body) > index else None


def concrete_witness(form: object) -> bool:
    """Does this form mention a constant: a literal, a keyword, a defconst?"""
    if isinstance(form, Sym):
        text = str(form)
        if text.startswith(":"):
            return True  # a keyword: a specific value in this tree's vocabulary
        return len(text) > 2 and text.startswith("*") and text.endswith("*")
    if isinstance(form, (int, float)):
        return True
    if isinstance(form, str):  # a string literal; Sym was handled above
        return True
    if isinstance(form, list):
        if head(form) == "quote":
            return True
        return any(concrete_witness(item) for item in form)
    return False


def teeth_form(tree: "Tree") -> list[dict]:
    """``must-fail`` bodies that are general claims rather than witnesses."""
    findings: list[dict] = []
    for book in sorted(tree.books.values(), key=lambda b: b.path):
        for line, arguments in book.must_fail_forms:
            body = next((item for item in arguments
                         if not (isinstance(item, Sym) and str(item).startswith(":"))),
                        None)
            if head(body) not in ("thm", "defthm", "defthmd"):
                continue
            if concrete_witness(statement_of(body)):
                continue
            name = str(body[1]) if (head(body) != "thm" and len(body) > 1
                                    and isinstance(body[1], Sym)) else "thm"
            findings.append({
                "check": name, "book": book.path, "line": line,
                "reason": ("bare-general-claim: the must-fail body has no "
                           "constant, so it refutes nothing in particular"),
            })
    return findings


def has_export_theory(book: Book) -> bool:
    """Does this book withdraw anything on its way out?

    The same computation the export-hygiene lint exempts a theorem by: the
    rules a non-local top-level ``in-theory`` turns off, with ``deftheory``
    names expanded.  A book that withdraws nothing exports its whole enabled
    world, so what it costs an includer is not bounded by its interface.
    """
    return bool(book.disabled_rules)


def exports_no_rule(book: Book) -> bool:
    """Has this book no rule to export, whatever its theory events say?

    A macro book (`books/defrecord.lisp`, `books/deftransition.lisp`) defines
    macros and `:program`-mode plumbing.  `:program` mode has no definitional
    axiom, so the book adds nothing to any theory and including it cannot
    cost an includer a rule.  Withdrawing nothing is then the honest export
    event, not a missing one.
    """
    return (bool(book.functions)
            and all(function.program for function in book.functions)
            and not book.theorems
            and not book.encapsulates
            # An include-only shim re-exports what it includes, whatever it
            # does or does not define itself.
            and not book.includes
            and not book.system_includes)


def included_path(book: Book, reference: str) -> str:
    """The repository path a book's ``include-book`` string names."""
    return resolve((Path(book.path).parent / reference).with_suffix(".lisp").as_posix())


def include_hygiene(tree: "Tree") -> list[dict]:
    """Non-local includes of local books that withdraw nothing on exit."""
    findings: list[dict] = []
    for book in sorted(tree.books.values(), key=lambda b: b.path):
        for line, reference in book.nonlocal_includes:
            target = tree.books.get(included_path(book, reference))
            # A book this tree does not read (a system book, or a path that
            # does not resolve) has no export theory to judge.
            if target is None or target.read_error is not None:
                continue
            if has_export_theory(target) or exports_no_rule(target):
                continue
            findings.append({
                "book": book.path, "line": line, "include": reference,
                "included": target.path,
                "reason": ("re-export: the included book ends with no theory "
                           "withdrawal, so every rule it leaves enabled is "
                           "enabled here and above"),
            })
    return findings


# --------------------------------------------------------------------------
# host-names lint
# --------------------------------------------------------------------------
#
# The fourth lint, and the only one that reads files no certification ever
# touches.  `host/*.lisp` and `host/native/*.lisp` are `ld`ed by the bridges
# at start-up, never certified, so an undefined name in them is found by a
# bridge crashing: `host/checkpoint-host.lisp` kept naming `*fn-store-groups*`
# after the compiled group table deleted it, and every `Acl2Store`
# constructor died with a Translate error until a later lane noticed.  This
# lint reads the host files the way the book lints read books and reports a
# name that is defined nowhere the host file can see.
#
# What a host file can see: its own definitions, the definitions of every
# host file it `ld`s, the definitions of every book reachable through its
# `include-book` forms (transitively, the same include graph the other lints
# use), and `tools/acl2-builtins.txt`.
#
# Deliberately conservative, because this is a WARN over unparsed code:
# a `local` book definition counts as visible, `loop` bodies and
# package-qualified symbols (`sb-posix:close`) are not read at all, and an
# unresolvable `include-book` silences nothing but contributes nothing.
# Under-reporting here is a missed crash; over-reporting would make the lint
# noise that a lane learns to skip.

BUILTINS = ROOT / "tools/acl2-builtins.txt"

# Heads that define a name in the file being read.  The name is `form[1]`,
# or the head of `form[1]` when that is a list (`(defstruct (name opts) ...)`).
HOST_DEFINITION_HEADS = {
    "defun", "defund", "defun-nx", "defun-inline", "defund-inline",
    "defmacro", "defabbrev", "defn", "defnd", "defun-sk", "defstobj",
    "defconst", "defconstant", "defparameter", "defvar", "defglobal",
    "defstruct", "define-condition", "deftype", "defsetf", "defgeneric",
}

# Heads whose subforms are syntax, data, or another language.  `loop` is
# SBCL's iteration macro in `host/native/io.lisp`: its keywords read as
# symbols in function position, and reading them would report `collect`.
HOST_OPAQUE_HEADS = {
    "quote", "declare", "declaim", "in-package", "defpackage", "defttag",
    "deftype", "defstruct", "define-condition", "defsetf", "loop", "loop-finish",
}

# Heads the reader itself produces, or that hold a form in every position.
HOST_TRANSPARENT_HEADS = {"quasiquote", "unquote", "unquote-splicing",
                          "function", "vector", "progn", "progn!", "local",
                          "with-output", "eval-when", "value-triple"}

DEFCONST_NAME = re.compile(r"^\*.+\*$")


def macro_names(tree: "Tree") -> set[str]:
    """Every `defmacro` name the tree defines, in books and in host files.

    A macro's arguments are syntax, not forms: `(fnn-posix (path) ...)` binds
    `path`, and reading its first argument as a call reports `path`.  The lint
    judges the macro name and stops there.
    """
    names = {name for host in tree.hosts.values() for name in host.macros}
    return names | {name for book in tree.books.values() for name in book.macros}


def host_definition_name(form: list) -> str | None:
    if len(form) < 2:
        return None
    target = form[1]
    if isinstance(target, list):
        target = target[0] if target and isinstance(target[0], Sym) else None
    return str(target) if isinstance(target, Sym) else None


def slot_accessors(form: list) -> set[str]:
    """The reader names a `defstruct` or `define-condition` generates."""
    names: set[str] = set()
    name = host_definition_name(form)
    if name is None:
        return names
    if head(form) == "defstruct":
        prefix, slots = f"{name}-", form[2:]
        if isinstance(form[1], list):
            for option in form[1][1:]:
                if str(head(option)).lstrip(":") == "conc-name":
                    prefix = "" if len(option) < 2 else str(option[1])
        names.add(f"make-{name}")
        names.add(f"{name}-p")
        if isinstance(form[1], list):
            for option in form[1][1:]:
                if str(head(option)).lstrip(":") in ("constructor", "predicate",
                                                     "copier") \
                        and len(option) >= 2 and isinstance(option[1], Sym):
                    names.add(str(option[1]))
        for slot in slots:
            field_name = slot if isinstance(slot, Sym) else (
                slot[0] if isinstance(slot, list) and slot and isinstance(slot[0], Sym)
                else None)
            if field_name is not None:
                names.add(f"{prefix}{field_name}")
    else:  # define-condition: readers are named, not derived
        for slot in (form[3] if len(form) > 3 and isinstance(form[3], list) else []):
            if not isinstance(slot, list):
                continue
            options = keyword_plist(slot[1:])
            for key in (":accessor", ":reader", ":writer"):
                if isinstance(options.get(key), Sym):
                    names.add(str(options[key]))
    return names


def encapsulated_names(signatures: object) -> set[str]:
    """The function names an `encapsulate` signature list constrains."""
    names: set[str] = set()
    if not isinstance(signatures, list):
        return names
    for signature in signatures:
        if not isinstance(signature, list) or not signature:
            continue
        subject = signature[0]
        if isinstance(subject, Sym):
            names.add(str(subject))          # (f (x y) t)
        elif isinstance(subject, list) and subject and isinstance(subject[0], Sym):
            names.add(str(subject[0]))       # ((f * *) => *)
    return names


def referenceable(name: str) -> bool:
    """Is this symbol one the lint judges?

    Not a keyword, not package-qualified (`sb-posix:close` names another
    package's world, which this tool does not read), not a lambda-list
    marker, not a character or number.
    """
    return bool(name) and not (
        name.startswith(":") or ":" in name or name.startswith("&")
        or name.startswith("#") or is_number(name))


@dataclass
class HostFile:
    """An `ld`ed Lisp file: never certified, so only a bridge start-up reads it."""
    path: str
    defines: set[str] = field(default_factory=set)
    includes: list[str] = field(default_factory=list)
    lds: list[str] = field(default_factory=list)
    macros: set[str] = field(default_factory=set)
    # Top-level forms, kept for the reference pass: which names are macros is
    # not known until every book and host file has been read.
    forms: list[tuple[object, int]] = field(default_factory=list)
    # (name, line of the top-level form the reference sits in)
    references: list[tuple[str, int]] = field(default_factory=list)
    read_error: str | None = None


def analyze_host(path: Path, relative: str) -> HostFile:
    host = HostFile(path=relative)
    try:
        forms = Reader(path.read_text(encoding="utf-8")).top_level()
    except ReadError as exc:
        host.read_error = str(exc)
        return host
    host.forms = forms
    for form, line in forms:
        host_record(host, form, line)
    return host


def host_record(host: HostFile, form: object, line: int) -> None:
    """One top-level form: its definitions, its dependencies, its references."""
    name = head(form)
    if name in ("local", "progn", "progn!", "with-output", "encapsulate",
                "eval-when", "value-triple", "when", "unless"):
        if name == "encapsulate" and len(form) >= 2:
            host.defines |= encapsulated_names(form[1])
        for item in form[2 if name == "encapsulate" else 1:]:
            host_record(host, item, line)
        return
    if name == "include-book" and len(form) >= 2 and isinstance(form[1], str):
        if ":dir" not in keyword_plist(form[2:]):
            host.includes.append(form[1])
        return
    if name in ("ld", "load") and len(form) >= 2 and isinstance(form[1], str):
        # `ld` is the interpreted host files' load edge and `load` is the
        # raw-Lisp ones' (host/native/io.lisp, host/native/tcpcl.lisp, both
        # loaded under `(progn! (set-raw-mode t) ...)`).  Both name a file
        # whose definitions the loading file may then use.
        host.lds.append(form[1])
        return
    if isinstance(name, str) and name.endswith("define-alien-routine"):
        # `(sb-alien:define-alien-routine ("flock" fnn-%flock) ...)`: a raw
        # foreign entry point, named in the second position of its first
        # argument.  The rest is alien syntax, not forms.
        alien = form[1] if len(form) >= 2 else None
        if isinstance(alien, list) and len(alien) >= 2 and isinstance(alien[1], Sym):
            host.defines.add(str(alien[1]))
        elif isinstance(alien, Sym):
            host.defines.add(str(alien))
        return
    if name in HOST_DEFINITION_HEADS and isinstance(form, list):
        defined = host_definition_name(form)
        if defined is not None:
            host.defines.add(defined)
            if name in ("defmacro", "defabbrev"):
                host.macros.add(defined)
        host.defines |= slot_accessors(form)


def host_references(host: HostFile, form: object, line: int,
                    macros: set[str] | None = None) -> None:
    """Every symbol used in function position, and every `*constant*`."""
    macros = set() if macros is None else macros
    if isinstance(form, Sym):
        text = str(form)
        if DEFCONST_NAME.match(text) and referenceable(text):
            host.references.append((text, line))
        return
    if not isinstance(form, list) or not form:
        return
    name = head(form)
    if name is None:
        for item in form:                      # ((lambda (x) ...) arg)
            host_references(host, item, line, macros)
        return
    if name in HOST_OPAQUE_HEADS or ":" in name:
        # A package-qualified head (`sb-alien:define-alien-routine`) names a
        # macro in a package this tool does not read; its arguments are that
        # macro's syntax.
        return
    if name in HOST_TRANSPARENT_HEADS:
        for item in form[1:]:
            host_references(host, item, line, macros)
        return
    if name in ("let", "let*"):
        for binding in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
            if isinstance(binding, list):
                for item in binding[1:]:
                    host_references(host, item, line, macros)
        rest = form[2:]
    elif name in ("flet", "labels", "macrolet"):
        for binding in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
            if isinstance(binding, list) and binding and isinstance(binding[0], Sym):
                host.defines.add(str(binding[0]))
                for item in binding[2:]:
                    host_references(host, item, line, macros)
        rest = form[2:]
    elif name == "lambda":
        rest = form[2:]
    elif name in ("mv-let", "mv?-let", "destructuring-bind", "multiple-value-bind"):
        rest = form[2:]
    elif name in ("case", "case-match"):
        for item in form[1:2]:
            host_references(host, item, line, macros)
        for clause in form[2:]:
            for item in (clause[1:] if isinstance(clause, list) else []):
                host_references(host, item, line, macros)
        return
    elif name in ("dolist", "dotimes"):
        for item in (form[1][1:] if len(form) > 1 and isinstance(form[1], list) else []):
            host_references(host, item, line, macros)
        rest = form[2:]
    elif name in ("do", "do*"):
        for binding in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
            for item in (binding[1:] if isinstance(binding, list) else []):
                host_references(host, item, line, macros)
        rest = form[2:]
    elif name == "cond":
        # A clause is `(test form ...)`: every element is a form, and a bare
        # variable test (`(context :context)`) is not a call of `context`.
        for clause in form[1:]:
            for item in (clause if isinstance(clause, list) else [clause]):
                host_references(host, item, line, macros)
        return
    elif name in ("handler-case", "handler-bind", "restart-case"):
        host_references(host, form[1] if len(form) > 1 else None, line, macros)
        for clause in form[2:]:
            for item in (clause[2:] if isinstance(clause, list) else []):
                host_references(host, item, line, macros)
        return
    elif name == "the":
        rest = form[2:]
    elif name.startswith("with-") and len(form) > 1 and isinstance(form[1], list):
        # The `with-` convention: the first argument is a binding spec.
        for binding in form[1]:
            for item in (binding[1:] if isinstance(binding, list) else []):
                host_references(host, item, line, macros)
        rest = form[2:]
    elif name in HOST_DEFINITION_HEADS:
        # The name and the formals are not references; the body is.
        rest = form[3:] if name.startswith("defun") or name in (
            "defmacro", "defabbrev", "defn", "defnd", "defun-sk") else form[2:]
    else:
        if referenceable(name):
            host.references.append((name, line))
        if name in macros:
            return  # a macro's arguments are its syntax, not forms
        rest = form[1:]
    for item in rest:
        host_references(host, item, line, macros)


def collect_references(host: HostFile, macros: set[str]) -> None:
    """The second pass: every name used, once the macro names are known."""
    host.references = []
    for form, line in host.forms:
        if head(form) in ("include-book", "ld", "load"):
            continue
        host_references(host, form, line, macros)


def host_paths() -> list[tuple[Path, str]]:
    """Every `.lisp` outside `books/` and `tests/acl2/` that the tree loads.

    `host/` and `host/native/` are the tree's two host directories; anything
    else reaches this list by being named in an `(ld "...")` that a host file
    or a `tools/*.py` bridge issues.
    """
    found: dict[str, Path] = {}
    for directory in HOST_DIRS:
        for path in sorted((ROOT / directory).glob("*.lisp")):
            found[path.relative_to(ROOT).as_posix()] = path
    sources = [ROOT / relative for relative in found] + sorted((ROOT / "tools").glob("*.py"))
    for source in sources:
        for reference in LD_REFERENCE.findall(source.read_text(encoding="utf-8")):
            relative = resolve(reference)
            if (relative.startswith(("books/", "tests/acl2/"))
                    or not (ROOT / relative).is_file()):
                continue
            found[relative] = ROOT / relative
    return [(path, relative) for relative, path in sorted(found.items())]


LD_REFERENCE = re.compile(r'\((?:ld|load)\s+"([^"]+\.lisp)"')


def load_hosts() -> dict[str, HostFile]:
    return {relative: analyze_host(path, relative) for path, relative in host_paths()}


def acl2_builtins() -> set[str]:
    if not BUILTINS.is_file():
        return set()
    return {line.split(";", 1)[0].strip().lower()
            for line in BUILTINS.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith(";")}


def host_visible(host: HostFile, tree: "Tree") -> set[str]:
    """Every name this host file can reach, transitively."""
    visible: set[str] = set()
    seen: set[str] = set()
    pending = [host.path]
    while pending:
        relative = pending.pop()
        if relative in seen:
            continue
        seen.add(relative)
        current = tree.hosts.get(relative)
        if current is None:
            continue
        visible |= current.defines
        base = Path(relative).parent
        for reference in current.includes:
            for candidate in (resolve((base / reference).with_suffix(".lisp").as_posix()),
                              resolve(f"{reference}.lisp")):
                if candidate in tree.books:
                    visible |= book_closure_definitions(tree, candidate)
                    break
        for reference in current.lds:
            for candidate in (resolve((base / reference).as_posix()), resolve(reference)):
                if candidate in tree.hosts:
                    pending.append(candidate)
                    break
    return visible


def book_closure_definitions(tree: "Tree", relative: str) -> set[str]:
    """Every definition of a book and of the books it includes."""
    names: set[str] = set()
    seen: set[str] = set()
    pending = [relative]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        book = tree.books.get(current)
        if book is None:
            continue
        names |= book.definitions
        base = Path(current).parent
        for reference in book.includes:
            pending.append(resolve((base / reference).with_suffix(".lisp").as_posix()))
    return names


def host_names(tree: "Tree") -> list[dict]:
    """Names a host file uses that nothing it loads defines."""
    builtins = acl2_builtins()
    macros = macro_names(tree)
    elsewhere: dict[str, str] = {}
    for book in sorted(tree.books.values(), key=lambda b: b.path):
        for name in book.definitions:
            elsewhere.setdefault(name, book.path)
    for other in sorted(tree.hosts.values(), key=lambda h: h.path):
        for name in other.defines:
            elsewhere.setdefault(name, other.path)
    findings: list[dict] = []
    for host in sorted(tree.hosts.values(), key=lambda h: h.path):
        if host.read_error is not None:
            findings.append({"host": host.path, "line": 1, "name": host.path,
                             "reason": f"unreadable: {host.read_error}"})
            continue
        collect_references(host, macros)
        visible = host_visible(host, tree) | builtins
        reported: set[str] = set()
        for name, line in host.references:
            key = name.lower()
            if key in visible or key in reported:
                continue
            reported.add(key)
            source = elsewhere.get(key)
            reason = ("undefined: nothing in this tree defines it and it is "
                      "not in tools/acl2-builtins.txt, so the bridge that "
                      "loads this file fails at start-up")
            if source is not None:
                reason = (f"defined in {source}, which this file neither "
                          "includes nor `ld`s: it resolves only because "
                          "something else loaded that file into the same "
                          "session first")
            findings.append({"host": host.path, "line": line, "name": name,
                             "source": source, "reason": reason})
    return findings


# --------------------------------------------------------------------------
# hand-written record lint
# --------------------------------------------------------------------------
#
# The fifth lint, and the only one about a migration rather than a defect.
# `books/defrecord.lisp` generates the pattern of docs/proof-style.md section
# 1; a book that still writes it out has eleven events per three-field record
# to keep in step by hand, and the tree has repeatedly lost one of the three
# forward-chaining shape facts that way and paid for it in a rule fan.  WARN,
# never an error: a hand-written record is correct, it is just not generated,
# and the count is how the migration stays visible.

SELECTOR_PRIMITIVES = {"car", "cdr", "fn-ag-car", "fn-ag-cdr"}


def selector_over(form: object, variable: str) -> bool:
    """Is this a total positional selector applied to `variable`?

    Two shapes are in the tree: the `car`/`cdr` chain `books/acceptance.lisp`
    writes under an `mbe`, and the `(fn-bp-nth 3 x)` call `books/scheduler.lisp`
    and the bp books write.  Both are one field of a raw-list record.
    """
    if isinstance(form, Sym):
        return str(form) == variable
    if not isinstance(form, list) or not form or not isinstance(form[0], Sym):
        return False
    name = str(form[0])
    if name in SELECTOR_PRIMITIVES and len(form) == 2:
        return selector_over(form[1], variable)
    if name.endswith("-nth") and len(form) == 3 and isinstance(form[1], int):
        return selector_over(form[2], variable)
    return False


def accessor_body(body: object, variable: str) -> bool:
    """The body of a one-field accessor, with an `mbe` wrapper stripped."""
    if head(body) == "mbe":
        logic = keyword_plist(body[1:]).get(":logic")
        return logic is not None and selector_over(logic, variable)
    return selector_over(body, variable)


def hand_written_record(tree: "Tree") -> list[dict]:
    """Books whose records are written out instead of generated.

    One finding per book, at its first shape predicate: the pattern is a book
    property, and reporting it per record would repeat the same accessor
    count once per record in the book.
    """
    findings: list[dict] = []
    for book in sorted(tree.books.values(), key=lambda b: b.path):
        written = [f for f in book.functions if not f.generated
                   and len(f.formals) == 1 and isinstance(f.formals[0], Sym)]
        accessors: dict[str, int] = {}
        shapes: dict[str, list[Function]] = {}
        for function in written:
            variable = str(function.formals[0])
            if accessor_body(function.body, variable):
                accessors[variable] = accessors.get(variable, 0) + 1
            elif function.name.endswith("-shapep"):
                shapes.setdefault(variable, []).append(function)
        for variable, found in sorted(shapes.items()):
            count = accessors.get(variable, 0)
            if count < 3:
                continue
            names = ", ".join(sorted(f.name for f in found))
            findings.append({
                "book": book.path, "line": min(f.line for f in found),
                "shape": sorted(f.name for f in found)[0], "shapes": len(found),
                "accessors": count, "variable": variable,
                "reason": (f"hand-written record: {len(found)} shape "
                           f"predicate(s) ({names}) and {count} one-argument "
                           f"selector accessors over `{variable}` are written "
                           "out; books/defrecord.lisp generates this pattern "
                           "with fn-defrecord"),
            })
    return findings


def lint_findings(tree: "Tree") -> dict[str, list[dict]]:
    return {"export_hygiene": export_hygiene(tree),
            "enabled_projection": enabled_projection(tree),
            "teeth_form": teeth_form(tree),
            "include_hygiene": include_hygiene(tree),
            "host_names": host_names(tree),
            "hand_written_record": hand_written_record(tree)}


def lint_warnings(tree: "Tree | None" = None) -> list[str]:
    """One line per finding, for `--check` and `make check`."""
    findings = lint_findings(tree if tree is not None else load_tree())
    lines = []
    for entry in findings["export_hygiene"]:
        lines.append(f"export hygiene: {entry['book']}:{entry['line']}: "
                     f"{entry['theorem']}: {entry['reason']}")
    for entry in findings["enabled_projection"]:
        lines.append(f"enabled projection: {entry['book']}:{entry['line']}: "
                     f"{entry['function']}: {entry['reason']} "
                     f"({', '.join(entry['stated_in'][:4])})")
    for entry in findings["teeth_form"]:
        lines.append(f"teeth form: {entry['book']}:{entry['line']}: "
                     f"{entry['check']}: {entry['reason']}")
    for entry in findings["include_hygiene"]:
        lines.append(f"include hygiene: {entry['book']}:{entry['line']}: "
                     f"{entry['included']}: {entry['reason']}")
    for entry in findings["host_names"]:
        lines.append(f"host names: {entry['host']}:{entry['line']}: "
                     f"{entry['name']}: {entry['reason']}")
    for entry in findings["hand_written_record"]:
        lines.append(f"hand-written record: {entry['book']}:{entry['line']}: "
                     f"{entry['shape']}: {entry['reason']}")
    return lines


# --------------------------------------------------------------------------
# tree, roots and closure
# --------------------------------------------------------------------------


HOST_DIRS = ("host", "host/native")


def book_paths() -> list[tuple[Path, str]]:
    found = []
    for directory in ("books", "tests/acl2"):
        for path in sorted((ROOT / directory).glob("*.lisp")):
            found.append((path, path.relative_to(ROOT).as_posix()))
    return found


def makefile_roots() -> list[str]:
    text = (ROOT / "Makefile").read_text(encoding="utf-8")
    match = re.search(r"(?ms)^ACL2_BOOKS\s*\??=\s*(.*?)(?=^\S|\Z)", text)
    if not match:
        raise ValueError("Makefile: no ACL2_BOOKS assignment")
    body = match.group(1).replace("\\\n", " ")
    return [token for token in body.split() if token]


def root_closure(books: dict[str, Book], roots: list[str]) -> set[str]:
    """Roots plus everything they locally include, as repository paths."""
    closure: set[str] = set()
    pending = [f"{root}.lisp" for root in roots]
    while pending:
        relative = pending.pop()
        if relative in closure:
            continue
        closure.add(relative)
        book = books.get(relative)
        if book is None:
            continue
        base = Path(relative).parent
        for reference in book.includes:
            target = (base / reference).with_suffix(".lisp")
            pending.append(target.as_posix().replace("books/../books/", "books/"))
    return {resolve(relative) for relative in closure}


def resolve(relative: str) -> str:
    parts: list[str] = []
    for part in relative.split("/"):
        if part == "..":
            if parts:
                parts.pop()
        elif part not in ("", "."):
            parts.append(part)
    return "/".join(parts)


def load_tree() -> Tree:
    books = {relative: analyze_book(path, relative) for path, relative in book_paths()}
    return Tree(books, makefile_roots(), load_hosts())


# --------------------------------------------------------------------------
# the generated ledger
# --------------------------------------------------------------------------


GUARD_STATES = ("verified", "declared-off", "default-guarded", "default-unguarded")


def book_row(book: Book, tree: Tree) -> dict:
    guards = {state: 0 for state in GUARD_STATES}
    for function in book.functions:
        guards[function.guard_status] += 1
    suspects = sorted(t.name for t in book.theorems if t.name in tree.suspects)
    return {
        "book": book.path,
        "in_root_closure": book.path in tree.closure,
        "is_root": book.path[:-5] in tree.roots,
        "theorems": len(book.theorems),
        "functions": len(book.functions),
        "guards": guards,
        "verify_guards_events": len(book.verify_guards),
        "assert_events": book.assert_events,
        "must_fails": book.must_fails,
        "defconsts": book.defconsts,
        "defmacros": book.defmacros,
        "encapsulates": book.encapsulates,
        "includes": sorted(book.includes),
        "system_includes": sorted(book.system_includes),
        "suspects": suspects,
        "read_error": book.read_error,
    }


def build_ledger(tree: Tree) -> dict:
    rows = [book_row(book, tree) for book in
            sorted(tree.books.values(), key=lambda b: b.path)]
    totals = {
        "books": len(rows),
        "books_in_root_closure": sum(1 for row in rows if row["in_root_closure"]),
        "roots": len(tree.roots),
        "theorems": sum(row["theorems"] for row in rows),
        "functions": sum(row["functions"] for row in rows),
        "assert_events": sum(row["assert_events"] for row in rows),
        "must_fails": sum(row["must_fails"] for row in rows),
        "encapsulates": sum(row["encapsulates"] for row in rows),
        "guards": {state: sum(row["guards"][state] for row in rows)
                   for state in GUARD_STATES},
        "suspect_theorems": len(tree.suspects),
    }
    lints = lint_findings(tree)
    totals["export_hygiene_warnings"] = len(lints["export_hygiene"])
    totals["enabled_projection_warnings"] = len(lints["enabled_projection"])
    totals["teeth_form_warnings"] = len(lints["teeth_form"])
    totals["include_hygiene_warnings"] = len(lints["include_hygiene"])
    totals["host_names_warnings"] = len(lints["host_names"])
    totals["hand_written_record_warnings"] = len(lints["hand_written_record"])
    suspects = [{"theorem": name,
                 "book": tree.theorems[name].book,
                 "line": tree.theorems[name].line,
                 "reasons": reasons}
                for name, reasons in sorted(tree.suspects.items())]
    return {
        "schema_version": 2,
        "description": ("Generated by tools/ledger.py from books/*.lisp and "
                        "tests/acl2/*.lisp.  Do not edit; run "
                        "`python3 tools/ledger.py --write`."),
        "roots": list(tree.roots),
        "totals": totals,
        "books": rows,
        "suspects": suspects,
        "lints": lints,
    }


def ledger_markdown(ledger: dict) -> str:
    totals = ledger["totals"]
    guards = totals["guards"]
    lines = [
        "# Generated assurance ledger",
        "",
        "Generated by `tools/ledger.py` from `books/*.lisp` and",
        "`tests/acl2/*.lisp`. Do not edit by hand; run",
        "`python3 tools/ledger.py --write`. `make check` fails when this file is",
        "stale. Counts describe artifacts, not coverage; see",
        "[the proof strategy](../docs/proofs.md) for what a count does not mean.",
        "",
        "## Totals",
        "",
        "| Quantity | Count |",
        "| --- | --- |",
        f"| Books read | {totals['books']} |",
        f"| Certification roots in the Makefile | {totals['roots']} |",
        f"| Books inside the root closure | {totals['books_in_root_closure']} |",
        f"| `defthm` and `defthmd` events | {totals['theorems']} |",
        f"| `defun` events | {totals['functions']} |",
        f"| Functions with verified guards | {guards['verified']} |",
        f"| Functions declared `:verify-guards nil` and never verified | {guards['declared-off']} |",
        f"| Functions left at the default with an explicit guard | {guards['default-guarded']} |",
        f"| Functions left at the default with no guard | {guards['default-unguarded']} |",
        f"| `assert-event` checks | {totals['assert_events']} |",
        f"| `must-fail` checks | {totals['must_fails']} |",
        f"| `encapsulate` events | {totals['encapsulates']} |",
        f"| Theorems flagged SUSPECT by shape | {totals['suspect_theorems']} |",
        f"| Export-hygiene warnings | {totals['export_hygiene_warnings']} |",
        f"| Enabled-projection warnings | "
        f"{totals['enabled_projection_warnings']} |",
        f"| Teeth-form warnings | {totals['teeth_form_warnings']} |",
        f"| Include-hygiene warnings | {totals['include_hygiene_warnings']} |",
        f"| Host-names warnings | {totals['host_names_warnings']} |",
        f"| Hand-written-record warnings | "
        f"{totals['hand_written_record_warnings']} |",
        "",
        "## Lints",
        "",
        "Six WARN lints, counted above and listed in full under `lints` in",
        "[`ledger.json`](ledger.json). *Export hygiene* counts theorems a book",
        "leaves enabled whose shape rewrites downstream goals out of accessor",
        "vocabulary: an equality between two one-argument applications, or a",
        "`consp`/`len` conclusion backchained to a `len` hypothesis. A theorem",
        "that is `local`, `defthmd`, `:rule-classes nil`, or disabled by a",
        "closing `in-theory` -- directly, or through a `deftheory` name the",
        "book defines and then withdraws -- is not counted.",
        "*Enabled projection* counts accessors a book ships with the",
        "definition rune ENABLED while a theorem in another book is stated",
        "over them: one formal, a body that is only a walk into it, absent",
        "from the book's closing withdrawal, and mentioned in another book's",
        "theorem statement. Nothing is wrong until something downstream",
        "unfolds one, and then every lemma over that accessor silently stops",
        "matching -- the same shape as a whole-state recognizer left enabled",
        "in a vocabulary, which cost this tree an 8844-subgoal split, a run",
        "killed at the timeout and a two-million-step induction in one day",
        "(2026-09-20). The repair is one name in the book's existing",
        "`deftheory`; the lint does not make it. *Teeth form*",
        "counts `must-fail`",
        "checks whose body is a bare `thm`/`defthm` mentioning no constant, so",
        "nothing in particular is refuted. *Include hygiene* counts non-local",
        "`include-book` forms whose target is a local book that ends with no",
        "theory withdrawal: such an include enables every rule of that book in",
        "the includer and in everything above it. `books/bp-ingress.lisp` took",
        "one for a single guard hint and turned a six-minute proof into an",
        "1800 s timeout. *Host names* counts symbols used in `host/*.lisp` and",
        "`host/native/*.lisp` -- files the bridges `ld` and no certification",
        "reads -- that nothing those files include, `ld` or inherit from",
        "`tools/acl2-builtins.txt` defines: the shape of the",
        "`*fn-store-groups*` reference that survived the group table and broke",
        "every `Acl2Store` start-up. *Hand-written record* counts books",
        "whose records are written out event by event instead of generated",
        "by `fn-defrecord` (`books/defrecord.lisp`): a shape predicate and",
        "three or more one-argument selector accessors over the same",
        "variable. Writing the pattern by hand is correct and is how the",
        "tree lost one of the three forward-chaining shape facts four times",
        "in one cycle, each time for a rule fan; the count is how the",
        "migration stays visible. No lint judges truth;",
        "`python3 tools/ledger.py --check --strict` turns all five into errors.",
        "",
        "## Per book",
        "",
        "Guard columns: verified / declared off / default with a guard / default",
        "with no guard. A book outside the root closure is certified by nothing",
        "that `make certify` requests.",
        "",
        "| Book | Root | Theorems | Functions | Guards | `assert-event` | `must-fail` | Suspect |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in ledger["books"]:
        if row["read_error"]:
            lines.append(f"| `{row['book']}` | unreadable | | | | | | {row['read_error']} |")
            continue
        root = "root" if row["is_root"] else ("closure" if row["in_root_closure"] else "-")
        guard = "/".join(str(row["guards"][state]) for state in GUARD_STATES)
        lines.append(
            f"| `{row['book']}` | {root} | {row['theorems']} | {row['functions']} "
            f"| {guard} | {row['assert_events']} | {row['must_fails']} "
            f"| {len(row['suspects'])} |")
    lines += [
        "",
        "## Theorems flagged SUSPECT by shape",
        "",
        "A flag is a claim about the *shape* of a statement, not about its truth.",
        "Every theorem below is proved; none may be cited as a registry event in",
        "`planning/proof-events.json`. The detector's limits are documented in",
        "[the proof strategy](../docs/proofs.md#the-generated-ledger).",
        "",
        "| Theorem | Book | Line | Why |",
        "| --- | --- | --- | --- |",
    ]
    for entry in ledger["suspects"]:
        why = "; ".join(entry["reasons"]).replace("|", "\\|")
        lines.append(f"| `{entry['theorem']}` | `{entry['book']}` | {entry['line']} | {why} |")
    lines.append("")
    return "\n".join(lines)


# --------------------------------------------------------------------------
# registry validation
# --------------------------------------------------------------------------


def load_proof_events() -> dict:
    return json.loads(PROOF_EVENTS.read_text(encoding="utf-8"))


def validate_events(tree: Tree, curated: dict) -> tuple[list[str], dict[str, list[str]]]:
    """Check the curated map and return (problems, regenerated events arrays)."""
    problems: list[str] = []
    if curated.get("schema_version") != 1:
        problems.append("planning/proof-events.json: unsupported schema_version")
    registry = json.loads(PROOFS.read_text(encoding="utf-8"))
    known = {entry["id"] for entry in registry["proofs"]}
    regenerated: dict[str, list[str]] = {}
    seen: set[str] = set()
    for target in curated.get("targets", []):
        ident = target.get("id", "")
        if ident not in known:
            problems.append(f"planning/proof-events.json: unknown proof target {ident!r}")
            continue
        if ident in seen:
            problems.append(f"{ident}: listed more than once")
        seen.add(ident)
        names: list[str] = []
        for event in target.get("events", []):
            name = event.get("name", "")
            kind = event.get("kind", "theorem")
            if name in names:
                problems.append(f"{ident}: repeated event {name!r}")
            names.append(name)
            if kind == "theorem":
                problems.extend(check_theorem_event(tree, ident, name))
            elif kind == "guarded-function":
                problems.extend(check_function_event(tree, ident, name))
            else:
                problems.append(f"{ident}: event {name!r} has unknown kind {kind!r}")
        regenerated[ident] = names
    for ident in sorted(known - seen):
        entry = next(e for e in registry["proofs"] if e["id"] == ident)
        if entry.get("events"):
            problems.append(f"{ident}: proofs.json lists events but "
                            f"proof-events.json does not cover the target")
        regenerated[ident] = []
    return problems, regenerated


def check_theorem_event(tree: Tree, ident: str, name: str) -> list[str]:
    theorem = tree.theorems.get(name)
    if theorem is None:
        return [f"{ident}: no such theorem in books/ or tests/acl2/: {name}"]
    problems = []
    if theorem.book not in tree.closure:
        problems.append(f"{ident}: {name} lives in {theorem.book}, which no "
                        f"Makefile certification root reaches")
    if name in tree.suspects:
        problems.append(f"{ident}: {name} is SUSPECT ("
                        + "; ".join(tree.suspects[name]) + ")")
    return problems


def check_function_event(tree: Tree, ident: str, name: str) -> list[str]:
    function = tree.functions.get(name)
    if function is None:
        return [f"{ident}: no such function in books/: {name}"]
    problems = []
    if function.book not in tree.closure:
        problems.append(f"{ident}: {name} lives in {function.book}, which no "
                        f"Makefile certification root reaches")
    if function.guard_status != "verified":
        problems.append(f"{ident}: {name} is cited as a guarded function but its "
                        f"guard status is {function.guard_status}")
    return problems


def apply_events(regenerated: dict[str, list[str]]) -> str:
    """``proofs.json`` with regenerated ``events``; everything else untouched."""
    registry = json.loads(PROOFS.read_text(encoding="utf-8"))
    for entry in registry["proofs"]:
        names = regenerated.get(entry["id"], [])
        if names:
            entry["events"] = names
        else:
            entry.pop("events", None)
    return json.dumps(registry, indent=2, ensure_ascii=False) + "\n"


# --------------------------------------------------------------------------
# entry points
# --------------------------------------------------------------------------


def check_problems(tree: "Tree | None" = None) -> list[str]:
    """Everything `make check` must fail on.

    The caller may pass a tree it already loaded; reading 180 books twice to
    produce the same answer is waste, not independence.
    """
    problems: list[str] = []
    tree = load_tree() if tree is None else tree
    for book in tree.books.values():
        if book.read_error:
            problems.append(f"{book.path}: unreadable: {book.read_error}")
    if not PROOF_EVENTS.is_file():
        return problems + ["planning/proof-events.json: missing"]
    curated = load_proof_events()
    event_problems, regenerated = validate_events(tree, curated)
    problems.extend(event_problems)

    ledger = build_ledger(tree)
    for path, expected in ((LEDGER_JSON, json.dumps(ledger, indent=2,
                                                    ensure_ascii=False) + "\n"),
                           (LEDGER_MD, ledger_markdown(ledger)),
                           (PROOFS, apply_events(regenerated))):
        relative = path.relative_to(ROOT).as_posix()
        if not path.is_file():
            problems.append(f"{relative}: missing; run `python3 tools/ledger.py --write`")
        elif path.read_text(encoding="utf-8") != expected:
            problems.append(f"{relative}: stale; run `python3 tools/ledger.py --write`")
    return problems


def write_all() -> list[str]:
    tree = load_tree()
    curated = load_proof_events()
    problems, regenerated = validate_events(tree, curated)
    ledger = build_ledger(tree)
    LEDGER_JSON.write_text(json.dumps(ledger, indent=2, ensure_ascii=False) + "\n",
                           encoding="utf-8")
    LEDGER_MD.write_text(ledger_markdown(ledger), encoding="utf-8")
    PROOFS.write_text(apply_events(regenerated), encoding="utf-8")
    return problems


def report(tree: Tree) -> None:
    ledger = build_ledger(tree)
    totals = ledger["totals"]
    print(f"{totals['books']} books, {totals['theorems']} theorems, "
          f"{totals['functions']} functions, {totals['roots']} certification roots.")
    print("guards: " + ", ".join(f"{state}={totals['guards'][state]}"
                                 for state in GUARD_STATES))
    print(f"{totals['assert_events']} assert-event, {totals['must_fails']} must-fail, "
          f"{totals['encapsulates']} encapsulate.")
    print(f"{totals['suspect_theorems']} theorems flagged SUSPECT by shape.")
    for entry in ledger["suspects"]:
        print(f"  {entry['theorem']} ({entry['book']}:{entry['line']})")
        for reason in entry["reasons"]:
            print(f"      {reason}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true",
                        help="regenerate ledger.json, ledger.md and proofs.json events")
    parser.add_argument("--check", action="store_true",
                        help="fail on an unknown or SUSPECT cited theorem, or stale output")
    parser.add_argument("--strict", action="store_true",
                        help="with --check, fail on any lint warning: export "
                             "hygiene, teeth form, include hygiene or host names")
    arguments = parser.parse_args(argv)
    if arguments.check:
        tree = load_tree()
        problems = check_problems(tree)
        warnings = lint_warnings(tree)
        for problem in problems:
            print(f"ERROR: {problem}", file=sys.stderr)
        for warning in warnings:
            print(f"WARN: {warning}", file=sys.stderr)
        if problems or (warnings and arguments.strict):
            return 1
        print(f"Ledger OK: generated counts, cited events and registry are "
              f"current; {len(warnings)} lint warnings.")
        return 0
    if arguments.write:
        problems = write_all()
        for problem in problems:
            print(f"ERROR: {problem}", file=sys.stderr)
        print(f"Wrote {LEDGER_JSON.relative_to(ROOT)}, {LEDGER_MD.relative_to(ROOT)} "
              f"and the {PROOFS.relative_to(ROOT)} event arrays.")
        return 1 if problems else 0
    report(load_tree())
    return 0


if __name__ == "__main__":
    sys.exit(main())
