#!/usr/bin/env python3
"""Generate fn's assurance ledger from the books, and check the proof registry.

Counts in fn are generated, never typed.  This tool reads ``books/*.lisp`` and
``tests/acl2/*.lisp`` with the s-expression reader in this file.  It is not the
Lisp reader: nothing is interned, evaluated, or macro-expanded, so reading a
book cannot run a book.  The books are our own source, but the rule that
parsing never invokes the reader holds for them too.

What it reports per book: every ``defthm``, ``defun``, ``verify-guards``,
``must-fail``, ``assert-event`` and ``include-book``; the guard status of every
function; and the theorems whose *shape* disqualifies them as registry
evidence.

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


def record(book: Book, form: object, line: int, *, local: bool, suppressed: bool) -> None:
    name = head(form)
    if name is None:
        return
    if name in TRANSPARENT:
        inner_local = local or name == "local"
        for item in form[1:]:
            record(book, item, line, local=inner_local, suppressed=suppressed)
        return
    if name == "encapsulate":
        if not suppressed:
            book.encapsulates += 1
        for item in form[2:]:
            record(book, item, line, local=local, suppressed=suppressed)
        return
    if name in SUPPRESSING:
        if name.startswith("must-fail") and not suppressed:
            book.must_fails += 1
            book.must_fail_forms.append((line, list(form[1:])))
        for item in form[1:]:
            record(book, item, line, local=local, suppressed=True)
        return
    if name == "make-event":
        return  # not statically readable; reporting it as an event would be a guess
    if suppressed:
        return
    if name in ("defthm", "defthmd") and len(form) >= 3 and isinstance(form[1], Sym):
        options = keyword_plist(form[3:])
        book.theorems.append(Theorem(
            name=str(form[1]), book=book.path, line=line, statement=form[2],
            hints=options.get(":hints"), rest=list(form[3:]), local=local,
            disabled=name == "defthmd"))
        return
    if name in ("defun", "defund", "defun-nx") and len(form) >= 4 and isinstance(form[1], Sym):
        has_guard, setting = declared(form[3:])
        book.functions.append(Function(
            name=str(form[1]), book=book.path, line=line,
            formals=form[2] if isinstance(form[2], list) else [],
            body=form[-1], declared_guard=has_guard,
            verify_guards_decl=setting, local=local))
        return
    if name == "verify-guards" and len(form) >= 2 and isinstance(form[1], Sym):
        book.verify_guards.append(str(form[1]))
        return
    if name == "include-book" and len(form) >= 2 and isinstance(form[1], str):
        if ":dir" in keyword_plist(form[2:]):
            book.system_includes.append(form[1])
        else:
            book.includes.append(form[1])
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
        return
    if name == "defmacro":
        book.defmacros += 1
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

    def __init__(self, books: dict[str, Book], roots: list[str]) -> None:
        self.books = books
        self.roots = roots
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
# Two shape lints, both WARN by default and both counted in the generated
# ledger.  Neither is a claim that a theorem is wrong: they name the two ways
# this tree has repeatedly made later proofs expensive.
#
# * Export hygiene.  A book's micro discipline (`planning/deputies/BRIEF.md`)
#   is that accessor equalities and `len` backchaining rules stay inside the
#   book that needs them: `:rule-classes nil`, `local`, `defthmd`, or a
#   closing `in-theory (disable ...)`.  One such rule left enabled rewrites
#   every downstream goal out of accessor vocabulary.
# * Teeth form.  A `must-fail` whose body is a bare `thm` over free variables
#   shows only that ACL2 did not prove a general claim, which a typo also
#   achieves.  Teeth are concrete: a specific violating value.

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


def lint_findings(tree: "Tree") -> dict[str, list[dict]]:
    return {"export_hygiene": export_hygiene(tree), "teeth_form": teeth_form(tree)}


def lint_warnings(tree: "Tree | None" = None) -> list[str]:
    """One line per finding, for `--check` and `make check`."""
    findings = lint_findings(tree if tree is not None else load_tree())
    lines = []
    for entry in findings["export_hygiene"]:
        lines.append(f"export hygiene: {entry['book']}:{entry['line']}: "
                     f"{entry['theorem']}: {entry['reason']}")
    for entry in findings["teeth_form"]:
        lines.append(f"teeth form: {entry['book']}:{entry['line']}: "
                     f"{entry['check']}: {entry['reason']}")
    return lines


# --------------------------------------------------------------------------
# tree, roots and closure
# --------------------------------------------------------------------------


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
    return Tree(books, makefile_roots())


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
    totals["teeth_form_warnings"] = len(lints["teeth_form"])
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
        f"| Teeth-form warnings | {totals['teeth_form_warnings']} |",
        "",
        "## Lints",
        "",
        "Two WARN lints, counted above and listed in full under `lints` in",
        "[`ledger.json`](ledger.json). *Export hygiene* counts theorems a book",
        "leaves enabled whose shape rewrites downstream goals out of accessor",
        "vocabulary: an equality between two one-argument applications, or a",
        "`consp`/`len` conclusion backchained to a `len` hypothesis. A theorem",
        "that is `local`, `defthmd`, `:rule-classes nil`, or disabled by a",
        "closing `in-theory` -- directly, or through a `deftheory` name the",
        "book defines and then withdraws -- is not counted. *Teeth form*",
        "counts `must-fail`",
        "checks whose body is a bare `thm`/`defthm` mentioning no constant, so",
        "nothing in particular is refuted. Neither lint judges truth;",
        "`python3 tools/ledger.py --check --strict` turns both into errors.",
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
                        help="with --check, fail on export-hygiene and teeth-form warnings")
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
