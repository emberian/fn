#!/usr/bin/env python3
"""The Lisp reader and tree analyser the tools share: books, test books, host files.

Nothing is interned, evaluated or macro-expanded: reading a book cannot run a
book.  ``Reader`` and ``read_forms`` read s-expressions; ``head``,
``keyword_plist`` and ``conjuncts`` take them apart; ``generated_expansion``
mirrors the generators (def-loop, defrecord, defprotocol, defteeth, ...);
``analyze_book`` and ``analyze_host`` give a ``Book`` or ``HostFile`` per
file; ``makefile_roots`` and ``root_closure`` read the Makefile's
certification roots; ``load_tree`` is the whole analysed ``Tree``, persisted
under build/cache/ledger-tree by its inputs' digest (``FN_LEDGER_FORMS_CACHE``
names the per-text forms cache a box shares between worktrees).

The proof registry this file once generated and checked (planning/proofs.json,
proof-events.json, proof-retirements.json; the --check, --write, --repoint,
--retire and --restore commands) left with the registers on cut/breaking
(M1-d, 2026-10-17).  OWED.md is the ledger.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
# One module under both names.  `from tools import ledger' (interface_emit,
# harness_check, check_scaffold, ...) and `import ledger' (green_check,
# depth_check, ...) made two module objects, so a tree cache entry pickled by
# one (its classes named `ledger.Tree') failed the other's isinstance check
# and was analysed again, four minutes on persvati, in three of make check's
# steps at once (check-parallel, 2026-09-29).  Imported as `tools.ledger',
# this file registers itself as `ledger' and names its classes so; imported
# as `tools.ledger' after `ledger', the import returns that module (this
# body's remaining definitions go nowhere).
if __name__ == "tools.ledger":
    if "ledger" in sys.modules:
        sys.modules[__name__] = sys.modules["ledger"]
    else:
        sys.modules["ledger"] = sys.modules[__name__]
    __name__ = "ledger"  # noqa: A001 -- the classes below pickle as ledger.X
ROOT = Path(__file__).resolve().parents[1]
class Sym(str):
    """A symbol.  A Lisp string literal reads as a plain ``str``; this is not."""

    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"Sym({str.__repr__(self)})"


DELIMITERS = set("()'\"`,; \t\n\r\f")
class ReadError(ValueError):
    """The source is not readable as s-expressions."""


class Reader:
    """Read s-expressions without interning, evaluating, or expanding."""

    def __init__(self, source: str) -> None:
        self.source = source
        self.pos = 0
        self._line_at = (0, 1)

    def line(self, position: int) -> int:
        # Counted on from the last position asked (top_level asks in
        # increasing order): counting from the start each time made a read
        # of N forms O(N x length) -- 12 minutes of make check for
        # host_check --load's read of the whole world's text (X17).
        at, number = self._line_at
        if position < at:
            at, number = 0, 1
        number += self.source.count("\n", at, position)
        self._line_at = (position, number)
        return number

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
        """Every top-level form, paired with the line it starts on.

        A whole text read from its start is answered from the per-text cache
        (`_cached_top_level`): the same bytes always read the same. The
        returned forms are shared read-only data; copy locally before editing."""
        if self.pos == 0 and type(self) is Reader and len(self.source) >= _FORMS_CACHE_MIN:
            return _cached_top_level(self)
        return self._top_level()

    def _top_level(self) -> list[tuple[object, int]]:
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


# A delimiter run: whitespace, or a `;` comment through its newline.
_CANONICAL_GAP = re.compile(r"(?:[ \t\n\r\f]+|;[^\n]*(?:\n|\Z))+")
# One token: a terminating macro character, a string, or a run of
# constituents with `\\x` and `|...|` escapes (a `#` mid-token is a constituent,
# so `a#|b|#c` is one symbol, as it is to ACL2).
_CANONICAL_TOKEN = re.compile(
    r"""[()'`,]|"(?:[^"\\]+|\\.)*"|(?:[^ \t\n\r\f()'`,";\\|]+|\\.|\|(?:[^|\\]+|\\.)*\|)+""",
    re.DOTALL)
_BLOCK_MARK = re.compile(r"#\||\|#")
# The same scan as one substitution, for a source with no `#|`: every string,
# `|...|` and `\\x` is kept (so a `;` or blank inside one is not a delimiter)
# and every delimiter run becomes one space.
_CANONICAL_FAST = re.compile(
    r"""("(?:[^"\\]+|\\.)*"|\|(?:[^|\\]+|\\.)*\||\\.)|(?:[ \t\n\r\f]+|;[^\n]*(?:\n|\Z))+""",
    re.DOTALL)
def _canonical_piece(match: re.Match) -> str:
    return match.group(1) or " "


def canonical_text(source: str) -> str:
    """``source`` with every comment and whitespace run made one space.

    The cache key of a certificate (``tools/certs.py``) hashes this, so a
    comment-only or layout-only edit keeps the key.  The rule it must keep:
    two sources with the same canonical text are read by ACL2 as the same
    forms.  It does, because it only replaces what the Common Lisp reader
    treats as a delimiter -- a run of whitespace, a ``;`` comment up to its
    newline, a ``#|...|#`` comment (nested) that starts a token -- by one
    space, and keeps every token byte for byte: strings with their escapes,
    ``|...|`` and ``\\`` escapes inside symbols, character names, ``#``
    dispatches.  Nothing is lowercased, parsed as a number or interned (that
    is `Reader`'s job and would conflate what ACL2 distinguishes, ``|Foo|``
    against ``foo``).  Where a gap is optional (``(a)`` against ``( a )``)
    the texts differ, which only costs a recertification.  Docstrings are
    strings, so they stay: ACL2's book-hash covers them.
    """
    if "#|" not in source and source.count('"') % 2 == 0:
        return _CANONICAL_FAST.sub(_canonical_piece, source).strip(" ")
    return _canonical_slow(source)


def _canonical_slow(source: str) -> str:
    out: list[str] = []
    n = len(source)
    i = 0
    gap = False
    while i < n:
        m = _CANONICAL_GAP.match(source, i)
        if m:
            gap, i = True, m.end()
            continue
        if source.startswith("#|", i):
            depth, j = 1, i + 2
            while j < n and depth:
                k = _BLOCK_MARK.search(source, j)
                if k is None:
                    break
                depth += 1 if k.group() == "#|" else -1
                j = k.end()
            if depth:
                raise ReadError("unterminated block comment")
            gap, i = True, j
            continue
        m = _CANONICAL_TOKEN.match(source, i)
        if not m:
            raise ReadError(f"unterminated string or escape at line {source.count(chr(10), 0, i) + 1}")
        if gap and out:
            out.append(" ")
        gap = False
        out.append(m.group())
        i = m.end()
    return "".join(out)


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


# The per-text read cache (lane loops, 2026-10-04).  One certify_books
# --lane run read the same ~1,300 books 19,163 times (local_closure from
# scratch per book in lane_edges: 426 of its 544 profiled seconds), and
# host_check --load 13,137 times (288 s); proof_repl start 3 times a book.
# A text's forms are a function of its bytes and this reader, so an entry
# is named by the digest of both and is valid exactly when its name
# matches. Callers only read forms (including retained bodies and generator
# inputs); transformations build new lists. Share the parsed list in-process
# so repeat reads do not unpickle it again. Then build/cache/ledger-forms/ (one file per
# text; a reader change starts a new format directory and removes the old
# ones).  FN_LEDGER_FORMS_CACHE=0 turns the disk half off; a path moves it.
_FORMS_CACHE_MIN = 2048
_FORMS_MEMO: dict[bytes, list[tuple[object, int]]] = {}
_FORMS_FORMAT: "str | None" = None
def _forms_format() -> str:
    global _FORMS_FORMAT
    if _FORMS_FORMAT is None:
        _FORMS_FORMAT = hashlib.sha256(b"fn-ledger-forms-1\0" + Path(__file__).resolve()
                                       .read_bytes()).hexdigest()[:24]
    return _FORMS_FORMAT


def _forms_cache_dir() -> "Path | None":
    setting = os.environ.get("FN_LEDGER_FORMS_CACHE", "")
    if setting == "0":
        return None
    base = Path(setting) if setting else Path(__file__).resolve().parents[1] / "build" / "cache" / "ledger-forms"
    return base / _forms_format()


def _cached_top_level(reader: "Reader") -> list[tuple[object, int]]:
    import pickle
    key = hashlib.sha256(reader.source.encode("utf-8", "surrogatepass")).digest()
    forms = _FORMS_MEMO.get(key)
    if forms is not None:
        reader.pos = len(reader.source)
        return forms
    directory = _forms_cache_dir()
    data = None
    if directory is not None:
        try:
            data = (directory / key.hex()[:2] / (key.hex() + ".pickle")).read_bytes()
        except OSError:
            pass
    if data is not None:
        try:
            forms = pickle.loads(data)
        except Exception:
            forms = None
        if isinstance(forms, list):
            _FORMS_MEMO[key] = forms
            reader.pos = len(reader.source)
            return forms
    forms = reader._top_level()
    _FORMS_MEMO[key] = forms
    if directory is not None:
        data = pickle.dumps(forms, protocol=pickle.HIGHEST_PROTOCOL)
        _forms_cache_write(directory, key.hex(), data)
    return forms


def _forms_cache_write(directory: Path, name: str, data: bytes) -> None:
    try:
        if not directory.is_dir():
            directory.mkdir(parents=True, exist_ok=True)
            # Another reader's format (an older ledger.py) goes once nothing
            # has created it for a day: a shared directory (a box's runs, by
            # FN_LEDGER_FORMS_CACHE) may hold two versions' readers at once.
            for other in directory.parent.iterdir():
                if (other.is_dir() and other != directory
                        and time.time() - other.stat().st_mtime > 86400):
                    import shutil
                    shutil.rmtree(other, ignore_errors=True)
        sub = directory / name[:2]
        sub.mkdir(exist_ok=True)
        temporary = sub / ".{}.{}.tmp".format(name, os.getpid())
        temporary.write_bytes(data)
        os.replace(temporary, sub / (name + ".pickle"))
    except OSError:
        pass  # a cache that cannot be written is a slower run, never a wrong one


def read_forms(source: str) -> list:
    """Every top-level form of ``source``."""
    return [form for form, _line in Reader(source).top_level()]


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


def conjuncts(form: object, _seen: set[int] | None = None) -> list:
    """Flatten a top-level ``and``."""
    if head(form) == "and":
        _seen = set() if _seen is None else _seen
        if id(form) in _seen:
            return []  # repeated shared AND is idempotent
        _seen.add(id(form))
        out: list = []
        for item in form[1:]:
            out.extend(conjuncts(item, _seen))
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


def calls(form: object, found: set[str] | None = None,
          _seen: set[int] | None = None) -> set[str]:
    """Every symbol in function position, quoted subforms excluded."""
    found = set() if found is None else found
    if not isinstance(form, list) or not form:
        return found
    if head(form) == "quote":
        return found
    _seen = set() if _seen is None else _seen
    if id(form) in _seen:
        return found
    _seen.add(id(form))
    if isinstance(form[0], Sym):
        found.add(str(form[0]))
    for item in form[1:] if isinstance(form[0], Sym) else form:
        calls(item, found, _seen)
    return found


def substitute(form: object, bindings: dict[str, object]) -> object:
    """Replace free variable occurrences.  Binding forms are not tracked; see
    ``docs/proofs.md`` for what that costs the suspect detector."""
    memo: dict[int, object] = {}
    work = 0
    allocated = 0

    def walk(term: object) -> object:
        nonlocal work, allocated
        work += 1
        if work > NORMALIZATION_WORK:
            raise AnalysisIncomplete("substitution work budget exhausted")
        if isinstance(term, Sym):
            return bindings.get(str(term), term)
        if not isinstance(term, list) or head(term) == "quote":
            return term
        if id(term) in memo:
            return memo[id(term)]
        allocated += len(term) + 1
        if allocated > NORMALIZATION_LIMIT:
            raise AnalysisIncomplete("substitution allocation budget exhausted")
        result: list = []
        for index, item in enumerate(term):
            # ACL2 has separate function/variable namespaces.
            value = item if index == 0 and isinstance(item, Sym) else walk(item)
            result.append(value)
        memo[id(term)] = result
        return result

    return walk(form)


def normalise_null(form: object, _memo: dict | None = None) -> object:
    """Rewrite every ``(null x)`` to ``(equal x nil)``.

    The two are the same proposition and the shape detectors below must not
    depend on which one a lemma spells, because the spelling is FORCED: a
    ``(null x)`` conclusion generates no rewrite rule at all -- ACL2 answers
    that its own NULL rule subsumes the proposed one and declines to store
    it -- so a ``-unfolds`` lemma has to write ``(equal x nil)`` where the
    definition it restates writes ``(null x)``.  Measured 2026-09-20 (lane
    w11/bytestore-k2): fn-sf-frontier-rollback-visiblep-unfolds WAS flagged
    recognizer-body-conclusion while its emptiness conjunct read ``(null
    (fn-sf-successes s))``, and stopped being flagged the moment that
    conjunct had to change.  The SUSPECT count held at 46 across that
    change and the stability was an artefact.
    """
    if isinstance(form, list):
        _memo = {} if _memo is None else _memo
        if id(form) in _memo:
            return _memo[id(form)]
        parts = [normalise_null(part, _memo) for part in form]
        if head(form) == "null" and len(parts) == 2:
            parts = [Sym("equal"), parts[1], Sym("nil")]
        _memo[id(form)] = parts
        return parts
    return form


def same(left: object, right: object) -> bool:
    """Structural equality up to ``(null x)`` / ``(equal x nil)``."""
    return same_exact(normalise_null(left), normalise_null(right))


def same_exact(left: object, right: object, _memo: dict | None = None) -> bool:
    """Structural equality that keeps symbols and string literals distinct."""
    if isinstance(left, Sym) != isinstance(right, Sym):
        return False
    if isinstance(left, list) and isinstance(right, list):
        _memo = {} if _memo is None else _memo
        key = (id(left), id(right))
        if key in _memo:
            return _memo[key]
        if len(_memo) > NORMALIZATION_WORK:
            raise AnalysisIncomplete("comparison work budget exhausted")
        equal = (len(left) == len(right)
                 and all(same_exact(a, b, _memo) for a, b in zip(left, right)))
        _memo[key] = equal
        return equal
    if isinstance(left, list) or isinstance(right, list):
        return False
    return type(left) is type(right) and left == right


REFLEXIVE = {"equal", "iff", "=", "subsetp", "subsetp-equal", "fn-subsetp"}
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
    # Functions an `encapsulate' signature introduces: constrained, with no
    # definition outside it (a codec seam's public names, a named assumption).
    constrained: set[str] = field(default_factory=set)
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
    # defmacro name -> its body forms (after the lambda list).
    macro_bodies: dict[str, list] = field(default_factory=dict)
    # The theorem names of must-fails a ``defkeystone`` or ``defteeth``
    # generated beside a ground counterexample (its removal or mutant witness).
    paired_must_fails: set[str] = field(default_factory=set)
    # Keystone name -> the parsed ``defteeth``/``defkeystone`` spec that
    # declares its teeth (TEETH CONTRACT v1): tools/keystone_emit.py builds the
    # obligation manifest from these, and from ``teeth_owed``, the
    # ``(table fn-teeth-owed 'NAME ROW)`` rows a generator emits (name -> row).
    teeth_declared: dict[str, dict] = field(default_factory=dict)
    teeth_owed: dict[str, list] = field(default_factory=dict)
    # (line, reason) for each `must-fail' labelled `; teeth: prover-refusal
    # REASON' in the comment block directly above it: a refusal of proof
    # search, not a necessity witness (PKT-341; see PROVER_REFUSAL).
    prover_refusals: list[tuple[int, str]] = field(default_factory=list)
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
SUPPRESSING = {"must-fail", "must-fail!", "must-fail-checked", "must-succeed", "must-succeed*",
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


# A `must-fail' of a weakened theorem shows only that the prover did not find
# a proof.  Where no counter-witness can be evaluated (a program of 2^64
# octets; a stobj recogniser false of no executable value) that is all it
# shows, and counting it as a tooth claims a necessity nobody exhibited
# (PKT-341).  The test book says so in the comment block directly above the
# form:
#     ; teeth: prover-refusal REASON
# and the ledger and tools/teeth_check.py count such must-fails apart.
PROVER_REFUSAL = re.compile(r"^\s*;+\s*teeth:\s*prover-refusal\b\s*(.*)$")
def prover_refusal_labels(lines: list[str], line: int) -> str | None:
    """The REASON of a `; teeth: prover-refusal REASON' comment in the block
    of comment lines directly above LINE (1-based), or None."""
    index = line - 2
    while index >= 0 and lines[index].lstrip().startswith(";"):
        match = PROVER_REFUSAL.match(lines[index])
        if match:
            return match.group(1).strip() or "(no reason given)"
        index -= 1
    return None


def analyze_book(path: Path, relative: str) -> Book:
    book = Book(path=relative)
    try:
        text = path.read_text(encoding="utf-8")
        forms = Reader(text).top_level()
    except ReadError as exc:
        book.read_error = str(exc)
        return book
    for form, line in forms:
        record(book, form, line, local=False, suppressed=False)
    if book.must_fail_forms:
        lines = text.splitlines()
        for line, _ in book.must_fail_forms:
            reason = prover_refusal_labels(lines, line)
            if reason is not None:
                book.prover_refusals.append((line, reason))
    for expression in book.in_theory_forms:
        collect_disabled(expression, book.disabled_rules, book.theories)
    verified = set(book.verify_guards)
    for function in book.functions:
        if function.name in verified:
            function.verified_by_event = True
    return book


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


def def_loop_bodies(name: str, formals: list, options: dict) -> tuple:
    """Logic and executable bodies from books/def-loop.lisp's event builders.

    Keep the term structure: consumers also inspect tail position, guards
    and bindings, not just mentions. No Lisp evaluation or world lookup.
    """
    def term(fn, *args):
        return [Sym(fn), *args]

    def present(value):
        return value is not None and value != Sym("nil") and value != []

    shape = str(options.get(":shape", ":map"))
    st = options.get(":into")
    xs = options.get(":over")
    if not present(xs):
        xs = next((f for f in formals if shape != ":into" or f != st), Sym("nil"))
    n = options.get(":count", formals[0] if formals else Sym("nil"))
    elt = options.get(":elt")

    def subst(value):
        if present(elt) and isinstance(value, Sym) and value == elt:
            return term("car", xs)
        if isinstance(value, list) and head(value) != "quote":
            return [subst(v) for v in value]
        return value

    def option(key, default="nil"):
        return subst(options.get(key, Sym(default)))

    body, tail = option(":body"), option(":tail")
    acc = options.get(":acc", Sym("acc"))
    loop = str(options.get(":loop") or name + "-loop")
    next_args = [term("cdr", xs) if f == xs else
                 term("-", n, 1) if shape == ":take" and f == n else f for f in formals]
    rec = term(name, *next_args)
    again = lambda value: term(loop, *next_args, value)
    test = term("consp", xs)
    if shape == ":fold":
        # books/def-loop.lisp fn-dl-fold-events: ST threads through every step;
        # ROW is an (mv ROW-VALUE ST) term and both bodies return (mv ROWS ST).
        # The recursion's state is the list SVARS of the formals NEXT changes.
        fold_st = options.get(":st")
        fail = option(":fail", ":bad")
        svars = [xs] if not isinstance(options.get(":over"), list) else list(options[":over"])
        terms = [option(":next")] if len(svars) == 1 else [subst(t) for t in options.get(":next", [])]
        call_args = [terms[svars.index(f)] if f in svars else f for f in formals]
        recur, step_loop = term(name, *call_args), lambda row: term(loop, *call_args, row)
        done_test, bindings = option(":done"), option(":let")
        let_wrap = (lambda x: term("let*", bindings, x)) if present(bindings) else (lambda x: x)
        mvs = lambda *v: term("mv", *v)
        failed = lambda var: term("if", term("eq", var, fail), mvs(fail, fold_st))
        logic = term("if", done_test, mvs(Sym("nil"), fold_st),
                     let_wrap(term("mv-let", [Sym("dl-row"), fold_st], option(":row"),
                                   failed(Sym("dl-row"))
                                   + [term("mv-let", [Sym("dl-rest"), fold_st], recur,
                                           failed(Sym("dl-rest"))
                                           + [mvs(term("cons", Sym("dl-row"), Sym("dl-rest")), fold_st)])])))
        loop_body = term("if", done_test, mvs(term("revappend", acc, Sym("nil")), fold_st),
                         let_wrap(term("mv-let", [Sym("dl-row"), fold_st], option(":row"),
                                       failed(Sym("dl-row"))
                                       + [step_loop(term("cons", Sym("dl-row"), acc))])))
        return logic, loop_body
    if shape == ":into":
        logic = term("if", test,
                     term("let", [[st, [options.get(":write"), body, st]]], rec), st)
        return logic, logic
    if shape == ":sum":
        return (term("if", test, term("+", body, rec), 0),
                term("if", test, again(term("+", body, acc)), acc))
    if shape == ":concat":
        return (term("if", test, term("append", body, rec), Sym("nil")),
                term("if", test, again(term("revappend", body, acc)),
                     term("revappend", acc, Sym("nil"))))
    logic_inner, loop_inner = term("cons", body, rec), again(term("cons", body, acc))
    fixed = term("true-list-fix", acc) if options.get(":acc-fix") == Sym("t") else acc
    done = term("revappend", fixed, tail)
    if shape == ":take" and present(options.get(":base")):
        return (term("if", option(":base"), tail, logic_inner),
                term("if", option(":base"), done, loop_inner))
    if shape == ":take":
        test = term("not", term("zp", n))
    while_term = option(":while", "t")
    if while_term != Sym("t"):
        test = term("and", test, while_term)
    if shape == ":map":
        keep = option(":keep", "t")
        if options.get(":keep-order") == Sym(":skip-first"):
            logic_inner = term("if", keep, rec, logic_inner)
            loop_inner = term("if", keep, again(acc), loop_inner)
        elif keep != Sym("t"):
            logic_inner = term("if", keep, logic_inner, rec)
            loop_inner = term("if", keep, loop_inner, again(acc))
        if present(options.get(":stop")):
            logic_inner = term("if", option(":stop"), option(":stop-value"), logic_inner)
            loop_inner = term("if", option(":stop"),
                              term("revappend", fixed, option(":stop-value")), loop_inner)
        bindings = option(":let")
        if present(bindings):
            logic_inner = term("let*", bindings, logic_inner)
            loop_inner = term("let*", bindings, loop_inner)
        if present(options.get(":base")):
            # :map :base TERM is base-first (books/def-loop.lisp: (if BASE TAIL INNER)).
            return (term("if", option(":base"), tail, logic_inner),
                    term("if", option(":base"), done, loop_inner))
    return term("if", test, logic_inner, tail), term("if", test, loop_inner, done)


def def_loop_expansion(form: list) -> list:
    """The events ``(def-loop NAME FORMALS ...)`` generates, as the ledger sees them.

    books/def-loop.lisp owns the loop twin: the accumulator loop
    ``NAME-loop`` (``:verify-guards nil``, verified after the local bridge),
    the wrapper ``NAME`` whose ``mbe`` runs the loop, the local bridge
    ``NAME-loop-is-revappend`` (``-is-plus`` for ``:sum``), the two
    ``verify-guards`` and the withdrawal of the loop.  A ``:into`` form
    defines ``NAME`` alone with the exported ``NAME-is-append``.  The bodies
    preserve the generated term structure; proof hints and table rows are
    omitted, and bridge statements match the templates exactly.
    The ledger reads
    names, guards and ``verify-guards``, and the macro is proved by
    tests/acl2/def-loop-tests.lisp.
    """
    if not (len(form) >= 3 and isinstance(form[1], Sym) and isinstance(form[2], list)):
        return []
    name = str(form[1])
    formals = [item for item in form[2] if isinstance(item, Sym)]
    options = keyword_plist(form[3:])
    shape = str(options.get(":shape", Sym(":map")))
    guard = options.get(":guard", Sym("t"))
    acc = options.get(":acc", Sym("acc"))
    loop = str(options.get(":loop") or Sym(name + "-loop"))
    body, loop_body = def_loop_bodies(name, formals, options)
    if shape == ":into":
        stobj = options.get(":into")
        map_formals = list(formals)
        if stobj in map_formals:
            map_formals.remove(stobj)  # ACL2 remove1-eq preserves formal order.
        decl = [Sym("declare"), [Sym("xargs"), Sym(":stobjs"), stobj, Sym(":guard"), guard]]
        for key in (":guard-hints", ":measure"):
            if key in options:
                decl[1] += [Sym(key), options[key]]
        return [[Sym("defun"), Sym(name), list(formals), decl, body],
                [Sym("defthm"), Sym(f"{name}-is-append"),
                 [Sym("implies"), [Sym("true-listp"), stobj],
                  [Sym("equal"), [Sym(name)] + list(formals),
                   [Sym("append"), stobj, [options.get(":map", Sym("nil"))] + map_formals]]]],
                [Sym("in-theory"), [Sym("disable"), Sym(name)]]]
    acc_fix = str(options.get(":acc-fix", Sym("nil"))) == "t"
    # :concat shares the map bridge signature and list accumulator guard.
    # :base selects the base-first :map/:take shape and its library proof.
    # It changes no emitted name, guard, or bridge statement.
    # :keep-order only selects branch order and its library proof; emitted
    # names, guards and bridge statements are identical for both orders.
    acc_pred = Sym("acl2-numberp") if shape == ":sum" else Sym("true-listp")
    acc_guard: object = [acc_pred, acc]
    if not (isinstance(guard, Sym) and str(guard) == "t"):
        acc_guard = [Sym("and"), guard, acc_guard]
    if acc_fix:
        acc_guard = guard
    if str(options.get(":loop-guard", Sym(":default"))) != ":default":
        acc_guard = options[":loop-guard"]
    loop_decl = [Sym("declare"), [Sym("xargs"), Sym(":guard"), acc_guard,
                                  Sym(":verify-guards"), Sym("nil")]]
    name_decl = [Sym("declare"), [Sym("xargs"), Sym(":guard"), guard,
                                  Sym(":verify-guards"), Sym("nil")]]
    stobjs = options.get(":stobjs")
    if stobjs and str(stobjs) != "nil":
        stobjs = [stobjs] if isinstance(stobjs, Sym) else stobjs
        loop_decl[1] += [Sym(":stobjs"), stobjs]
        name_decl[1] += [Sym(":stobjs"), stobjs]
    if ":measure" in options:
        loop_decl[1] += [Sym(":measure"), options[":measure"]]
        name_decl[1] += [Sym(":measure"), options[":measure"]]
    bridge = f"{loop}-is-plus" if shape == ":sum" else f"{loop}-is-revappend"
    statement = [Sym("equal"), [Sym(loop)] + list(formals) + [acc],
                 [Sym("+" if shape == ":sum" else "revappend"),
                  [Sym("true-list-fix"), acc] if acc_fix else acc,
                  [Sym(name)] + list(formals)]]
    if shape == ":sum":
        statement = [Sym("implies"), [Sym("acl2-numberp"), acc], statement]
    unit = 0 if shape == ":sum" else Sym("nil")
    return [[Sym("defun"), Sym(loop), list(formals) + [acc], loop_decl, loop_body],
            [Sym("defun"), Sym(name), list(formals), name_decl,
             [Sym("mbe"), Sym(":logic"), body,
              Sym(":exec"), [Sym(loop)] + list(formals) + [unit]]],
            [Sym("local"), [Sym("defthm"), Sym(bridge), statement]],
            [Sym("verify-guards"), Sym(loop)],
            [Sym("verify-guards"), Sym(name)],
            [Sym("in-theory"), [Sym("disable"), Sym(loop)]]]


def defprotocol_expansion(form: list) -> list:
    """The host-reached macro ``(defprotocol NAME ROWS...)`` defines, as read.

    books/protocol-table.lisp's ``defprotocol`` defines the reader
    dispatchers' command layer ``fn-nntp-command-dispatch`` (lane
    defprotocol-2), whose expansion ``fn-proto-command-dispatch-term``
    computes from the table: the :pinned rows' :arms are in it (today
    XFNCATCHUP's ``fn-cu-serve-reply``).  A reader that never evaluates sees
    the macro only here: one ``defmacro`` whose body mentions that function
    and the :pinned rows' :arms terms, so a mention-graph walk reaches what
    the expansion calls.
    """
    if not (len(form) >= 2 and isinstance(form[1], Sym)):
        return []
    pinned: list = []
    for row in form[2:]:
        if not (isinstance(row, list) and row):
            continue
        items = row[1:]
        for index in range(0, len(items) - 1, 2):
            if (isinstance(items[index], Sym) and str(items[index]) == ":arms"
                    and isinstance(items[index + 1], list) and items[index + 1]
                    and str(items[index + 1][0]) == ":pinned"):
                pinned.extend(items[index + 1][1:])
    return [
        [Sym("defmacro"), Sym("fn-nntp-command-dispatch"),
         [Sym("archive-call"), Sym("&key"), Sym("pinned")],
         [Sym("fn-proto-command-dispatch-term"), Sym("archive-call"), Sym("pinned"),
          [Sym("quote"), pinned]]]]


def defprotocol_served_expansion(form: list) -> list:
    """The constants ``(defprotocol-served NAME ROWS...)`` defines (lane
    def-command, books/protocol-served-table.lisp): the :select rows' names
    (fn-served-advance-eventp's keywords), the protocol table's :archive
    rows', every served keyword and the rows with :forms (the served
    dispatcher books/protocol-served.lisp generates from them)."""
    if not (len(form) >= 2 and isinstance(form[1], Sym)):
        return []
    name = form[1]
    return [
        [Sym("defconst"), name, [Sym("quote"), list(form[2:])]],
        [Sym("defconst"), Sym("*fn-proto-select-names*"),
         [Sym("fn-proto-names-with-view"), Sym(":select"), name]],
        [Sym("defconst"), Sym("*fn-proto-archive-names*"),
         [Sym("fn-proto-names-with-dispatch"), Sym(":archive"), Sym("*fn-proto-table*")]],
        [Sym("defconst"), Sym("*fn-proto-served-names*"),
         [Sym("fn-proto-served-names"), Sym("*fn-proto-table*")]],
        [Sym("defconst"), Sym("*fn-proto-cat-rows*"),
         [Sym("fn-proto-cat-row-names"), name]],
    ]


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


DEFTEETH_KEYS = {":claim", ":subject", ":witness", ":witness-lemma", ":witness-unguarded", ":instances", ":stobjs", ":stobj-checks", ":breaks",
                 ":mutations", ":corrupt", ":visits", ":allocation", ":must-fail",
                 ":hints"}
DEFKEYSTONE_KEYS = DEFTEETH_KEYS | {":id", ":restates", ":hyps", ":rule-classes",
                                    ":otf-flg"}
BOUND_SUFFIX = {":visits": "-visits-", ":allocation": "-allocation-"}
EXEMPTIONS = {":not-applicable", ":deferred"}
def _dk_bindingsp(x: object) -> bool:
    if not isinstance(x, list):
        return False
    names = []
    for item in x:
        if not (isinstance(item, list) and len(item) == 2 and isinstance(item[0], Sym)):
            return False
        names.append(str(item[0]))
    return len(names) == len(set(names))


def _dk_nil(x: object) -> object:
    return [] if isinstance(x, Sym) and str(x) == "nil" else x


def _dk_reasonp(x: object) -> bool:
    return isinstance(x, str) and not isinstance(x, Sym) and bool(x)


def _dk_exemptionp(x: object) -> bool:
    """``(:not-applicable "why")`` or ``(:deferred "why")``."""
    return (isinstance(x, list) and len(x) == 2 and str(x[0]) in EXEMPTIONS
            and _dk_reasonp(x[1]))


def _dk_plist(tail: list) -> dict | None:
    """A keyword-value tail as a dict, or None where it is not one."""
    if len(tail) % 2 or not all(isinstance(tail[i], Sym) and str(tail[i]).startswith(":")
                                for i in range(0, len(tail), 2)):
        return None
    return keyword_plist(tail)


def _dk_entry_opts(tail: list, keys: set[str]) -> dict | None:
    """A witness entry's options (``:logical "why"``, ``:lemma THM``,
    ``:fault "intent"``), or None."""
    opts = _dk_plist(tail)
    if opts is None or any(key not in keys for key in opts):
        return None
    if ":lemma" in opts and not (isinstance(opts[":lemma"], Sym) and str(opts[":lemma"]) != "nil"):
        return None
    for key in (":logical", ":fault"):
        if key in opts and not _dk_reasonp(opts[key]):
            return None
    return opts


def _dk_claimp(x: object) -> bool:
    """``(((L1 H1) ... (Ln Hn)) C)`` with distinct labels."""
    if head(x) in {"let", "let*"}:
        return (len(x) == 3 and isinstance(_dk_nil(x[1]), list)
                and all(isinstance(b, list) and len(b) == 2 and isinstance(b[0], Sym)
                        for b in _dk_nil(x[1])) and _dk_claimp(x[2]))
    if not (isinstance(x, list) and len(x) == 2 and isinstance(_dk_nil(x[0]), list)):
        return False
    labels = []
    for pair in _dk_nil(x[0]):
        if not (isinstance(pair, list) and len(pair) == 2 and isinstance(pair[0], Sym)
                and str(pair[0]) != "nil"):
            return False
        labels.append(str(pair[0]))
    return len(labels) == len(set(labels))


def _dk_claim_core(claim):
    return _dk_claim_core(claim[2]) if head(claim) in {"let", "let*"} else claim


def _dk_claim_scope(claim, term):
    if head(claim) not in {"let", "let*"}:
        return term
    return [claim[0], claim[1],
            [Sym("declare"), [Sym("ignorable")] + [b[0] for b in _dk_nil(claim[1])]],
            _dk_claim_scope(claim[2], term)]


def _dk_bound_entries(x: object) -> list | None:
    """``((LABEL V B :attains BINDINGS | :not-attained "why" [:rests-on (A ...)]
    [:hints H] [:lemma THM]) ...)`` as a list, or None where `fn-dk-boundsp`
    refuses."""
    x = _dk_nil(x)
    if not isinstance(x, list):
        return None
    for entry in x:
        if not (isinstance(entry, list) and len(entry) >= 3 and isinstance(entry[0], Sym)
                and str(entry[0]) != "nil"):
            return None
        opts = _dk_plist(entry[3:])
        if opts is None or any(key not in {":attains", ":not-attained", ":rests-on",
                                           ":derived-by", ":hints", ":lemma"} for key in opts):
            return None
        if ":derived-by" in opts and not isinstance(opts[":derived-by"], Sym):
            return None
        if (":attains" in opts) == (":not-attained" in opts):
            return None
        if ":attains" in opts and not _dk_bindingsp(opts[":attains"]):
            return None
        if ":not-attained" in opts and not _dk_reasonp(opts[":not-attained"]):
            return None
        if not isinstance(_dk_nil(opts.get(":rests-on", [])), list):
            return None
    if len({str(e[0]) for e in x}) != len(x):
        return None
    return x


def _dk_constantp(x: object) -> bool:
    if isinstance(x, Sym):
        return str(x) in ("nil", "t")
    return head(x) == "quote" and len(x) == 2 and isinstance(x[1], Sym) \
        and str(x[1]) in ("nil", "t")


def _dk_assumption_breakp(entry: list) -> bool:
    return (len(entry) == 2 and isinstance(entry[1], list) and len(entry[1]) == 2
            and str(entry[1][0]) == ":assumption" and isinstance(entry[1][1], Sym)
            and str(entry[1][1]) != "nil")


def _dk_removal_kind(entry: list) -> Sym:
    return (Sym(":assumption") if _dk_assumption_breakp(entry)
            else _dk_witness_kind(keyword_plist(entry[2:])))


def _dk_spec_parts(name: Sym, options: dict) -> dict | None:
    """The parsed parts of a defteeth SPEC (or the SPEC a defkeystone form
    stands for), or None where `fn-dk-spec-refusal` refuses: the same checks,
    in the same order.  World-free: the claim is read, never the world."""
    claim = options.get(":claim")
    if claim is None or not _dk_claimp(claim):
        return None
    core = _dk_claim_core(claim)
    labels = [pair[0] for pair in _dk_nil(core[0])]
    hyps = [_dk_claim_scope(claim, pair[1]) for pair in _dk_nil(core[0])]
    concl = _dk_claim_scope(claim, core[1])
    if ":stobjs" in options and not (
            _dk_bindingsp(_dk_nil(options[":stobjs"]))
            and ":instances" not in options and ":witness-lemma" not in options):
        return None
    if ":stobj-checks" in options:
        checks = _dk_nil(options[":stobj-checks"])
        if not (options.get(":stobjs") and isinstance(checks, list)
                and all(isinstance(c, list) and len(c) in (2, 4)
                        and isinstance(c[0], list) and c[0]
                        and isinstance(c[1], list) and c[1]
                        and (len(c) == 2 or str(c[2]) == ":hints") for c in checks)):
            return None
    if ":witness-unguarded" in options and not (
            _dk_reasonp(options[":witness-unguarded"]) and options.get(":stobjs")):
        return None
    witness = options.get(":witness")
    if not (witness and _dk_bindingsp(witness)):
        return None
    if ":instances" in options:
        instances = options[":instances"]
        if not (isinstance(instances, list) and len(instances) == 2
                and all(isinstance(fn, Sym) for fn in instances)
                and ":witness-lemma" not in options):
            return None
    if ":witness-lemma" in options and not (isinstance(options[":witness-lemma"], Sym)
                                           and str(options[":witness-lemma"]) != "nil"):
        return None
    subject = options.get(":subject")
    if ":subject" in options and not (isinstance(subject, Sym) and str(subject) != "nil"):
        return None
    breaks = _dk_nil(options.get(":breaks", []))
    if not isinstance(breaks, list):
        return None
    by_label: dict[str, list] = {}
    for entry in breaks:
        if not (isinstance(entry, list) and len(entry) >= 2 and isinstance(entry[0], Sym)
                and str(entry[0]) != "nil"
                and (_dk_assumption_breakp(entry)
                     or (_dk_bindingsp(entry[1])
                         and _dk_entry_opts(entry[2:], {":logical", ":lemma"}) is not None))):
            return None
        if str(entry[0]) in by_label:
            return None
        by_label[str(entry[0])] = entry
    if any(label not in {str(x) for x in labels} for label in by_label):
        return None
    if any(str(label) not in by_label for label in labels):
        return None
    if ":mutations" not in options:
        return None
    mutations = options[":mutations"]
    exemption = str(mutations[0]) if _dk_exemptionp(mutations) else None
    mutations = [] if exemption else _dk_nil(mutations)
    if not isinstance(mutations, list):
        return None
    for m in mutations:
        if not (isinstance(m, list) and len(m) >= 3 and isinstance(m[0], Sym)
                and str(m[0]) != "nil" and isinstance(m[1], list) and _dk_bindingsp(m[2])
                and _dk_entry_opts(m[3:], {":fault", ":logical", ":lemma"}) is not None
                and ":fault" in keyword_plist(m[3:])):
            return None
        edit = m[1]
        if head(edit) == ":conclusion" and len(edit) == 2:
            if _dk_constantp(edit[1]) or edit[1] == core[1]:
                return None
        elif head(edit) == ":hypothesis" and len(edit) == 3 and isinstance(edit[1], Sym):
            if str(edit[1]) not in {str(x) for x in labels}:
                return None
            if (isinstance(edit[2], Sym) and str(edit[2]) == "t") \
                    or _dk_claim_scope(claim, edit[2]) == hyps[[str(x) for x in labels].index(str(edit[1]))]:
                return None
        else:
            return None
    if len({str(m[0]) for m in mutations}) != len(mutations):
        return None
    corrupt = _dk_nil(options.get(":corrupt", []))
    if not (isinstance(corrupt, list) and all(
            isinstance(c, list) and len(c) == 2 and isinstance(c[0], Sym)
            and _dk_bindingsp(c[1]) for c in corrupt)):
        return None
    visits = _dk_bound_entries(options.get(":visits", []))
    allocation = _dk_bound_entries(options.get(":allocation", []))
    if visits is None or allocation is None:
        return None
    if (visits or allocation) and ":subject" not in options:
        return None
    must_fail = options.get(":must-fail", Sym("nil"))
    if not (isinstance(must_fail, Sym) and str(must_fail) in ("t", "nil")):
        return None
    return {"name": name, "claim": claim, "hyps": hyps, "concl": concl, "labels": labels,
            "witness": witness, "breaks": by_label, "mutations": mutations,
            "exemption": exemption, "corrupt": corrupt, "visits": visits,
            "allocation": allocation, "subject": subject,
            "must_fail": str(must_fail) == "t", "options": options}


def defteeth_parts(form: list) -> dict | None:
    """The parsed parts of a well-formed ``(defteeth NAME . SPEC)``, or None
    where the Lisp macro would refuse on the SPEC alone (`fn-teeth-refusal`).
    Whether NAME is a theorem whose formula is the translated claim is the
    world's to say at certification."""
    if not (len(form) >= 2 and isinstance(form[1], Sym) and str(form[1]) != "nil"):
        return None
    options = _dk_plist(list(form[2:]))
    if options is None or any(key not in DEFTEETH_KEYS for key in options):
        return None
    return _dk_spec_parts(form[1], options)


def defkeystone_claim(name: Sym, term: object, options: dict) -> list | None:
    """The claim a defkeystone form states, from TERM's source
    ``implies``/``and`` and its ``:hyps`` labels (`fn-dk-claim-of`); None
    where the labels do not number the hypotheses."""
    implies = (isinstance(term, list) and len(term) == 3 and head(term) == "implies")
    if implies:
        hyps = term[1][1:] if head(term[1]) == "and" else [term[1]]
        concl = term[2]
    else:
        hyps, concl = [], term
    if ":hyps" in options:
        labels = _dk_nil(options[":hyps"])
        if not (isinstance(labels, list) and all(isinstance(x, Sym) for x in labels)
                and len({str(x) for x in labels}) == len(labels) == len(hyps)):
            return None
    else:
        labels = [Sym(f"h{i}") for i in range(1, len(hyps) + 1)]
    return [[[label, hyp] for label, hyp in zip(labels, hyps)], concl]


def defkeystone_spec(form: list) -> dict | None:
    """The defteeth SPEC a well-formed defkeystone form stands for
    (`fn-dk-spec-of`), as a keyword dict, or None."""
    if not (len(form) >= 3 and isinstance(form[1], Sym) and str(form[1]) != "nil"):
        return None
    options = _dk_plist(list(form[3:]))
    if options is None or any(key not in DEFKEYSTONE_KEYS for key in options):
        return None
    if ":claim" in options:
        return None
    subject = options.get(":subject")
    if not (isinstance(subject, Sym) and str(subject) != "nil"):
        return None
    claim = defkeystone_claim(form[1], form[2], options)
    if claim is None:
        return None
    spec = {":claim": claim}
    spec.update({key: value for key, value in options.items()
                 if key not in (":id", ":restates", ":hyps", ":rule-classes", ":otf-flg")})
    return spec


def defkeystone_parts(form: list) -> dict | None:
    """The parsed parts of a well-formed defkeystone form, or None.

    The checks are `fn-dk-refusal`'s; None where the Lisp macro would refuse."""
    spec = defkeystone_spec(form)
    if spec is None:
        return None
    parts = _dk_spec_parts(form[1], spec)
    if parts is None:
        return None
    options = keyword_plist(list(form[3:]))
    parts.update({"term": form[2], "id": options.get(":id"),
                  "restates": options.get(":restates"), "form_options": options})
    return parts


def _dk_override(base: list, over: list) -> list:
    over = list(over)
    out = []
    for binding in base:
        match = next((b for b in over if str(b[0]) == str(binding[0])), None)
        if match is not None:
            out.append(match)
            over.remove(match)
        else:
            out.append(binding)
    return out + over


def _dk_at(bindings: list, term: object) -> list:
    return [Sym("let*"), bindings,
            [Sym("declare"), [Sym("ignorable")] + [b[0] for b in bindings]], term]


def _dk_logical(term: object) -> list:
    return [Sym("with-guard-checking"), Sym(":none"), term]


def _dk_implies(hyps: list, concl: object) -> object:
    if not hyps:
        return concl
    if len(hyps) == 1:
        return [Sym("implies"), hyps[0], concl]
    return [Sym("implies"), [Sym("and")] + list(hyps), concl]


def _dk_conj(terms: list) -> object:
    return terms[0] if len(terms) == 1 else [Sym("and")] + list(terms)


def _dk_quote(x: object) -> list:
    return [Sym("quote"), x]


def defkeystone_names(parts: dict) -> dict[str, list[str]]:
    """The theorem names a well-formed form admits and asks to fail: the
    keystone (defkeystone only), its visit and allocation bounds (admitted),
    and, under ``:must-fail t``, the weakened and mutant statements."""
    name = str(parts["name"])
    musts = parts["must_fail"]
    return {"keystone": [name],
            "bounds": [f"{name}{BOUND_SUFFIX[kind]}{entry[0]}"
                       for kind in (":visits", ":allocation") for entry in parts[kind[1:]]],
            "without": [f"{name}-without-{label}" for label in parts["labels"]
                        if not _dk_assumption_breakp(parts["breaks"][str(label)])] if musts else [],
            "mutant": [f"{name}-mutant-{m[0]}" for m in parts["mutations"]] if musts else []}


def defteeth_names(parts: dict) -> dict[str, list[str]]:
    """As ``defkeystone_names`` for a defteeth form (which admits no keystone)."""
    names = defkeystone_names(parts)
    names["keystone"] = []
    return names


def _dk_bound_rows(entries: list) -> list:
    """``(L V B :attains|:not-attained :rests-on (A ...))`` per entry, as
    `fn-dk-bound-rows` writes them."""
    rows = []
    for entry in entries:
        opts = keyword_plist(entry[3:])
        rows.append([entry[0], entry[1], entry[2],
                     Sym(":attains") if ":attains" in opts else Sym(":not-attained"),
                     Sym(":rests-on"), _dk_nil(opts.get(":rests-on", Sym("nil"))) or Sym("nil"),
                     Sym(":derived-by"), opts.get(":derived-by", Sym("nil"))])
    return rows


def _dk_witness_kind(opts: dict) -> Sym:
    if ":lemma" in opts:
        return Sym(":lemma")
    if ":logical" in opts:
        return Sym(":logical")
    return Sym(":reachable")


def teeth_row(parts: dict, by: str, formula: object = None) -> list:
    """``(table fn-teeth 'NAME ROW)`` as `fn-dk-row` writes it; FORMULA is
    the world's theorem, nil in this static reading."""
    removals = [[label, _dk_removal_kind(parts["breaks"][str(label)])]
                for label in parts["labels"]]
    mutations: object = (Sym(parts["exemption"]) if parts["exemption"]
                         else [[m[0], m[1][0], keyword_plist(m[3:])[":fault"]]
                               for m in parts["mutations"]] or Sym("nil"))
    row = [Sym(":by"), Sym(by), Sym(":claim"), parts["claim"],
           Sym(":formula"), Sym("nil") if formula is None else formula,
           Sym(":subject"), parts["subject"] if parts["subject"] is not None else Sym("nil"),
           Sym(":witness"), (Sym(":instance") if ":instances" in parts["options"]
                             else Sym(":lemma") if ":witness-lemma" in parts["options"]
                             else Sym(":unguarded") if ":witness-unguarded" in parts["options"]
                             else Sym(":executable")),
           Sym(":hyps"), list(parts["labels"]) or Sym("nil"),
           Sym(":removals"), removals or Sym("nil"),
           Sym(":mutations"), mutations,
           Sym(":corrupt"), [c[0] for c in parts["corrupt"]] or Sym("nil"),
           Sym(":visits"), _dk_bound_rows(parts["visits"]) or Sym("nil"),
           Sym(":allocation"), _dk_bound_rows(parts["allocation"]) or Sym("nil")]
    return [Sym("table"), Sym("fn-teeth"), _dk_quote(parts["name"]), _dk_quote(row)]


def _dk_witness_event(name: Sym, msg: str, bindings: list, terms: list, opts: dict) -> list:
    """`fn-dk-witness-event`: the assert-event, logical under :logical, or the
    lemma check under :lemma."""
    upper = str(name).upper()
    claim = _dk_conj([_dk_at(bindings, term) for term in terms])
    if ":lemma" in opts:
        return [Sym("fn-dk-lemma-check"), name, opts[":lemma"], bindings, _dk_conj(terms), msg]
    if ":unguarded" in opts:
        return [Sym("assert-event"), [Sym("fn-dk-unguarded"), claim],
                Sym(":msg"), f"{upper}: {msg} (unguarded: {opts[':unguarded']})"]
    if ":logical" in opts:
        return [Sym("assert-event"), _dk_logical(claim),
                Sym(":msg"), f"{upper}: {msg} (logical: {opts[':logical']})"]
    return [Sym("assert-event"), claim, Sym(":msg"), f"{upper}: {msg}"]


def teeth_events(parts: dict, by: str, formula: object = None) -> list:
    """The teeth of a keystone, as `fn-dk-teeth-events` emits them: the
    positive witness, removals, mutants, corrupted states, the bounds, the row."""
    name = parts["name"]
    options, witness = parts["options"], parts["witness"]
    hyps, concl, labels = parts["hyps"], parts["concl"], parts["labels"]
    hint_args = [Sym(":hints"), options[":hints"]] if ":hints" in options else []
    musts = parts["must_fail"]
    events: list = [_dk_witness_event(
        name, "witness", witness, hyps + [concl],
        {":lemma": options[":witness-lemma"]} if ":witness-lemma" in options
        else {":unguarded": options[":witness-unguarded"]} if ":witness-unguarded" in options
        else {})]
    for index, label in enumerate(labels):
        entry = parts["breaks"][str(label)]
        if _dk_assumption_breakp(entry):
            continue
        bindings = _dk_override(witness, entry[1])
        retained = hyps[:index] + hyps[index + 1:]
        events.append(_dk_witness_event(
            name, f"without {str(label).upper()}", bindings,
            retained + [[Sym("not"), hyps[index]], [Sym("not"), concl]],
            keyword_plist(entry[2:])))
        if musts:
            events.append([Sym("local"), [Sym("must-fail-checked"),
                                          [Sym("defthm"), Sym(f"{name}-without-{label}"),
                                           _dk_implies(retained, concl)] + hint_args]])
    for m in parts["mutations"]:
        bindings = _dk_override(witness, m[2])
        edit = list(m[1])
        edit[-1] = _dk_claim_scope(parts["claim"], edit[-1])
        if head(edit) == ":conclusion":
            terms = hyps + [concl, [Sym("not"), edit[1]]]
            mutant = _dk_implies(hyps, edit[1])
        else:
            at = [str(x) for x in labels].index(str(edit[1]))
            terms = (hyps[:at] + hyps[at + 1:]
                     + [edit[2], [Sym("not"), hyps[at]], [Sym("not"), concl]])
            mutant = _dk_implies(hyps[:at] + [edit[2]] + hyps[at + 1:], concl)
        events.append(_dk_witness_event(name, f"mutant {str(m[0]).upper()}", bindings,
                                        terms, keyword_plist(m[3:])))
        if musts:
            events.append([Sym("local"), [Sym("must-fail-checked"),
                                          [Sym("defthm"), Sym(f"{name}-mutant-{m[0]}"),
                                           mutant] + hint_args]])
    for corrupt in parts["corrupt"]:
        bindings = _dk_override(witness, corrupt[1])
        events.append([Sym("assert-event"),
                       _dk_logical(_dk_at(bindings, [Sym("and"),
                                                     [Sym("not"), _dk_conj(hyps)],
                                                     [Sym("not"), concl]])),
                       Sym(":msg"), f"{str(name).upper()}: corrupt {str(corrupt[0]).upper()}"])
    for kind in (":visits", ":allocation"):
        for entry in parts[kind[1:]]:
            label, v, bound = entry[0], entry[1], entry[2]
            opts = keyword_plist(entry[3:])
            entry_hints = [Sym(":hints"), opts[":hints"]] if ":hints" in opts else []
            claim = [Sym("<="), v, bound]
            events.append([Sym("defthm"), Sym(f"{name}{BOUND_SUFFIX[kind]}{label}"),
                           _dk_implies(hyps, claim)] + entry_hints)
            events.append(_dk_witness_event(
                name, f"{kind[1:]} {str(label).upper()}", witness, hyps + [claim],
                {":lemma": opts[":lemma"]} if ":lemma" in opts else {}))
            if ":attains" in opts:
                events.append(_dk_witness_event(
                    name, f"attains {str(label).upper()}",
                    _dk_override(witness, opts[":attains"]),
                    hyps + [[Sym("equal"), v, bound]], {}))
    events.append(teeth_row(parts, by, formula))
    return events


def defteeth_expansion(form: list) -> list:
    """The events ``(defteeth NAME ...)`` generates, as the ledger sees them:
    one ``progn`` of the teeth (``:formula nil`` in the row, which the world
    fills at certification), or nothing for a form the Lisp macro refuses on
    its spec."""
    parts = defteeth_parts(form)
    if parts is None:
        return []
    return [[Sym("progn")] + teeth_events(parts, "defteeth")]


def defkeystone_expansion(form: list) -> list:
    """The events ``(defkeystone ...)`` generates, as the ledger sees them:
    the defthm, the restates check and the teeth (which the Lisp macro binds
    to the world in a make-event: ``fn-dk-expand`` emits the make-event, and
    its expansion is ``teeth_events`` of the spec), in one ``progn``; nothing
    for a form the Lisp macro refuses."""
    parts = defkeystone_parts(form)
    if parts is None:
        return []
    name, options = parts["name"], parts["form_options"]
    upper = str(name).upper()
    hint_args = [Sym(":hints"), options[":hints"]] if ":hints" in options else []
    thm = [Sym("defthm"), name, parts["term"]] + hint_args
    for key in (":rule-classes", ":otf-flg"):
        if key in options:
            thm += [Sym(key), options[key]]
    events: list = [thm]
    if parts["restates"] is not None:
        world = [Sym("w"), Sym("state")]
        events.append([Sym("assert-event"),
                       [Sym("equal"),
                        [Sym("getpropc"), _dk_quote(name), _dk_quote(Sym("theorem")),
                         Sym("nil"), world],
                        [Sym("getpropc"), _dk_quote(parts["restates"]),
                         _dk_quote(Sym("theorem")), Sym("nil"), world]],
                       Sym(":msg"), f"{upper}: restates"])
    events += teeth_events(parts, "defkeystone")
    return [[Sym("progn")] + events]


def _gen_sym(*parts: object) -> Sym:
    return Sym("".join(str(part) for part in parts))


def _gen_lambda(form: object, arity: int) -> list | None:
    if not (isinstance(form, list) and len(form) == 3 and head(form) == "lambda"
            and isinstance(form[1], list) and len(form[1]) == arity
            and all(isinstance(v, Sym) for v in form[1])):
        return None
    return form


def _gen_sub(lam: list, actuals: list) -> object:
    alist = {str(v): a for v, a in zip(lam[1], actuals)}

    def walk(term: object) -> object:
        if isinstance(term, Sym):
            return alist.get(str(term), term)
        if isinstance(term, list):
            if head(term) == "quote":
                return term
            return [walk(item) for item in term]
        return term
    return walk(lam[2])


def _gen_nth(k: int, x: object) -> object:
    term = x
    for _ in range(k):
        term = [Sym("fn-cv-cdr"), term]
    return [Sym("fn-cv-car"), term]


def _gen_component(k: int, n: int, x: object) -> object:
    return x if n == 1 else _gen_nth(k, x)


def _gen_defun(name: Sym, formals: list, body: object, guard: object = Sym("t"),
               stobjs: object = None) -> list:
    xargs = [Sym("xargs"), Sym(":guard"), guard]
    if stobjs is not None:
        xargs += [Sym(":stobjs"), stobjs]
    return [Sym("defun"), name, formals, [Sym("declare"), xargs], body]


def def_carried_view_parts(form: list) -> dict | None:
    """The parsed declaration, or None where `fn-cv-refusal` refuses."""
    if not (len(form) >= 2 and isinstance(form[1], Sym) and str(form[1]) != "nil"):
        return None
    options = _dk_plist(list(form[2:]))
    if options is None or any(key not in {":key", ":indexes", ":build", ":stamp"} for key in options):
        return None
    stamp = None
    if ":stamp" in options:
        stamp_opts = _dk_plist(list(options[":stamp"])) if isinstance(options[":stamp"], list) else None
        if (stamp_opts is None or set(stamp_opts) != {":stamped", ":determines"}
                or _gen_lambda(stamp_opts[":stamped"], 2) is None
                or not isinstance(stamp_opts[":determines"], Sym)):
            return None
        stamp = stamp_opts
    key = options.get(":key")
    indexes = options.get(":indexes")
    if not (isinstance(key, Sym) and str(key) != "nil" and isinstance(indexes, list) and indexes):
        return None
    entries = []
    kinds = set()
    for entry in indexes:
        if not (isinstance(entry, list) and entry and isinstance(entry[0], Sym)):
            return None
        opts = _dk_plist(list(entry[1:]))
        if opts is None or any(key not in {":kind", ":key-fn", ":put", ":hasp", ":empty", ":lemmas"}
                               for key in opts):
            return None
        kind = str(opts.get(":kind", ""))
        if kind not in (":set", ":exact"):
            return None
        if _gen_lambda(opts.get(":put"), 2) is None or ":empty" not in opts:
            return None
        if kind == ":set" and (_gen_lambda(opts.get(":key-fn"), 1) is None
                               or _gen_lambda(opts.get(":hasp"), 2) is None):
            return None
        if kind == ":exact" and (":key-fn" in opts or ":hasp" in opts):
            return None
        kinds.add(kind)
        entries.append({"name": entry[0], "kind": kind, "put": opts[":put"],
                        "empty": opts[":empty"], "key_fn": opts.get(":key-fn"),
                        "hasp": opts.get(":hasp")})
    if len(kinds) != 1 or len({str(e["name"]) for e in entries}) != len(entries):
        return None
    return {"name": form[1], "key": key, "indexes": entries, "set": kinds == {":set"},
            "build": options.get(":build"), "stamp": stamp}


def def_carried_view_expansion(form: list) -> list:
    parts = def_carried_view_parts(form)
    if parts is None:
        return []
    name, ws, entries = parts["name"], parts["key"], parts["indexes"]
    n = len(entries)
    setp = parts["set"]
    ws_of = _gen_sym(name, "-", ws)
    put, empty = _gen_sym(name, "-put"), _gen_sym(name, "-empty")
    build_onto, fold = _gen_sym(name, "-build-onto"), _gen_sym(name, "-fold")
    build = parts["build"] if parts["build"] is not None else _gen_sym(name, "-build")
    okp, carryp, refresh = _gen_sym(name, "-okp"), _gen_sym(name, "-carryp"), _gen_sym(name, "-refresh")
    stamp = parts["stamp"]
    lcarryp = _gen_sym(name, "-list-carryp") if stamp else carryp
    carry, idxs, e = Sym("carry"), Sym("idxs"), Sym("e")
    put_terms = [_gen_sub(entry["put"], [e, _gen_component(k, n, idxs)])
                 for k, entry in enumerate(entries)]
    empty_terms = [entry["empty"] for entry in entries]
    tuple_ = (lambda terms: terms[0] if n == 1 else [Sym("list")] + terms)
    events: list = [
        _gen_defun(ws_of, [carry], [Sym("fn-cv-cdr"), [Sym("fn-cv-car"), carry]] if stamp
                   else [Sym("fn-cv-car"), carry]),
        _gen_defun(put, [e, idxs], tuple_(put_terms)),
        _gen_defun(empty, [], tuple_(empty_terms)),
        _gen_defun(build_onto, [Sym("ys"), idxs],
                   [Sym("if"), [Sym("consp"), Sym("ys")],
                    [put, [Sym("car"), Sym("ys")], [build_onto, [Sym("cdr"), Sym("ys")], idxs]], idxs]),
        _gen_defun(fold, [Sym("racc"), idxs],
                   [Sym("if"), [Sym("consp"), Sym("racc")],
                    [fold, [Sym("cdr"), Sym("racc")], [put, [Sym("car"), Sym("racc")], idxs]], idxs]),
        _gen_defun(build, [ws], [fold, [Sym("fn-cv-rev"), ws, Sym("nil")], [empty]]),
        [Sym("defthm"), _gen_sym(build, "-is-build-onto"),
         [Sym("equal"), [build, ws], [build_onto, ws, [empty]]]],
    ]
    conjuncts = []
    for k, entry in enumerate(entries):
        idx = entry["name"]
        of = _gen_sym(name, "-", idx, "-of")
        events.append(_gen_defun(of, [idxs], _gen_component(k, n, idxs)))
        events.append(_gen_defun(_gen_sym(name, "-", idx), [carry], [of, [Sym("fn-cv-cdr"), carry]]))
        if setp:
            index_okp = _gen_sym(name, "-", idx, "-okp")
            key_car = _gen_sub(entry["key_fn"], [[Sym("car"), ws]])
            events.append(_gen_defun(
                index_okp, [ws, idxs],
                [Sym("if"), [Sym("consp"), ws],
                 [Sym("and"), [Sym("or"), [Sym("not"), key_car],
                               _gen_sub(entry["hasp"], [key_car, [of, idxs]])],
                  [index_okp, [Sym("cdr"), ws], idxs]],
                 Sym("t")]))
            key_e2 = _gen_sub(entry["key_fn"], [Sym("e2")])
            key_e = _gen_sub(entry["key_fn"], [e])
            events.append([Sym("defthm"), _gen_sym(name, "-", idx, "-hasp-of-put"),
                           [Sym("implies"),
                            [Sym("and"), key_e2, _gen_sub(entry["hasp"], [key_e2, [of, idxs]])],
                            _gen_sub(entry["hasp"], [key_e2, [of, [put, e, idxs]]])]])
            events.append([Sym("defthm"), _gen_sym(name, "-", idx, "-put-has-key"),
                           [Sym("implies"), key_e,
                            _gen_sub(entry["hasp"], [key_e, [of, [put, e, idxs]]])]])
            events.append([Sym("defthm"), _gen_sym(name, "-", idx, "-okp-of-build"),
                           [index_okp, ws, [build_onto, ws, [empty]]]])
            events.append([Sym("defthm"), _gen_sym(name, "-", idx, "-okp-of-extend"),
                           [Sym("implies"), [index_okp, Sym("old"), idxs],
                            [index_okp, [Sym("append"), Sym("new"), Sym("old")],
                             [build_onto, Sym("new"), idxs]]]])
            conjuncts.append([index_okp, ws, idxs])
    if setp:
        events.append(_gen_defun(okp, [ws, idxs], [Sym("and")] + conjuncts))
    else:
        events.append(_gen_defun(okp, [ws, idxs], [Sym("equal"), idxs, [build_onto, ws, [empty]]]))
    events.append(_gen_defun(lcarryp, [carry], [okp, [Sym("fn-cv-car"), carry], [Sym("fn-cv-cdr"), carry]]))
    if stamp:
        events.append(_gen_defun(carryp, [carry],
                                 [lcarryp, [Sym("cons"), [ws_of, carry], [Sym("fn-cv-cdr"), carry]]]))
    events.append([Sym("defthm"), _gen_sym(name, "-okp-of-build"), [okp, ws, [build_onto, ws, [empty]]]])
    events.append([Sym("defthm"), _gen_sym(name, "-okp-of-extend"),
                   [Sym("implies"), [okp, Sym("old"), idxs],
                    [okp, [Sym("append"), Sym("new"), Sym("old")], [build_onto, Sym("new"), idxs]]]])
    events.append(_gen_defun(
        refresh, [carry, ws],
        [Sym("if"), [Sym("equal"), ws, [Sym("fn-cv-car"), carry]],
         [Sym("cons"), ws, [Sym("fn-cv-cdr"), carry]],
         [Sym("mv-let"), [Sym("found"), Sym("racc")],
          [Sym("fn-cv-walk"), ws, [Sym("fn-cv-car"), carry], Sym("nil")],
          [Sym("if"), Sym("found"),
           [Sym("cons"), ws, [fold, Sym("racc"), [Sym("fn-cv-cdr"), carry]]],
           [Sym("cons"), ws, [fold, [Sym("fn-cv-rev"), ws, Sym("nil")], [empty]]]]]]))
    events.append([Sym("defthm"), _gen_sym(lcarryp, "-of-refresh"),
                   [Sym("implies"), [lcarryp, carry], [lcarryp, [refresh, carry, ws]]]])
    if not stamp:
        events.append([Sym("defthm"), _gen_sym(ws_of, "-of-refresh"),
                       [Sym("equal"), [ws_of, [refresh, carry, ws]], ws]])
    events.append([Sym("defthm"), _gen_sym(refresh, "-walks-the-delta"),
                   [Sym("equal"),
                    [Sym("fn-cv-walk-steps"), [Sym("append"), Sym("new"), [ws_of, carry]], [ws_of, carry]],
                    [Sym("len"), Sym("new")]]])
    if setp or (n == 1 and isinstance(empty_terms[0], Sym) and str(empty_terms[0]) == "nil"):
        events.append([Sym("defthm"), _gen_sym(carryp, "-of-nil"), [carryp, Sym("nil")]])
    events.append([Sym("table"), Sym("fn-teeth-owed"), _dk_quote(_gen_sym(lcarryp, "-of-refresh")),
                   _dk_quote([Sym(":by"), Sym("def-carried-view"), Sym(":claim"),
                              [[[Sym("carried"), [lcarryp, carry]]], [lcarryp, [refresh, carry, ws]]]])])
    if stamp:
        st, s_ = Sym("stamp"), Sym("ws")
        stamp_of, stampedp = _gen_sym(name, "-stamp"), _gen_sym(name, "-stampedp")
        refresh_s, fresh_fn = _gen_sym(name, "-refresh-stamped"), _gen_sym(name, "-fresh")
        fresh = [fresh_fn, st, ws]
        events.append(_gen_defun(fresh_fn, [st, ws], _gen_sub(stamp[":stamped"], [st, ws])))
        events.append(_gen_defun(stamp_of, [carry], [Sym("fn-cv-car"), [Sym("fn-cv-car"), carry]]))
        events.append(_gen_defun(stampedp, [carry], [fresh_fn, [stamp_of, carry], [ws_of, carry]]))
        events.append(_gen_defun(
            refresh_s, [carry, st, ws],
            [Sym("if"), [Sym("equal"), st, [stamp_of, carry]],
             [Sym("cons"), [Sym("cons"), st, ws], [Sym("fn-cv-cdr"), carry]],
             [Sym("let"), [[Sym("r"), [refresh, [Sym("cons"), [ws_of, carry], [Sym("fn-cv-cdr"), carry]], ws]]],
              [Sym("cons"), [Sym("cons"), st, ws], [Sym("fn-cv-cdr"), Sym("r")]]]]))
        hyps = [[carryp, carry], [stampedp, carry], fresh]
        events.append([Sym("defthm"), _gen_sym(fresh_fn, "-determines"),
                       [Sym("implies"), [Sym("and"), [fresh_fn, Sym("s"), Sym("a")], [fresh_fn, Sym("s"), Sym("b")]],
                        [Sym("equal"), Sym("a"), Sym("b")]]])
        events.append([Sym("defthm"), _gen_sym(name, "-key-of-refresh"),
                       [Sym("equal"), [Sym("fn-cv-car"), [refresh, carry, ws]], ws]])
        events.append([Sym("defthm"), _gen_sym(carryp, "-of-refresh-stamped"),
                       [Sym("implies"), [Sym("and")] + hyps, [carryp, [refresh_s, carry, st, ws]]]])
        events.append([Sym("defthm"), _gen_sym(stampedp, "-of-refresh-stamped"),
                       [Sym("implies"), fresh, [stampedp, [refresh_s, carry, st, ws]]]])
        events.append([Sym("defthm"), _gen_sym(stamp_of, "-of-refresh-stamped"),
                       [Sym("equal"), [stamp_of, [refresh_s, carry, st, ws]], st]])
        events.append([Sym("table"), Sym("fn-teeth-owed"), _dk_quote(_gen_sym(carryp, "-of-refresh-stamped")),
                       _dk_quote([Sym(":by"), Sym("def-carried-view"), Sym(":claim"),
                                  [[[Sym("carried"), hyps[0]], [Sym("stamped"), hyps[1]], [Sym("fresh"), fresh]],
                                   [carryp, [refresh_s, carry, st, ws]]]])])
    return events


def def_carried_reader_expansion(form: list) -> list:
    if not (len(form) >= 3 and isinstance(form[1], Sym) and isinstance(form[2], list)):
        return []
    r, formals = form[1], list(form[2])
    options = _dk_plist(list(form[3:]))
    wanted = {":of", ":carry", ":list", ":stamp", ":when", ":probe", ":fast", ":reference", ":by",
              ":name", ":guard", ":stobjs"}
    if options is None or any(key not in wanted for key in options):
        return []
    for key in (":of", ":carry", ":list", ":probe", ":fast", ":reference", ":by"):
        if key not in options:
            return []
    view, c, ws = options[":of"], options[":carry"], options[":list"]
    probe = options[":probe"]
    if not (isinstance(probe, list) and len(probe) == 2 and isinstance(probe[0], Sym)):
        return []
    reference = options[":reference"]
    carryp = _gen_sym(view, "-carryp")
    thm = options.get(":name") or _gen_sym(r, "-is-", head(reference) or "reference")
    # the probe's :hasp is the view's declaration, which the ledger does not
    # resolve statically: the reader body keeps the probe as the view's
    # NAME-IDX accessor applied to the key, a faithful shape for the hygiene
    # checks (the exact hasp term is the world's)
    # the view's stamp relation is the world's; the mirror states a stamped
    # reader's premises through the view's NAME-stampedp and a NAME-fresh
    # placeholder over the stamp and the list (the exact relation is read
    # at certification)
    s_ = options.get(":stamp")
    fast_test = ([Sym("equal"), s_, [_gen_sym(view, "-stamp"), c]] if s_ is not None
                 else [Sym("equal"), ws, [_gen_sym(view, "-", Sym("key")), c]])
    body = [Sym("if"),
            [Sym("and"), options.get(":when", Sym("t")), fast_test,
             [Sym("not"), [_gen_sym(view, "-", probe[0], "-probe"), probe[1], c]]],
            options[":fast"], reference]
    hyps = [[Sym("carried"), [carryp, c]]]
    if s_ is not None:
        hyps += [[Sym("stamped"), [_gen_sym(view, "-stampedp"), c]],
                 [Sym("fresh"), [_gen_sym(view, "-fresh"), s_, ws]]]
    return [_gen_defun(r, formals, body, options.get(":guard", Sym("t")), options.get(":stobjs")),
            [Sym("defthm"), thm, [Sym("implies"), [Sym("and")] + [h[1] for h in hyps],
                                  [Sym("equal"), [r] + formals, reference]]],
            [Sym("table"), Sym("fn-teeth-owed"), _dk_quote(thm),
             _dk_quote([Sym(":by"), Sym("def-carried-reader"), Sym(":claim"),
                        [hyps, [Sym("equal"), [r] + formals, reference]]])],
            [Sym("in-theory"), [Sym("disable"), r]]]


def def_keyset_check_expansion(form: list) -> list:
    if not (len(form) >= 3 and isinstance(form[1], Sym) and isinstance(form[2], list)
            and len(form[2]) == 2 and all(isinstance(v, Sym) for v in form[2])):
        return []
    name, (xs, ys) = form[1], form[2]
    options = _dk_plist(list(form[3:]))
    wanted = {":sense", ":xs-key", ":ys-key", ":each", ":base", ":logic-member", ":member-is",
              ":keys", ":policy", ":verify-guards"}
    if options is None or any(key not in wanted for key in options):
        return []
    if str(options.get(":sense")) not in (":present", ":absent"):
        return []
    present = str(options[":sense"]) == ":present"
    xkey = options.get(":xs-key", [Sym("lambda"), [Sym("x")], Sym("x")])
    ykey = options.get(":ys-key", [Sym("lambda"), [Sym("y")], Sym("y")])
    each = options.get(":each", [Sym("lambda"), [Sym("x")], Sym("t")])
    base = options.get(":base", Sym("t"))
    base_term = _gen_sub([Sym("lambda"), [Sym("xs")], base], [xs])
    policy = str(options.get(":policy", ":long"))
    keys = options.get(":keys") or _gen_sym(name, "-keys")
    filler, scan, ks, walk = (_gen_sym(name, "-fill"), _gen_sym(name, "-scan"),
                              _gen_sym(name, "-ks"), _gen_sym(name, "-walk"))
    car_xs, car_ys = [Sym("car"), xs], [Sym("car"), ys]
    if ":logic-member" in options:
        member = _gen_sub(options[":logic-member"], [car_xs, ys])
    else:
        member = [Sym("if"), [Sym("member-equal"), _gen_sub(xkey, [car_xs]), [keys, ys]], Sym("t"), Sym("nil")]
    want = (lambda b: b if present else [Sym("not"), b])
    ks_stobj = Sym("fn-keyset")
    events: list = []
    if ":keys" not in options:
        events.append(_gen_defun(keys, [ys], [Sym("if"), [Sym("consp"), ys],
                                               [Sym("cons"), _gen_sub(ykey, [car_ys]), [keys, [Sym("cdr"), ys]]],
                                               Sym("nil")]))
    logic_body = [Sym("if"), [Sym("consp"), xs],
                  [Sym("and"), _gen_sub(each, [car_xs]), want(member), [walk, [Sym("cdr"), xs], ys]],
                  base_term]
    events.append(_gen_defun(walk, [xs, ys], logic_body))
    events.append(_gen_defun(filler, [ys, ks_stobj],
                             [Sym("if"), [Sym("consp"), ys],
                              [Sym("let"), [[ks_stobj, [Sym("fn-keyset-tab-put"), _gen_sub(ykey, [car_ys]), Sym("t"), ks_stobj]]],
                               [filler, [Sym("cdr"), ys], ks_stobj]],
                              ks_stobj], stobjs=ks_stobj))
    events.append(_gen_defun(scan, [xs, ks_stobj],
                             [Sym("if"), [Sym("consp"), xs],
                              [Sym("and"), _gen_sub(each, [car_xs]),
                               want([Sym("if"), [Sym("fn-keyset-tab-boundp"), _gen_sub(xkey, [car_xs]), ks_stobj], Sym("t"), Sym("nil")]),
                               [scan, [Sym("cdr"), xs], ks_stobj]],
                              base_term], stobjs=ks_stobj))
    events.append(_gen_defun(ks, [xs, ys],
                             [Sym("with-local-stobj"), ks_stobj,
                              [Sym("mv-let"), [Sym("ok"), ks_stobj],
                               [Sym("let"), [[ks_stobj, [filler, ys, ks_stobj]]],
                                [Sym("mv"), [scan, xs, ks_stobj], ks_stobj]],
                               Sym("ok")]]))
    events.append([Sym("defthm"), _gen_sym(name, "-scan-after-fill"),
                   [Sym("implies"), [Sym("not"), [Sym("consp"), [Sym("nth"), 0, ks_stobj]]],
                    [Sym("equal"), [scan, xs, [filler, ys, ks_stobj]], [walk, xs, ys]]]])
    events.append([Sym("defthm"), _gen_sym(name, "-ks-is-logic"),
                   [Sym("equal"), [ks, xs, ys], [walk, xs, ys]]])
    exec_body = {":always": [ks, xs, ys],
                 ":nonempty": [Sym("if"), [Sym("consp"), xs], [ks, xs, ys], base_term]}.get(
        policy, [Sym("if"), [Sym("fn-ks-longp"), ys], [ks, xs, ys], [walk, xs, ys]])
    name_logic = [Sym("if"), [Sym("consp"), xs],
                  [Sym("and"), _gen_sub(each, [car_xs]), want(member), [name, [Sym("cdr"), xs], ys]],
                  base_term]
    events.append([Sym("defun"), name, [xs, ys],
                   [Sym("declare"), [Sym("xargs"), Sym(":guard"), Sym("t"), Sym(":verify-guards"), Sym("nil")]],
                   [Sym("mbe"), Sym(":logic"), name_logic, Sym(":exec"), exec_body]])
    events.append([Sym("defthm"), _gen_sym(name, "-walk-is-logic"),
                   [Sym("equal"), [walk, xs, ys], [name, xs, ys]]])
    if str(options.get(":verify-guards", Sym("t"))) != "nil":
        events.append([Sym("verify-guards"), name])
    for thm, claim in ((_gen_sym(name, "-ks-is-logic"), [Sym("equal"), [ks, xs, ys], [walk, xs, ys]]),
                       (_gen_sym(name, "-walk-is-logic"), [Sym("equal"), [walk, xs, ys], [name, xs, ys]])):
        events.append([Sym("table"), Sym("fn-teeth-owed"), _dk_quote(thm),
                       _dk_quote([Sym(":by"), Sym("def-keyset-check"), Sym(":claim"), [Sym("nil"), claim]])])
    events.append([Sym("in-theory"), [Sym("disable"), keys, walk, filler, scan, ks, _gen_sym(name, "-ks-is-logic")]])
    return events


def def_cursor_batch_expansion(form: list) -> list:
    """Mirror exported events of books/def-cursor-batch, without evaluating Lisp.

    Literal step contracts supply the actual batch function and theorem subjects.
    This source model establishes event presence, never ACL2 admission evidence.
    Local proof setup and checked prerequisite MAKE-EVENTs are not exported.
    """
    if not (len(form) >= 3 and isinstance(form[1], Sym)
            and isinstance(form[2], list)
            and all(isinstance(x, Sym) for x in form[2])):
        return []
    opts = _dk_plist(list(form[3:]))
    allowed = {":step", ":stobjs", ":byte-proof", ":call-proof", ":remaining", ":residual-proof",
               ":yield-proof"}
    if opts is None or set(opts) - allowed:
        return []
    if not all(isinstance(opts.get(k), Sym) for k in
               (":step", ":byte-proof", ":call-proof", ":residual-proof", ":yield-proof")):
        return []
    if str(opts[":yield-proof"]).lower() == "nil":
        return []
    remaining = opts.get(":remaining")
    if not isinstance(remaining, list) or not remaining:
        return []
    name, extra, step = form[1], form[2], opts[":step"]
    batch = _gen_sym(name, "-batch")
    cur, visits, byte_count = Sym("cur"), Sym("visits"), Sym("bytes")
    call = [batch, cur, visits, byte_count] + extra
    step_call = [step, cur, visits, byte_count] + extra
    recurse = [batch, Sym("next"), [Sym("1-"), visits], byte_count] + extra
    body = [Sym("mv-let"), [Sym("octets"), Sym("next"), Sym("calls"), Sym("status")], step_call,
            [Sym("if"), [Sym("and"), [Sym("not"), Sym("octets")],
                          [Sym("eq"), Sym("status"), Sym(":candidate")],
                          [Sym("equal"), Sym("calls"), 1], [Sym("posp"), visits]],
             [Sym("mv-let"), [Sym("out"), Sym("rest"), Sym("more"), Sym("state")], recurse,
              [Sym("mv"), Sym("out"), Sym("rest"), [Sym("+"), 1, Sym("more")], Sym("state")]],
             [Sym("mv"), Sym("octets"), Sym("next"), Sym("calls"), Sym("status")]]]
    guard = [Sym("and"), [Sym("natp"), visits], [Sym("natp"), byte_count]]
    definition = _gen_defun(batch, [cur, visits, byte_count] + extra, body,
                            guard, opts.get(":stobjs"))
    definition[3][1] += [Sym(":measure"), [Sym("nfix"), visits], Sym(":verify-guards"), Sym("nil")]
    def nth(index):
        return [Sym("mv-nth"), index, call]
    rest = _gen_sub([Sym("lambda"), [cur], remaining], [nth(1)])
    return [definition,
            [Sym("defthm"), _gen_sym(name, "-batch-byte-bound"),
             [Sym("<="), [Sym("len"), nth(0)], [Sym("nfix"), byte_count]],
             Sym(":rule-classes"), Sym(":linear")],
            [Sym("defthm"), _gen_sym(name, "-batch-call-bound"),
             [Sym("<="), nth(2), [Sym("nfix"), visits]], Sym(":rule-classes"), Sym(":linear")],
            [Sym("defthm"), _gen_sym(name, "-batch-residual"),
             [Sym("equal"), [Sym("append"), [Sym("car"), call], rest], remaining],
             Sym(":rule-classes"), Sym("nil")],
            [Sym("defthm"), _gen_sym(name, "-batch-call-natp"), [Sym("natp"), nth(2)],
             Sym(":rule-classes"), [Sym(":rewrite"), Sym(":type-prescription")]],
            [Sym("defthm"), _gen_sym(name, "-batch-yield-spends-the-visits"),
             [Sym("implies"), [Sym("and"), [Sym("posp"), byte_count],
                               [Sym("equal"), nth(3), Sym(":yield")]],
              [Sym("equal"), nth(2), [Sym("nfix"), visits]]]],
            [Sym("verify-guards"), batch]]


def def_loop_run_expansion(form: list) -> list:
    """Source view of def-loop/run's three guarded functions and drive theorem.

    The ACL2 macro owns admission, guard proofs and functional instantiation;
    this mirror exposes the exact executable calls to the ledger, callgraph
    and interface guard reader. Local proof scaffolding is omitted.
    """
    if not (len(form) >= 3 and isinstance(form[1], Sym) and isinstance(form[2], list)):
        return []
    name, formals = str(form[1]), form[2]
    opts = keyword_plist(form[3:])
    xs = opts.get(":over")
    if xs is None or str(xs) == "nil":
        xs = formals[0] if formals else None
    acc = opts.get(":acc")
    st = opts.get(":st")
    if str(st) == "nil":
        st = None
    reserved = {"dl-k", "dl-fuel", "dl-v", "dl-rest", "dl-a2", "dl-s"}
    if not (all(isinstance(x, Sym) for x in formals)
            and len(set(formals)) == len(formals) and not reserved.intersection(map(str, formals))
            and xs in formals and acc in formals and xs != acc
            and (st is None or (st in formals and st not in (xs, acc)))
            and opts.get(":row") is not None and str(opts[":row"]) != "nil"
            and opts.get(":quantum") is not None and str(opts[":quantum"]) != "nil"):
        return []
    spell = source_text
    success = opts.get(":success", Sym("nil"))
    end = opts.get(":end-status", success)
    guard = opts.get(":guard", Sym("t"))
    row, quantum = spell(opts[":row"]), spell(opts[":quantum"])
    args = " ".join(map(spell, formals))
    outs = " ".join(map(spell, [acc] + ([st] if st is not None else [])))
    outs2 = " ".join(map(spell, [Sym("dl-a2")] + ([st] if st is not None else [])))
    next_args = " ".join(spell([Sym("cdr"), xs] if x == xs else Sym("dl-a2") if x == acc else x)
                         for x in formals)
    resume_args = " ".join(spell(Sym("dl-rest") if x == xs else Sym("dl-a2") if x == acc else x)
                           for x in formals)
    extra = (" :stobjs " + spell(st)) if st is not None else ""
    if ":guard-hints" in opts:
        extra += " :guard-hints " + spell(opts[":guard-hints"])
    return read_forms(f"""
      (defun {name}-all ({args})
        (declare (xargs :guard {spell(guard)}{extra}))
        (if (atom {xs}) (mv {spell(end)} {outs})
          (mv-let (dl-v {outs2}) {row}
            (if (equal dl-v {spell(success)}) ({name}-all {next_args}) (mv dl-v {outs})))))
      (defun {name}-run (dl-k {args})
        (declare (xargs :guard (and (natp dl-k) {spell(guard)}){extra}))
        (cond ((atom {xs}) (let ((dl-v {spell(end)}))
                                (if (equal dl-v {spell(success)}) (mv :done nil {outs})
                                  (mv dl-v {xs} {outs}))))
              ((zp dl-k) (mv :more {xs} {outs}))
              (t (mv-let (dl-v {outs2}) {row}
                   (if (equal dl-v {spell(success)}) ({name}-run (1- dl-k) {next_args})
                     (mv dl-v {xs} {outs}))))))
      (defun {name}-drive (dl-fuel {args})
        (declare (xargs :guard (and (natp dl-fuel) {spell(guard)}){extra}))
        (if (zp dl-fuel) (mv '(:refused :fuel) {outs})
          (mv-let (dl-v dl-rest {outs2}) ({name}-run {quantum} {args})
            (cond ((equal dl-v :done) (mv {spell(success)} {outs2}))
                  ((equal dl-v :more) ({name}-drive (1- dl-fuel) {resume_args}))
                  (t (mv dl-v {outs2}))))))
      (defthm {name}-drive-is-all
        (equal ({name}-drive (+ 1 (len {xs})) {args}) ({name}-all {args}))
        :rule-classes nil)
    """)


def absstobj_obligation_events(name: Sym, exports: list, kinds: tuple) -> list:
    """The defthm events ``defabsstobj-missing-events`` names for a generated
    abstract stobj: each of KINDS (``correspondence``, ...) for the creator
    CREATE-NAME and for every export.  Names only; the formulas are ACL2's, so
    each statement is an opaque marker.  Presence, never admission evidence.
    One reader for every generator that ends in a defabsstobj."""
    creator = _gen_sym("create-", name)
    return [[Sym("defthm"), _gen_sym(export, "{" + kind + "}"),
             [Sym("fn-generated-obligation"), export, Sym(":" + kind)],
             Sym(":rule-classes"), Sym("nil")]
            for export in [creator] + list(exports) for kind in kinds]


def def_representation_index_expansion(form: list) -> list:
    """def-representation-index: the creator and the five exports of
    ``ixg-exports`` (books/def-representation-index.lisp: NAME-COUNT, NAME-AT,
    the :query-export, NAME-APPEND, NAME-CLEAR), each with its
    ``{correspondence}``.  Other obligation kinds ACL2 emits are not claimed."""
    if not (len(form) >= 3 and isinstance(form[1], Sym)):
        return []
    opts = keyword_plist(list(form[3:]))
    index = keyword_plist(opts[":index"]) if isinstance(opts.get(":index"), list) else {}
    qexport = index.get(":query-export")
    if not isinstance(qexport, Sym):
        return []
    name = form[1]
    exports = [_gen_sym(name, "-count"), _gen_sym(name, "-at"), qexport,
               _gen_sym(name, "-append"), _gen_sym(name, "-clear")]
    return absstobj_obligation_events(name, exports, ("correspondence",))


def def_generic_expansion(form: list) -> list:
    """def-generic (books/def-representation-generic.lisp): the three
    obligations the generator states for the creator and for every
    ``(:read|:update EXPORT :logic FN)`` row of ``:exports``."""
    if not (len(form) >= 3 and isinstance(form[1], Sym)):
        return []
    rows = keyword_plist(list(form[2:])).get(":exports")
    if not isinstance(rows, list):
        return []
    exports = [row[1] for row in rows
               if isinstance(row, list) and len(row) >= 2 and isinstance(row[1], Sym)]
    return absstobj_obligation_events(form[1], exports,
                                      ("correspondence", "guard-thm", "preserved"))


GENERATOR_EXPANSIONS = {
    "def-representation-index": def_representation_index_expansion,
    "def-generic": def_generic_expansion,
    "fn-defrecord": defrecord_expansion,
    "fn-defrecord-export": defrecord_export_expansion,
    "def-loop": def_loop_expansion,
    "def-loop/run": def_loop_run_expansion,
    "def-cursor/batch": def_cursor_batch_expansion,
    "defprotocol": defprotocol_expansion,
    "defprotocol-served": defprotocol_served_expansion,
    "defkeystone": defkeystone_expansion,
    "defteeth": defteeth_expansion,
    "def-carried-view": def_carried_view_expansion,
    "def-carried-reader": def_carried_reader_expansion,
    "def-keyset-check": def_keyset_check_expansion,
}
def generated_expansion(form: object) -> list | None:
    """Shared, non-evaluating generator dispatch; None means not mirrored.

    These are source models, not ACL2 admission evidence. Callers retain
    their own local/suppressed-event and definition traversal policies.
    Unknown generators are never guessed from similar names.
    """
    expand = GENERATOR_EXPANSIONS.get(head(form))
    return expand(form) if expand is not None else None


def source_text(form: object) -> str:
    """Print a non-evaluated reader form for consumers with lexical APIs."""
    if isinstance(form, Sym):
        return str(form)
    if isinstance(form, str):
        return '"' + form.replace('\\', '\\\\').replace('"', '\\"') + '"'
    if isinstance(form, list):
        return "(" + " ".join(source_text(item) for item in form) + ")"
    return str(form)


def source_events(forms, *, include_local: bool = True):
    """Yield source events with generator forms expanded and origin retained.

    Only event containers are traversed; quoted templates, function bodies,
    make-event and must-fail forms are not admitted events. The origin may
    be a source line or a top-level event number supplied by the caller.
    """
    for form, origin in forms:
        name = head(form)
        if name in SUPPRESSING or name in ("quote", "quasiquote", "make-event"):
            continue
        if name == "local" and not include_local:
            continue
        expansion = generated_expansion(form)
        if expansion is not None:
            yield from source_events(((item, origin) for item in expansion),
                                     include_local=include_local)
        elif name in TRANSPARENT or name in ("encapsulate", "mutual-recursion"):
            start = 2 if name == "encapsulate" else 1
            yield from source_events(((item, origin) for item in form[start:]),
                                     include_local=include_local)
        else:
            yield form, origin


def include_is_external(form: list) -> bool:
    """ACL2's :dir nil (also ()) selects an ordinary local include."""
    directory = keyword_plist(form[2:]).get(":dir")
    return (directory is not None and directory != []
            and not (isinstance(directory, Sym) and directory == "nil"))


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
                if not local:
                    book.constrained |= encapsulated_names(form[1])
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
    if name == "defkeystone":
        parts = defkeystone_parts(form)
        if parts is not None and not suppressed:
            # Each generated must-fail stands beside an evaluated ground
            # counterexample to the same weakened statement, so it is not a
            # bare general claim (`teeth_form`).
            names = defkeystone_names(parts)
            book.paired_must_fails |= set(names["without"] + names["mutant"])
            # the teeth cover the REGISTRY keystone: the restated theorem when
            # the form restates one (the formulas are checked equal), else NAME
            registry = parts["restates"] if parts["restates"] is not None else parts["name"]
            book.teeth_declared[str(registry)] = parts
    if name == "defteeth":
        parts = defteeth_parts(form)
        if parts is not None and not suppressed:
            names = defteeth_names(parts)
            book.paired_must_fails |= set(names["without"] + names["mutant"])
            book.teeth_declared[str(parts["name"])] = parts
    if name == "table" and len(form) >= 4 and head(form[2]) == "quote" \
            and isinstance(form[2][1], Sym) and head(form[3]) == "quote" and not suppressed:
        if str(form[1]) == "fn-teeth-owed" and isinstance(form[3][1], list):
            book.teeth_owed[str(form[2][1])] = form[3][1]
        return
    expansion = generated_expansion(form)
    if expansion is not None:
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
        if include_is_external(form):
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
            # The body, for the teeth-form lint: a must-fail over a macro
            # names what the macro's expansion names (PKT-364).
            book.macro_bodies[str(form[1])] = form[3:]
            book.macros.add(str(form[1]))
        return
    if name in ("defun-sk", "defstobj", "defabsstobj", "defabbrev") and len(form) >= 2 \
            and isinstance(form[1], Sym):
        book.definitions.add(str(form[1]))
        return


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
                 hosts: "dict[str, HostFile] | None" = None, *, eager: bool = True,
                 suspect_cache: "Path | None" = None) -> None:
        self.books = books
        self.roots = roots
        # ACL2 `ld` wrappers and explicit raw `load` adapters: see host_names.
        self.hosts: dict[str, HostFile] = {} if hosts is None else hosts
        self.functions: dict[str, Function] = {}
        self.theorems: dict[str, Theorem] = {}
        # Constrained function name -> the book whose `encapsulate' introduces it.
        self.constrained: dict[str, str] = {}
        for book in books.values():
            for name in book.constrained:
                self.constrained.setdefault(name, book.path)
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
        # Every theorem's suspect reasons: most of the analysis (~75 s of
        # ~82 s on persvati, 2026-09-28).  A per-book caller (`--book')
        # builds the tree with eager=False and asks `suspects_of' for its
        # own theorems only; `suspects' computes the whole map on first use.
        self._suspects: "dict[str, list[str]] | None" = None
        # C8: the suspect reasons persist per theorem under a key naming
        # everything the detectors read (suspect_keys), so a one-book edit
        # re-judges that book's theorems and those whose definitions moved.
        self._suspect_cache = suspect_cache
        if eager:
            self._suspects = self._all_suspects()

    def _all_suspects(self) -> dict[str, list[str]]:
        if self._suspect_cache is None:
            return {name: reasons for name, reasons in
                    ((theorem.name, self.suspect_reasons(theorem))
                     for theorem in self.theorems.values()) if reasons}
        keys = self.suspect_keys()
        cached = _suspect_cache_read(self._suspect_cache)
        fresh: dict[str, list[str]] = {}
        found: dict[str, list[str]] = {}
        for name, theorem in self.theorems.items():
            key = keys[name]
            reasons = cached.get(key)
            if reasons is None:
                reasons = self.suspect_reasons(theorem)
            fresh[key] = reasons
            if reasons:
                found[name] = reasons
        self.suspect_recomputed = sum(1 for key in fresh if key not in cached)
        if fresh != cached:
            _suspect_cache_write(self._suspect_cache, fresh)
        return found

    def suspect_keys(self) -> dict[str, str]:
        """Each theorem's key: its own forms, the statement of every theorem
        it names, and the definitional closure of every function it names
        (both sides of each definition, through every symbol of its body),
        plus, for a `*-preserves-*` name, the functions its subject prefix
        names.  That is everything `suspect_reasons' reads: the lemma
        lookups of detectors 1-2, the unfolding of 3-6 (to any depth), the
        name set of 7."""
        own = {name: _form_digest((f.formals, f.body)) for name, f in self.functions.items()}
        edges = {name: sorted(symbols_of(f.body) & own.keys() - {name})
                 for name, f in self.functions.items()}
        closure = _closure_digests(own, edges)
        statements = {name: _form_digest(t.statement) for name, t in self.theorems.items()}
        by_prefix: "dict[str, list[str]]" = {}
        keys = {}
        for name, theorem in self.theorems.items():
            h = hashlib.blake2b(digest_size=20)
            h.update(_form_digest((theorem.name, theorem.statement, theorem.hints)).encode())
            for symbol in sorted(symbols_of([theorem.statement, theorem.hints])):
                if symbol in closure:
                    h.update(b"f" + symbol.encode() + b"=" + closure[symbol].encode())
                if symbol in statements:
                    h.update(b"t" + symbol.encode() + b"=" + statements[symbol].encode())
            if "-preserves-" in name:
                subject = name.split("-preserves-")[0]
                if subject not in by_prefix:
                    by_prefix[subject] = sorted(
                        f for f in self.functions if f == subject or f.startswith(subject + "-"))
                h.update(b"p" + "\0".join(by_prefix[subject]).encode())
            keys[name] = h.hexdigest()
        return keys

    @property
    def suspects(self) -> dict[str, list[str]]:
        if self._suspects is None:
            self._suspects = self._all_suspects()
        return self._suspects

    def suspects_of(self, theorems: "list[Theorem]") -> dict[str, list[str]]:
        """The suspect reasons of THEOREMS alone (the whole map when known)."""
        if self._suspects is not None:
            return {t.name: self._suspects[t.name] for t in theorems if t.name in self._suspects}
        found = {}
        for theorem in theorems:
            # A name defined twice is judged by its first definition, as the
            # whole-tree map judges it.
            reasons = self.suspect_reasons(self.theorems.get(theorem.name, theorem))
            if reasons:
                found[theorem.name] = reasons
        return found

    # -- unfolding -------------------------------------------------------

    def unfold(self, form: object, depth: int = 3) -> object:
        """Bounded local unfolding, retaining shared argument subgraphs."""
        # Keep each input graph alive alongside its answer. beta_apply below
        # creates temporary graphs: caching only their ids lets Python reuse
        # a dead graph's identity for a different function expansion.
        memo: dict[tuple[int, int], tuple[object, object]] = {}
        allocated = 0

        def walk(term, remaining):
            nonlocal allocated
            if remaining <= 0 or not isinstance(term, list) or not term or head(term) == "quote":
                return term
            key = (id(term), remaining)
            if key in memo:
                return memo[key][1]
            allocated += len(term) + 1
            if allocated > NORMALIZATION_LIMIT:
                raise AnalysisIncomplete("bounded unfolding allocation budget exhausted")
            expanded = [term[0]] + [walk(item, remaining - 1) for item in term[1:]]
            name = head(expanded)
            function = self.functions.get(name) if name else None
            if (function is not None and isinstance(function.formals, list)
                    and name not in calls(function.body)
                    and len(function.formals) == len(expanded) - 1):
                bindings = {str(f): arg for f, arg in zip(function.formals, expanded[1:])
                            if isinstance(f, Sym)}
                expanded = walk(beta_apply(logic_body(function), bindings), remaining - 1)
            memo[key] = (term, expanded)
            return expanded

        return walk(form, depth)

    # -- detectors -------------------------------------------------------

    def suspect_reasons(self, theorem: Theorem) -> list[str]:
        reasons: list[str] = []
        try:
            return self._suspect_reasons(theorem, reasons)
        except (AnalysisIncomplete, RecursionError) as error:
            # Resource exhaustion is an unresolved analysis, never evidence
            # that this theorem escaped all assurance detectors.
            reasons.append(f"analysis-incomplete: {type(error).__name__}: {error}")
            return sorted(set(reasons))

    def _suspect_reasons(self, theorem: Theorem, reasons: list[str]) -> list[str]:
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

        # 6. The statement is definitional in a shape 4 and 5 do not read
        #    (lane audit-fixes, 2026-09-27; the keystone audit found ten such
        #    registered keystones): one IF/COND arm selected by a constant
        #    argument or by the hypotheses, an ``iff`` with the definition's
        #    own test, or two sides that unfold to the same term
        #    (accessor-of-constructor).
        arm = self.definitional_statement(theorem.statement)
        if arm:
            reasons.append(arm)

        # 7. A `*-preserves-*` name whose statement never calls its own subject.
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
                body = beta_apply(logic_body(function), bindings)
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
            if same(beta_apply(logic_body(function), bindings), conclusion):
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
            body = beta_apply(logic_body(function), bindings)
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

    def definitional_statement(self, statement: object) -> str | None:
        """Every conclusion conjunct is a definitional fact about one call.

        A conjunct counts when it is (a) ``(equal (f ARGS) V)`` where the
        constant arguments and the hypotheses decide f's IF/COND tests down
        to one arm and V is that arm; (b) ``(iff (f ARGS) TEST)`` where f's
        body is ``(if TEST NON-NIL nil)``; (c) ``(equal L R)`` whose sides
        unfold (non-recursive definitions, car/cdr of a constructor) to the
        same term; or (d) a ground check on a value (a) already fixed,
        ``(not (member-equal (f ...) '(437 439)))``.  One real conjunct and
        the statement is not flagged.
        """
        statement = beta(statement)
        parts: list[tuple[list, object]] = []
        for top in conjuncts(statement):
            hypotheses, conclusion = split_implication(top)
            for conjunct in conjuncts(conclusion):
                parts.append(([normalise_eq(h) for h in hypotheses],
                              normalise_eq(conjunct)))
        found: list[str] = []
        fixed: list[tuple[object, object]] = []
        pending: list[object] = []
        for hypotheses, conjunct in parts:
            reason = (self.arm_of_definition(hypotheses, conjunct, fixed)
                      or self.iff_of_definition_test(conjunct)
                      or self.unfolds_alike(conjunct))
            if reason:
                found.append(reason)
            else:
                pending.append(conjunct)
        if not found:
            return None
        for conjunct in pending:
            if not ground_after(conjunct, fixed):
                return None
        return sorted(set(found))[0]

    def arm_of_definition(self, hypotheses: list, conclusion: object,
                          fixed: list) -> str | None:
        if head(conclusion) != "equal" or len(conclusion) != 3:
            return None
        for call, value in ((conclusion[1], conclusion[2]),
                            (conclusion[2], conclusion[1])):
            name = head(call)
            function = self.functions.get(name) if name else None
            if function is None or not isinstance(function.formals, list):
                continue
            if len(function.formals) != len(call) - 1:
                continue
            bindings = {str(f): a for f, a in zip(function.formals, call[1:])
                        if isinstance(f, Sym)}
            body = normalise_eq(expand_cond(beta_apply(logic_body(function), bindings)))
            arm, decided = select_arm(body, hypotheses)
            if decided and arm is not None and same(arm, value):
                fixed.append((call, value))
                how = ("constant arguments" if not hypotheses
                       else "the hypotheses")
                return (f"arm-of-definition: {how} select one IF/COND arm of "
                        f"{name} and the conclusion is that arm's value")
        return None

    def iff_of_definition_test(self, conclusion: object) -> str | None:
        if head(conclusion) != "iff" or len(conclusion) != 3:
            return None
        for call, test in ((conclusion[1], conclusion[2]),
                           (conclusion[2], conclusion[1])):
            name = head(call)
            function = self.functions.get(name) if name else None
            if function is None or not isinstance(function.formals, list):
                continue
            if len(function.formals) != len(call) - 1:
                continue
            bindings = {str(f): a for f, a in zip(function.formals, call[1:])
                        if isinstance(f, Sym)}
            body = normalise_eq(expand_cond(beta_apply(logic_body(function), bindings)))
            if head(body) != "if" or len(body) != 4:
                continue
            _, t, then, otherwise = body
            if non_nil_literal(then) and same(otherwise, Sym("nil")) \
                    and same(t, normalise_eq(test)):
                return (f"iff-of-definition-test: {name} is (if TEST non-nil "
                        f"nil) and the statement is its truth iff TEST")
            if non_nil_literal(otherwise) and same(then, Sym("nil")) \
                    and same([Sym("not"), t], normalise_eq(test)):
                return (f"iff-of-definition-test: {name} is (if TEST nil "
                        f"non-nil) and the statement is its truth iff (not TEST)")
        return None

    def unfolds_alike(self, conclusion: object) -> str | None:
        if head(conclusion) != "equal" or len(conclusion) != 3:
            return None
        left, right = conclusion[1], conclusion[2]
        if same(left, right) or not (calls(left) or calls(right)):
            return None
        a = self.unfold_fully(left)
        b = self.unfold_fully(right)
        if a is None or b is None:
            return None
        if same(normalise_eq(a), normalise_eq(b)):
            return ("definition-restated: both sides unfold to the same term "
                    "(non-recursive definitions, accessor of constructor)")
        return None

    def unfold_fully(self, form: object, budget: int = 200,
                     limit: int = 4000) -> object | None:
        """Finite definitional detector: None outside its existing envelope.

        This detector deliberately stops after BUDGET definitions or LIMIT
        term cells. Those established boundaries differ from an unexpected
        normalization work/recursion failure, which invalidates analysis.
        """
        try:
            return _Normalizer(limit=limit, functions=self.functions,
                               unfold_budget=budget, finite_detector=True).normalize(form)
        except DetectorBoundary:
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


def symbols_of(form: object, found: "set[str] | None" = None) -> set[str]:
    """Every symbol anywhere in FORM, quoted subforms included."""
    found = set() if found is None else found
    stack = [form]
    while stack:
        item = stack.pop()
        if isinstance(item, Sym):
            found.add(str(item))
        elif isinstance(item, list):
            stack.extend(item)
    return found


def _form_digest(form: object) -> str:
    return hashlib.blake2b(repr(form).encode(), digest_size=16).hexdigest()


def _closure_digests(own: dict[str, str], edges: dict[str, list[str]]) -> dict[str, str]:
    """Each node's digest over its own and everything it reaches (Tarjan's
    strongly connected components, iteratively; a cycle shares one digest)."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on_stack: set[str] = set()
    stack: list[str] = []
    component: dict[str, int] = {}
    components: list[list[str]] = []
    counter = 0
    for start in sorted(own):
        if start in index:
            continue
        work = [(start, 0)]
        while work:
            node, position = work.pop()
            if position == 0:
                index[node] = low[node] = counter
                counter += 1
                stack.append(node)
                on_stack.add(node)
            successors = edges.get(node, [])
            for next_position in range(position, len(successors)):
                child = successors[next_position]
                if child not in index:
                    work.append((node, next_position + 1))
                    work.append((child, 0))
                    break
                if child in on_stack:
                    low[node] = min(low[node], index[child])
            else:
                if low[node] == index[node]:
                    members = []
                    while True:
                        member = stack.pop()
                        on_stack.discard(member)
                        component[member] = len(components)
                        members.append(member)
                        if member == node:
                            break
                    components.append(sorted(members))
                if work:
                    parent = work[-1][0]
                    low[parent] = min(low[parent], low[node])
    # Components complete in reverse topological order: callees first.
    digests: list[str] = []
    for members in components:
        h = hashlib.blake2b(digest_size=16)
        reached = set()
        for member in members:
            h.update(member.encode() + b"=" + own[member].encode())
            reached.update(component[c] for c in edges.get(member, []))
        for other in sorted(reached - {component[members[0]]}):
            h.update(digests[other].encode())
        digests.append(h.hexdigest())
    return {name: digests[component[name]] for name in own}


def _suspect_cache_read(path: Path) -> dict[str, list[str]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    if not isinstance(data, dict) or data.get("format") != _suspect_cache_format():
        return {}
    entries = data.get("entries")
    return entries if isinstance(entries, dict) else {}


def _suspect_cache_write(path: Path, entries: dict[str, list[str]]) -> None:
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        descriptor, name = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            json.dump({"format": _suspect_cache_format(), "entries": entries}, handle)
        os.replace(name, path)
    except OSError:
        pass


def _suspect_cache_format() -> str:
    """The detectors are this file: a changed ledger.py is a fresh cache."""
    return hashlib.sha256(b"fn-suspect-cache-1\0" + Path(__file__).resolve().read_bytes()
                          ).hexdigest()


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


# Analysis budgets bound tooling expansion, not source/runtime data. An
# exhausted budget is emitted as unresolved assurance analysis.
NORMALIZATION_LIMIT = 100_000
NORMALIZATION_WORK = 1_000_000
class AnalysisIncomplete(RuntimeError):
    pass


class DetectorBoundary(RuntimeError):
    """The definitional detector's established finite search envelope."""


def bounded_size(form: object, limit: int, memo: dict[int, int]) -> int:
    """Expanded tree weight of a shared term; stop before expanding its DAG."""
    if not isinstance(form, list):
        return 1
    if id(form) in memo:
        return memo[id(form)]
    total = 1
    for item in form:
        total += bounded_size(item, limit, memo)
        if total > limit:
            raise AnalysisIncomplete("normalization term budget exhausted")
    memo[id(form)] = total
    return total


@dataclass
class _Binding:
    term: object
    environment: dict


class _Normalizer:
    """Demand-driven beta/projection with shared binding values.

    Expose a constructor before traversing its children. CAR/CDR/NTH choose
    the needed arm while it is still syntax, so discarded observer traces
    never become expanded trees. Binding environments implement parallel
    LET/lambda and sequential LET* without copying substituted bodies.
    """

    def __init__(self, *, limit: int = NORMALIZATION_LIMIT,
                 functions: dict | None = None, unfold_budget: int = 200,
                 finite_detector: bool = False):
        self.limit = limit
        self.functions = functions or {}
        self.unfold_budget = unfold_budget
        self.work = 0
        self.memo: dict[tuple[int, int], object] = {}
        self.sizes: dict[int, int] = {}
        self.environments: list[dict] = []   # prevent identity reuse
        self.terms: list[object] = []
        self.recursive: dict[str, bool] = {}
        self.finite_detector = finite_detector
        self.allocated = 0

    def weight(self, term: object) -> int:
        try:
            return bounded_size(term, self.limit, self.sizes)
        except AnalysisIncomplete:
            if self.finite_detector:
                raise DetectorBoundary("definitional term boundary reached") from None
            raise

    def tick(self) -> None:
        self.work += 1
        if self.work > NORMALIZATION_WORK:
            raise AnalysisIncomplete("normalization work budget exhausted")

    def scope(self, parent: dict) -> dict:
        self.work += len(parent) + 1
        if self.work > NORMALIZATION_WORK:
            raise AnalysisIncomplete("binding environment budget exhausted")
        environment = parent.copy()
        self.environments.append(environment)
        return environment

    def expose(self, term: object, environment: dict) -> tuple[object, dict]:
        while True:
            self.tick()
            if isinstance(term, Sym) and str(term) in environment:
                binding = environment[str(term)]
                term, environment = binding.term, binding.environment
                continue
            if not isinstance(term, list) or not term or head(term) == "quote":
                return term, environment
            name = head(term)
            if name in ("let", "let*") and len(term) >= 3 and isinstance(term[1], list):
                current = self.scope(environment)
                for pair in term[1]:
                    if isinstance(pair, list) and len(pair) == 2 and isinstance(pair[0], Sym):
                        outer = self.scope(current) if name == "let*" else environment
                        current[str(pair[0])] = _Binding(pair[1], outer)
                term, environment = strip_declares(term[2:]), current
                continue
            if isinstance(term[0], list) and head(term[0]) == "lambda" and len(term[0]) >= 3:
                formals = term[0][1] if isinstance(term[0][1], list) else []
                current = self.scope(environment)
                for formal, argument in zip(formals, term[1:]):
                    if isinstance(formal, Sym):
                        current[str(formal)] = _Binding(argument, environment)
                term, environment = term[0][-1], current
                continue
            match = CXR.match(name or "")
            if match and len(term) == 2 and len(match.group(1)) > 1:
                inner = term[1]
                for letter in reversed(match.group(1)):
                    inner = [Sym("car" if letter == "a" else "cdr"), inner]
                    self.terms.append(inner)
                term = inner
                continue
            if name in ("car", "cdr") and len(term) == 2:
                argument, outer = self.expose(term[1], environment)
                if head(argument) == "cons" and len(argument) == 3:
                    term, environment = argument[1 if name == "car" else 2], outer
                    continue
                if head(argument) == "list":
                    if len(argument) == 1:
                        return Sym("nil"), outer
                    if name == "car":
                        term, environment = argument[1], outer
                        continue
                    term = [Sym("list")] + argument[2:] if len(argument) > 2 else Sym("nil")
                    self.terms.append(term)
                    environment = outer
                    continue
            if name == "nth" and len(term) == 3 and isinstance(term[1], int):
                argument, outer = self.expose(term[2], environment)
                if head(argument) == "list":
                    index = max(0, term[1])  # ACL2's NFIX, not Python negative indexing
                    term = argument[index + 1] if index + 1 < len(argument) else Sym("nil")
                    environment = outer
                    continue
            function = self.functions.get(name)
            if function is not None and isinstance(function.formals, list) and len(function.formals) == len(term) - 1:
                if name not in self.recursive:
                    self.recursive[name] = name in calls(logic_body(function))
                if not self.recursive[name]:
                    self.unfold_budget -= 1
                    if self.unfold_budget < 0:
                        raise DetectorBoundary("definition unfolding boundary reached")
                    current = self.scope({})
                    for formal, argument in zip(function.formals, term[1:]):
                        if isinstance(formal, Sym):
                            current[str(formal)] = _Binding(argument, environment)
                    term, environment = logic_body(function), current
                    continue
            return term, environment

    def normalize(self, term: object, environment: dict | None = None) -> object:
        if environment is None:
            environment = self.scope({})
        key = (id(term), id(environment))
        if key in self.memo:
            return self.memo[key]
        value, outer = self.expose(term, environment)
        exposed_key = (id(value), id(outer))
        if exposed_key in self.memo:
            self.memo[key] = self.memo[exposed_key]
            return self.memo[key]
        if not isinstance(value, list) or not value or head(value) == "quote":
            if self.finite_detector:
                self.weight(value)
            self.memo[key] = value
            self.memo[exposed_key] = value
            return value
        self.allocated += len(value) + 1
        if self.allocated > (NORMALIZATION_LIMIT if self.finite_detector else self.limit):
            raise AnalysisIncomplete("normalization allocation budget exhausted")
        result: list = []
        total = 1
        for index, item in enumerate(value):
            normalized = (item if index == 0 and isinstance(item, Sym)
                          else self.normalize(item, outer))
            if self.finite_detector:
                total += self.weight(normalized)
                if total > self.limit:
                    raise DetectorBoundary("definitional term boundary reached")
            result.append(normalized)
        if self.finite_detector:
            self.sizes[id(result)] = total
        self.memo[key] = result
        self.memo[exposed_key] = result
        self.terms.append(result)
        return result


def beta(form: object) -> object:
    """Normalize bindings and sound constructor projections before expansion."""
    return _Normalizer().normalize(form)


def beta_apply(form: object, bindings: dict[str, object]) -> object:
    """Bind call arguments lazily, then beta/project before duplication."""
    normalizer = _Normalizer()
    environment = normalizer.scope({})
    for name, argument in bindings.items():
        environment[name] = _Binding(argument, {})
    return normalizer.normalize(form, environment)


def strip_declares(body: list) -> object:
    """The value form of a ``let`` body, ignoring declarations."""
    return body[-1] if body else Sym("nil")


EQUALITY_SPELLINGS = ("eq", "eql", "=")
def normalise_eq(form: object) -> object:
    """Equality spellings, preserving sharing in normalized observer terms."""
    form = normalise_null(form)
    memo: dict[int, object] = {}

    def walk(term):
        if not isinstance(term, list) or not term or head(term) == "quote":
            return term
        if id(term) in memo:
            return memo[id(term)]
        parts = [walk(part) for part in term]
        if head(term) in EQUALITY_SPELLINGS and len(parts) == 3:
            parts = [Sym("equal"), parts[1], parts[2]]
        elif head(term) == "list" and len(parts) > 1 and all(literal(p) for p in parts[1:]):
            parts = [Sym("quote"), [p[1] if head(p) == "quote" else p for p in parts[1:]]]
        memo[id(term)] = parts
        return parts

    return walk(form)


def expand_cond(form: object, _memo: dict | None = None) -> object:
    """COND as nested IF, without copying shared subterms."""
    if not isinstance(form, list) or not form or head(form) == "quote":
        return form
    _memo = {} if _memo is None else _memo
    if id(form) in _memo:
        return _memo[id(form)]
    if head(form) == "cond":
        result: object = Sym("nil")
        for clause in reversed(form[1:]):
            if not isinstance(clause, list) or not clause:
                continue
            test = expand_cond(clause[0], _memo)
            value = expand_cond(clause[-1], _memo) if len(clause) > 1 else test
            result = value if same(test, Sym("t")) else [Sym("if"), test, value, result]
    else:
        result = [expand_cond(item, _memo) for item in form]
    _memo[id(form)] = result
    return result


def literal(form: object) -> bool:
    """A self-evaluating form: a number, a string, a keyword, t, nil, a quote."""
    if isinstance(form, Sym):
        return form.startswith(":") or form in ("t", "nil")
    if isinstance(form, (int, float, str)):
        return True
    return head(form) == "quote" and len(form) == 2


def non_nil_literal(form: object) -> bool:
    """A form whose value is never nil: a non-nil literal or a constructor."""
    if literal(form):
        return not same(form, Sym("nil")) and not same(form, [Sym("quote"), Sym("nil")])
    return head(form) in ("cons", "list", "list*") and len(form) > 1


def decide(test: object, facts: list, _memo: dict | None = None) -> bool | None:
    memo = {} if _memo is None else _memo
    if id(test) not in memo:
        memo[id(test)] = _decide(test, facts, memo)
    return memo[id(test)]


def _decide(test: object, facts: list, memo: dict) -> bool | None:
    """The truth of TEST from literal arithmetic and the hypotheses FACTS."""
    if any(same(test, fact) for fact in facts):
        return True
    if any(same([Sym("not"), test], fact) for fact in facts):
        return False
    if literal(test):
        return not (same(test, Sym("nil")) or same(test, [Sym("quote"), Sym("nil")]))
    name = head(test)
    if name == "not" and len(test) == 2:
        inner = decide(test[1], facts, memo)
        return None if inner is None else not inner
    if name in ("and", "or"):
        values = [decide(part, facts, memo) for part in test[1:]]
        if name == "and":
            if any(v is False for v in values):
                return False
            return True if all(v is True for v in values) else None
        if any(v is True for v in values):
            return True
        return False if all(v is False for v in values) else None
    if name == "equal" and len(test) == 3:
        left, right = test[1], test[2]
        if literal(left) and literal(right):
            return same(left, right)
        for subject, constant in ((left, right), (right, left)):
            if not literal(constant):
                continue
            for fact in facts:
                if head(fact) == "equal" and len(fact) == 3:
                    for known, value in ((fact[1], fact[2]), (fact[2], fact[1])):
                        if literal(value) and same(known, subject):
                            return same(value, constant)
        return None
    if name == "consp" and len(test) == 2:
        for fact in facts:
            if head(fact) == "equal" and len(fact) == 3:
                for known, value in ((fact[1], fact[2]), (fact[2], fact[1])):
                    if (head(known) == "car" and len(known) == 2
                            and same(known[1], test[1]) and non_nil_literal(value)):
                        return True
    return None


def select_arm(body: object, facts: list) -> tuple[object | None, bool]:
    """Walk BODY's IF chain, deciding each test; the arm reached and whether
    any test was decided.  ``(None, _)`` when a test stays undecided."""
    decided = False
    while head(body) == "if" and len(body) == 4:
        verdict = decide(body[1], facts)
        if verdict is None:
            return None, decided
        decided = True
        body = body[2] if verdict else body[3]
    return body, decided


def ground_after(conjunct: object, fixed: list) -> bool:
    """CONJUNCT, with each fixed call replaced by its value, has no variable
    and calls only built-in list and equality functions."""
    for call, value in fixed:
        conjunct = replace_form(conjunct, call, value)
    return ground(conjunct)


GROUND_FUNCTIONS = {"not", "equal", "member-equal", "member", "and", "or",
                    "consp", "atom", "natp", "integerp", "stringp", "symbolp",
                    "keywordp", "<", "<=", ">", ">=", "cons", "list", "car", "cdr"}
def ground(form: object, _memo: dict | None = None) -> bool:
    if isinstance(form, Sym):
        return literal(form)
    if not isinstance(form, list) or head(form) == "quote":
        return True
    memo = {} if _memo is None else _memo
    if id(form) not in memo:
        memo[id(form)] = (head(form) in GROUND_FUNCTIONS
                          and all(ground(item, memo) for item in form[1:]))
    return memo[id(form)]


def replace_form(form: object, target: object, value: object,
                 _memo: dict | None = None) -> object:
    memo = {} if _memo is None else _memo
    if id(form) in memo:
        return memo[id(form)]
    if same(form, target):
        result = value
    elif isinstance(form, list) and head(form) != "quote":
        result = [replace_form(item, target, value, memo) for item in form]
    else:
        result = form
    memo[id(form)] = result
    return result


CXR = re.compile(r"c([ad]{1,4})r\Z")
def if_branches(form: object, found: list | None = None,
                _seen: set[int] | None = None) -> list:
    """Every ``(if TEST THEN ELSE)`` as a triple."""
    found = [] if found is None else found
    if isinstance(form, list) and head(form) != "quote":
        _seen = set() if _seen is None else _seen
        if id(form) in _seen:
            return found
        _seen.add(id(form))
        if head(form) == "if" and len(form) == 4:
            found.append((form[1], form[2], form[3]))
        for item in form:
            if_branches(item, found, _seen)
    return found


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


def included_path(book: Book, reference: str) -> str:
    """The repository path a book's ``include-book`` string names."""
    return resolve((Path(book.path).parent / reference).with_suffix(".lisp").as_posix())


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
        if not include_is_external(form):
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


def host_paths(root: Path | None = None) -> list[tuple[Path, str]]:
    """Every `.lisp` outside `books/` and `tests/acl2/` that the tree loads.

    `host/` and `host/native/` are the tree's two host directories; anything
    else reaches this list by being named in an `(ld "...")` that a host file
    or a `tools/*.py` bridge issues.
    """
    root = ROOT if root is None else root
    found: dict[str, Path] = {}
    for directory in HOST_DIRS:
        for path in sorted((root / directory).glob("*.lisp")):
            found[path.relative_to(root).as_posix()] = path
    sources = [root / relative for relative in found] + sorted((root / "tools").glob("*.py"))
    for source in sources:
        for reference in LD_REFERENCE.findall(source.read_text(encoding="utf-8")):
            relative = resolve(reference)
            if (relative.startswith(("books/", "tests/acl2/"))
                    or not (root / relative).is_file()):
                continue
            found[relative] = root / relative
    return [(path, relative) for relative, path in sorted(found.items())]


LD_REFERENCE = re.compile(r'\((?:ld|load)\s+"([^"]+\.lisp)"')
def load_hosts() -> dict[str, HostFile]:
    return {relative: analyze_host(path, relative) for path, relative in host_paths()}


def acl2_builtins() -> set[str]:
    return builtin_names(BUILTINS)


def builtin_names(path: Path) -> set[str]:
    """The lower-case symbols in one reviewed runtime vocabulary file."""
    if not path.is_file():
        return set()
    return {line.split(";", 1)[0].strip().lower()
            for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith(";")}


def raw_load_references(form: object, raw: bool = False) -> list[str]:
    """The literal `load` targets executed in an explicit raw-mode region.

    This is intentionally structural rather than a path convention.  A
    `host/native/` file is raw only when a build form enables raw mode and
    loads it; ordinary ACL2 wrappers retain ACL2's vocabulary.  `progn!` is
    sequential, so a later `(set-raw-mode nil)` turns the scope off again.
    """
    if not isinstance(form, list) or not form:
        return []
    name = head(form)
    if name in ("quote", "quasiquote"):
        return []
    if name in ("progn", "progn!"):
        found: list[str] = []
        enabled = raw
        for item in form[1:]:
            if (head(item) == "set-raw-mode" and len(item) >= 2
                    and isinstance(item[1], Sym)):
                enabled = str(item[1]) == "t"
                continue
            found.extend(raw_load_references(item, enabled))
        return found
    found = []
    if raw and name == "load" and len(form) >= 2 and isinstance(form[1], str):
        found.append(form[1])
    for item in form[1:]:
        found.extend(raw_load_references(item, raw))
    return found


def raw_host_paths(tree: "Tree") -> set[str]:
    """Host files explicitly loaded in raw mode while a trust tag is active."""
    paths: set[str] = set()
    for host in tree.hosts.values():
        base = Path(host.path).parent
        trusted = False
        for form, _line in host.forms:
            if head(form) == "defttag":
                trusted = (len(form) >= 2 and isinstance(form[1], Sym)
                           and str(form[1]) != "nil")
                continue
            if not trusted:
                continue
            for reference in raw_load_references(form):
                for candidate in (resolve((base / reference).as_posix()),
                                  resolve(reference)):
                    if candidate in tree.hosts:
                        paths.add(candidate)
                        break
    return paths


HOST_DIRS = ("host", "host/native")
def book_paths(root: Path | None = None) -> list[tuple[Path, str]]:
    root = ROOT if root is None else root
    found = []
    for directory in ("books", "tests/acl2"):
        for path in sorted((root / directory).glob("*.lisp")):
            found.append((path, path.relative_to(root).as_posix()))
    return found


def makefile_roots(root: Path | None = None) -> list[str]:
    root = ROOT if root is None else root
    text = (root / "Makefile").read_text(encoding="utf-8")
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
        # Normalize before lookup as well as in the returned set: a test
        # root's ../../books include may itself include another local book.
        relative = resolve(pending.pop())
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


_TREE_CACHE: "tuple[str, Tree] | None" = None
# The analysed tree, shared across processes: `make check` runs six checkers
# that each analysed the same bytes (~5.5 s apiece).  An entry is named by
# the digest of everything the analysis is a function of -- the analyser's
# own source, the Python that ran it, the tree root, every input file's
# path and bytes, and the root list -- so an entry is valid exactly when its
# name matches, and nothing is invalidated by time.  Only the directory's
# size is bounded (oldest entries evicted).  FN_LEDGER_TREE_CACHE=0 turns it
# off; a directory path moves it.
TREE_CACHE_DIR = Path(__file__).resolve().parents[1] / "build" / "cache" / "ledger-tree"
TREE_CACHE_ENTRIES = 4
_TREE_CACHE_FORMAT = b"fn-ledger-tree-cache-4"
def _tree_cache_dir(root: Path | None = None) -> "Path | None":
    """Where analysed trees persist, or None when this call must not persist.

    Not when a caller has substituted any function the analysis runs (a
    test's mock would otherwise outlive its process), and not for a tree
    other than this file's own unless explicitly supplied to load_tree.
    """
    import os
    setting = os.environ.get("FN_LEDGER_TREE_CACHE", "")
    if setting == "0":
        return None
    genuine = (book_paths, host_paths, makefile_roots, analyze_book, analyze_host, Tree)
    if genuine != _GENUINE_ANALYSIS or (root is None and ROOT != Path(__file__).resolve().parents[1]):
        return None
    return Path(setting) if setting else TREE_CACHE_DIR


def _tree_cache_read(directory: Path, key: str) -> "Tree | None":
    import gc
    import pickle
    path = directory / (key + ".pickle")
    try:
        data = path.read_bytes()
    except OSError:
        return None
    # The tree is ~1.3 million small objects; collecting while they are
    # being created costs five times the load itself.
    enabled = gc.isenabled()
    gc.disable()
    try:
        stored_key, tree = pickle.loads(data)
    except Exception:
        return None
    finally:
        if enabled:
            gc.enable()
    if stored_key != key or not isinstance(tree, Tree):
        return None
    try:
        path.touch()
    except OSError:
        pass
    return tree


def _tree_cache_write(directory: Path, key: str, tree: Tree) -> None:
    import os
    import pickle
    try:
        directory.mkdir(parents=True, exist_ok=True)
        temporary = directory / ".{}.{}.tmp".format(key, os.getpid())
        temporary.write_bytes(pickle.dumps((key, tree), protocol=pickle.HIGHEST_PROTOCOL))
        os.replace(temporary, directory / (key + ".pickle"))
        entries = sorted(directory.glob("*.pickle"), key=lambda one: one.stat().st_mtime)
        for stale in entries[:-TREE_CACHE_ENTRIES]:
            stale.unlink(missing_ok=True)
    except (OSError, pickle.PicklingError):
        # A cache that cannot be written is a slower run, never a wrong one.
        # PicklingError: a second module object named `ledger' (a test that
        # loads tools/ledger.py by path) owns the name the classes pickle as.
        pass


def _checked_tree(tree: Tree, *, lazy: bool) -> Tree:
    if not lazy:
        problems = analysis_problems(tree)
        if problems:
            raise AnalysisIncomplete(f"{len(problems)} unresolved detector analyses: "
                                     + "; ".join(problems[:10]))
    return tree


def load_tree(*, lazy: bool = False, root: Path | None = None) -> Tree:
    """The analysed tree, computed once per content of its inputs.

    One `make check` process asked for it up to five times (teeth_check:
    static findings, macro names, the recogniser, hypothesis coverage and
    teeth, the registry), and each call re-parsed every book and re-derived
    every theorem's suspect reasons: 5 x ~9 s of teeth_check's 33 s
    (harness-repair, 2026-09-25).  The key is the bytes of every book, host
    and tools file the analysis reads and the Makefile, so an edit between
    calls (a test's temporary tree) is a new analysis, never a stale one.
    Across processes the same key names an entry in TREE_CACHE_DIR, with the
    analyser's source, the Python version and the root list added to it.
    ROOT explicitly selects another repository; omitted, it uses this tree.
    Its absolute path is part of both cache keys.
    Callers read the Tree; none mutates it.

    LAZY (a caller that never reads `suspects', or reads a few books'): a
    persisted tree is used when there is one; otherwise the tree is built
    without the whole-tree suspect pass (computed on first use of
    `suspects') and is kept for this process but never persisted, so no
    other process reads a partial analysis.
    """
    global _TREE_CACHE
    explicit_root = root
    root = ROOT if root is None else Path(root).resolve()
    books = book_paths() if explicit_root is None else book_paths(root)
    hosts = host_paths() if explicit_root is None else host_paths(root)
    digest = hashlib.sha256(str(root).encode())
    for path, relative in books + hosts + [(root / "Makefile", "Makefile")]:
        digest.update(relative.encode() + b"\0")
        try:
            digest.update(path.read_bytes())
        except OSError:
            digest.update(b"\1unreadable")
        digest.update(b"\0")
    key = digest.hexdigest()
    if _TREE_CACHE is not None and _TREE_CACHE[0] == key:
        return _checked_tree(_TREE_CACHE[1], lazy=lazy)
    roots = makefile_roots() if explicit_root is None else makefile_roots(root)
    directory = _tree_cache_dir(explicit_root)
    persistent = None
    if directory is not None:
        shared = hashlib.sha256(_TREE_CACHE_FORMAT + b"\0")
        shared.update(sys.version.encode() + b"\0")
        # Pickled classes are named by their module.  `python3 tools/ledger.py`
        # runs its main() from the imported module `ledger' (see the end of
        # this file), so a script run and every importer (teeth_check,
        # green_check, ...) pickle and read the same ledger.Tree under
        # one key; before 2026-09-28 the key held __name__ and the two never
        # shared an entry (defkeystone).
        shared.update(_PICKLE_MODULE.encode() + b"\0")
        shared.update(Path(__file__).resolve().read_bytes() + b"\0")
        shared.update(key.encode() + b"\0")
        shared.update("\n".join(roots).encode())
        persistent = shared.hexdigest()
        tree = _tree_cache_read(directory, persistent)
        if tree is not None:
            _TREE_CACHE = (key, tree)
            return _checked_tree(tree, lazy=lazy)
    tree = Tree({relative: analyze_book(path, relative) for path, relative in books},
                roots,
                {relative: analyze_host(path, relative) for path, relative in hosts},
                eager=not lazy,
                suspect_cache=(directory / "suspects.json") if directory is not None else None)
    _TREE_CACHE = (key, tree)
    if lazy:
        return tree
    _checked_tree(tree, lazy=False)
    if directory is not None:
        _tree_cache_write(directory, persistent, tree)
    return tree


GUARD_STATES = ("verified", "declared-off", "default-guarded", "default-unguarded")
def book_row(book: Book, tree: Tree) -> dict:
    return book_row_with(book, tree, tree.suspects)


def book_row_with(book: Book, tree: Tree, known: dict) -> dict:
    guards = {state: 0 for state in GUARD_STATES}
    for function in book.functions:
        guards[function.guard_status] += 1
    suspects = sorted(t.name for t in book.theorems if t.name in known)
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
        "prover_refusals": len(book.prover_refusals),
        "defconsts": book.defconsts,
        "defmacros": book.defmacros,
        "encapsulates": book.encapsulates,
        "includes": sorted(book.includes),
        "system_includes": sorted(book.system_includes),
        "suspects": suspects,
        "read_error": book.read_error,
    }


def analysis_problems(tree: Tree) -> list[str]:
    """Incomplete detector runs cannot establish a clean ledger."""
    return [f"{tree.theorems[name].book}: {name}: {reason}"
            for name, reasons in tree.suspects.items() for reason in reasons
            if reason.startswith("analysis-incomplete:")]


# What _tree_cache_dir compares against: the functions as this file defines them.
_GENUINE_ANALYSIS = (book_paths, host_paths, makefile_roots, analyze_book, analyze_host, Tree)
# The module the pickled tree's classes belong to.  A script run delegates
# to the imported module below, so this is always "ledger".
_PICKLE_MODULE = "ledger"
