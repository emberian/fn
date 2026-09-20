#!/usr/bin/env python3
"""The session-depth check: every session reaches the level its callee wants.

The served command chain is four records deep.  A served connection's session
is an AUTH session (`books/nntp-auth.lisp`, `fn-auth-open-session`) over a
PEER session (`books/peer-inbound.lisp`) over a POST session
(`books/nntp-post.lisp`) over the READER session (`books/nntp-session.lisp`).
Each wrapper's base accessor descends exactly one level:

    auth --fn-auth-session-base--> peer --fn-peer-session-base--> post
         --fn-post-session-base--> reader

All three base accessors are `car` of the record.  That is why a wrong depth
is silent: handing an auth session to a function that wants a peer session
does not fail, it reads the peer session's fields out of the auth session's
slots, or -- worse -- the callee tests a shape recognizer, finds it false and
answers with a benign value.  Four instances of exactly this shipped on
2026-09-20:

  * `fn-own-conn-boundedp` tested `fn-post-sessionp` of the whole connection
    session, so it was false on every connection: the owner never enqueued,
    `fn-own-advance` was a no-op, `fn-own-read` dropped every connection
    after its first read.
  * `books/served.lisp`'s `fn-served-post-outcome` reached one level short,
    and `fn-nntp-post-outcome` answers a non-`fn-post-sessionp` argument with
    NO EFFECTS, so the served path emitted neither 240 nor 441.
  * `tests/acl2/served-tests.lisp` had the same short reach on the test side.
  * `fn-served-transit-outcome` handed the auth session to
    `fn-peer-transit-outcome`; unobservable only because the transit reply
    octets happen to ignore the session.

The shapes are syntactic, so this check is static.  It reads the books with
`tools/ledger.py`'s s-expression reader (no ACL2, no evaluation), infers the
session level of every formal from the calls each definition makes, and then
reports two kinds of defect and one kind of style drift:

  DEPTH   a base accessor applied to an expression at the wrong level
          (`(fn-post-session-base <an auth session>)`);
  ARGUMENT
          an expression at a known level passed where the callee's formal is
          at a different one (`(fn-peer-transit-outcome <an auth session>)`);
  CHAIN   a base-accessor walk spelled by hand outside the named projections
          (style: it is how a level gets missed when a wrapper is added).

DEPTH and ARGUMENT fail the check.  CHAIN is reported and fails only under
`--strict`, in the shape `tools/transcribe_check.py` established: a defect
fails, drift is counted.

Run: `python3 tools/session_depth.py [--strict] [--json] [paths...]`
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

_SPEC = importlib.util.spec_from_file_location("ledger", ROOT / "tools" / "ledger.py")
_ledger = importlib.util.module_from_spec(_SPEC)
sys.modules.setdefault("ledger", _ledger)
_SPEC.loader.exec_module(_ledger)

Sym = _ledger.Sym


class Reader(_ledger.Reader):
    """The ledger's reader, remembering the line every list form starts on.

    A finding names the line of the term it is about, not the line of the
    top-level form that contains it: `books/owner-invariants.lisp` holds one
    `defthm` whose body spells nine walks over eighty lines.
    """

    def __init__(self, source: str) -> None:
        super().__init__(source)
        self.lines: dict[int, int] = {}

    def form(self) -> object:
        self.skip_space()
        start = self.pos
        value = super().form()
        if isinstance(value, list):
            self.lines[id(value)] = self.line(start)
        return value

# ---------------------------------------------------------------------------
# The ladder
# ---------------------------------------------------------------------------

LEVELS = ("auth", "peer", "post", "reader")
DEEPER = {"auth": "peer", "peer": "post", "post": "reader"}

# The base accessor of each wrapper, and the level it descends from.
BASE = {
    "fn-auth-session-base": "auth",
    "fn-peer-session-base": "peer",
    "fn-post-session-base": "post",
}

# The named projections: the only definitions allowed to spell a walk.  Every
# other site says the projection's name instead, so adding a wrapper is one
# edit here and not a sweep of the tree.
PROJECTION = {
    "fn-auth-post-session": "post",
    "fn-auth-reader-session": "reader",
    "fn-peer-reader-session": "reader",
}

# What a function returns, where the body cannot say it: the constructors
# (they build a `list`) and the whole-connection accessors.
RETURNS = {
    "fn-served-conn-session": "auth",
    "fn-own-conn-session": "auth",
    "fn-auth-open-session": "auth",
    "fn-auth-make-session": "auth",
    "fn-auth-with-base": "auth",
    "fn-peer-open-session": "peer",
    "fn-peer-make-session": "peer",
    "fn-peer-with-base": "peer",
    "fn-post-open-session": "post",
    "fn-post-make-session": "post",
    "fn-nntp-open-session": "reader",
    "fn-nntp-make-session": "reader",
    "fn-nntp-set-cursor": "reader",
    "fn-nntp-result-session": "reader",
}
RETURNS.update({name: DEEPER[level] for name, level in BASE.items()})
RETURNS.update(PROJECTION)

# What a constructor's session argument is, where the body cannot say it.
ARGUMENTS = {
    ("fn-auth-make-session", 0): "peer",
    ("fn-auth-with-base", 0): "auth",
    ("fn-auth-with-base", 1): "peer",
    ("fn-peer-make-session", 0): "post",
    ("fn-peer-with-base", 0): "peer",
    ("fn-peer-with-base", 1): "post",
    ("fn-post-make-session", 0): "reader",
    ("fn-nntp-make-session-not-a-function", 0): "reader",
    ("fn-nntp-set-cursor", 0): "reader",
    ("fn-nntp-make-result", 0): "reader",
}
ARGUMENTS.update({(name, 0): level for name, level in BASE.items()})
ARGUMENTS.update({(name, 0): "auth" for name in ("fn-auth-post-session",
                                                 "fn-auth-reader-session")})
ARGUMENTS[("fn-peer-reader-session", 0)] = "peer"

# `fn-post-make-result` / `fn-post-result-session` is the SHARED result record:
# nntp-post builds it over a post session, peer-inbound over a peer session,
# nntp-auth over an auth session.  It therefore carries no level and a session
# that round-trips through it is invisible to this check.  Named here so the
# blind spot is in the source and not only in the report.
UNTYPED = ("fn-post-make-result", "fn-post-result-session")

# The naming rule that seeds the rest: `fn-<tag>-session-<field>` is an
# accessor of that record and `fn-<tag>-sessionp` its recognizer, so argument
# 0 of either is at that record's level.  docs/prefixes.md pins the tags.
TAGS = {"auth": "fn-auth", "peer": "fn-peer", "post": "fn-post", "reader": "fn-nntp"}


def seed_by_name(name: str) -> str | None:
    for level, tag in TAGS.items():
        if name.startswith(tag + "-session-") or name == tag + "-sessionp":
            return level
    return None


# ---------------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------------

BINDERS = ("let", "let*")
SKIP_HEADS = ("quote", "quasiquote")


def sym(form: object) -> str | None:
    return str(form) if isinstance(form, Sym) else None


def call_head(form: object) -> str | None:
    if isinstance(form, list) and form and isinstance(form[0], Sym):
        return str(form[0])
    return None


def defun_of(form: object) -> tuple[str, list[str], list] | None:
    """(name, formals, body forms) of a `defun`/`defund`, or None."""
    head = call_head(form)
    if head not in ("defun", "defund", "defun-nx") or len(form) < 3:
        return None
    name, formals = sym(form[1]), form[2]
    if name is None or not isinstance(formals, list):
        return None
    names = [sym(f) for f in formals]
    if any(n is None or n.startswith("&") for n in names):
        return None
    return name, [n for n in names], list(form[3:])


WAIVER = "session-depth-ok:"


class Book:
    def __init__(self, path: Path, source: str) -> None:
        self.path = path
        reader = Reader(source)
        self.forms = reader.top_level()
        self.lines = reader.lines
        self.waivers = waivers_in(source)

    def line_of(self, form: object, fallback: int) -> int:
        return self.lines.get(id(form), fallback)

    def waiver(self, top_line: int) -> str | None:
        return self.waivers.get(top_line)


def waivers_in(source: str) -> dict[int, str]:
    """`; session-depth-ok: <reason>` waives the top-level form it precedes.

    The directive carries a reason, the reason is printed with the waived
    finding, and a waiver with no reason is not a waiver.  A deliberate
    wrong-depth witness is a tooth -- `tests/acl2/served-tests.lisp` forges a
    connection whose session is a bare POST session to show that
    `fn-served-connp` refuses it -- and a check with no way to say so gets
    switched off instead.
    """
    lines = source.splitlines()
    pending: str | None = None
    out: dict[int, str] = {}
    for number, text in enumerate(lines, start=1):
        stripped = text.strip()
        if WAIVER in stripped and stripped.startswith(";"):
            reason = stripped.split(WAIVER, 1)[1].strip()
            pending = reason or None
        elif not stripped or stripped.startswith(";"):
            continue
        else:
            if pending:
                out[number] = pending
            pending = None
    return out


def read_books(paths: list[Path]) -> list[Book]:
    return [Book(p, p.read_text(encoding="utf-8", errors="replace")) for p in paths]


# ---------------------------------------------------------------------------
# Inference: what level is each formal at?
# ---------------------------------------------------------------------------

CONFLICT = "conflict"


class Levels:
    """The inferred level of every formal and of every function's value."""

    def __init__(self) -> None:
        self.argument: dict[tuple[str, int], str] = dict(ARGUMENTS)
        self.returns: dict[str, str] = dict(RETURNS)
        self.conflicts: list[tuple[str, int, str, str]] = []

    def note_argument(self, name: str, index: int, level: str) -> bool:
        key = (name, index)
        known = self.argument.get(key)
        if known == level:
            return False
        if known is None:
            self.argument[key] = level
            return True
        if known != CONFLICT:
            self.conflicts.append((name, index, known, level))
            self.argument[key] = CONFLICT
            return True
        return False

    def note_return(self, name: str, level: str) -> bool:
        known = self.returns.get(name)
        if known == level:
            return False
        if known is None:
            self.returns[name] = level
            return True
        if known != CONFLICT:
            self.returns[name] = CONFLICT
            return True
        return False


def level_of(form: object, env: dict[str, str], levels: Levels) -> str | None:
    """The session level of an expression, or None when it is not known."""
    name = sym(form)
    if name is not None:
        value = env.get(name)
        return None if value in (None, CONFLICT) else value
    head = call_head(form)
    if head is None or head in SKIP_HEADS:
        return None
    if head in ("let", "let*") and len(form) >= 3:
        inner = dict(env)
        for binding in form[1] if isinstance(form[1], list) else []:
            if isinstance(binding, list) and len(binding) == 2 and sym(binding[0]):
                value = level_of(binding[1], inner if head == "let*" else env, levels)
                if value:
                    inner[sym(binding[0])] = value
                else:
                    inner.pop(sym(binding[0]), None)
        return level_of(form[-1], inner, levels)
    if head == "if" and len(form) == 4:
        left = level_of(form[2], env, levels)
        return left if left is not None and left == level_of(form[3], env, levels) else None
    if head == "mbe":
        return None
    value = levels.returns.get(head)
    return None if value in (None, CONFLICT) else value


def walk(form: object, env: dict[str, str], levels: Levels, visit) -> None:
    """Every call in `form`, with the environment in force at that call."""
    if not isinstance(form, list) or not form:
        return
    head = call_head(form)
    if head in SKIP_HEADS:
        return
    if head in BINDERS and len(form) >= 3 and isinstance(form[1], list):
        inner = dict(env)
        for binding in form[1]:
            if isinstance(binding, list) and len(binding) == 2 and sym(binding[0]):
                scope = inner if head == "let*" else env
                walk(binding[1], scope, levels, visit)
                value = level_of(binding[1], scope, levels)
                if value:
                    inner[sym(binding[0])] = value
                else:
                    inner.pop(sym(binding[0]), None)
            else:
                walk(binding, env, levels, visit)
        for item in form[2:]:
            walk(item, inner, levels, visit)
        return
    if head is not None:
        visit(form, head, env)
        for item in form[1:]:
            walk(item, env, levels, visit)
        return
    for item in form:
        walk(item, env, levels, visit)


def formal_env(name: str, formals: list[str], levels: Levels) -> dict[str, str]:
    env: dict[str, str] = {}
    for index, formal in enumerate(formals):
        value = levels.argument.get((name, index))
        if value not in (None, CONFLICT):
            env[formal] = value
    return env


def infer(books: list[Book], levels: Levels) -> None:
    definitions: list[tuple[str, list[str], list]] = []
    for book in books:
        for form, _line in book.forms:
            found = defun_of(form)
            if found:
                definitions.append(found)
                name, formals, _body = found
                seeded = seed_by_name(name)
                if seeded and formals:
                    levels.note_argument(name, 0, seeded)
    for _round in range(12):
        changed = False
        for name, formals, body in definitions:
            env = formal_env(name, formals, levels)
            index_of = {formal: i for i, formal in enumerate(formals)}

            def visit(form, head, scope, _name=name, _index=index_of):
                for position, argument in enumerate(form[1:]):
                    want = levels.argument.get((head, position))
                    if want in (None, CONFLICT):
                        continue
                    formal = sym(argument)
                    if formal is not None and formal in _index and formal not in scope:
                        nonlocal changed
                        if levels.note_argument(_name, _index[formal], want):
                            changed = True

            for item in body:
                walk(item, env, levels, visit)
            if body and name not in RETURNS:
                value = level_of(body[-1], formal_env(name, formals, levels), levels)
                if value and levels.note_return(name, value):
                    changed = True
        if not changed:
            return


# ---------------------------------------------------------------------------
# Defects that exist, are named, and belong to another lane
#
# A waiver (`; session-depth-ok:`) says a site is INTENTIONALLY at the wrong
# level.  These are the opposite: real defects, in a book this lane may not
# edit, recorded so that `make check` stays honest without being edited into
# uselessness.  Each entry names the owner and the fix.  An entry that no
# longer matches anything FAILS the check, so the list cannot rot: whoever
# fixes the site deletes its line here in the same commit.
# ---------------------------------------------------------------------------

OPEN_DEFECTS = (
    # books/owner-invariants.lisp reasons over the served connection's session
    # in eleven places and reaches ONE LEVEL SHORT in every one: it says
    # fn-peer-session-base where the connection holds an auth session, so the
    # :use instances name terms the goal does not contain.  Three of the four
    # forms the book is open at are exactly these.  Owner: w10/owner-relation
    # (the lane holding books/owner-invariants on 2026-09-20).  The fix is
    # fn-auth-session-base for the depth-1 reaches, fn-auth-post-session and
    # fn-auth-reader-session for the walks, and at :1414 an fn-auth-with-base
    # around the fn-peer-with-base so the rebuild keeps the login.
    ("books/owner-invariants.lisp", None, "fn-peer-session-base wants a peer session"),
    ("books/owner-invariants.lisp", None, "fn-peer-with-base argument 0 wants a peer session"),
)


def open_elsewhere(finding: "Finding") -> bool:
    for path, where, needle in OPEN_DEFECTS:
        if str(finding.path).endswith(path) and needle in finding.text \
                and (where is None or where == finding.where):
            return True
    return False


# ---------------------------------------------------------------------------
# The check
# ---------------------------------------------------------------------------

class Finding:
    def __init__(self, kind: str, path: Path, line: int, where: str, text: str,
                 waived: str | None = None) -> None:
        self.kind, self.path, self.line, self.where, self.text = kind, path, line, where, text
        self.waived = waived

    def as_dict(self) -> dict:
        return {"kind": self.kind, "file": str(self.path), "line": self.line,
                "context": self.where, "message": self.text, "waived": self.waived}

    def __str__(self) -> str:
        tail = f" [waived: {self.waived}]" if self.waived else ""
        return f"{self.path}:{self.line}: {self.kind}: {self.where}: {self.text}{tail}"


def render(form: object, depth: int = 0) -> str:
    if depth > 3:
        return "..."
    if isinstance(form, list):
        if not form:
            return "()"
        return "(" + " ".join(render(item, depth + 1) for item in form[:4]) + \
               (" ...)" if len(form) > 4 else ")")
    if isinstance(form, str) and not isinstance(form, Sym):
        return '"..."'
    return str(form)


def check(books: list[Book], levels: Levels) -> list[Finding]:
    findings: list[Finding] = []
    for book in books:
        for form, line in book.forms:
            found = defun_of(form)
            if found:
                name, formals, body = found
                env = formal_env(name, formals, levels)
                where = name
                items = body
            else:
                head = call_head(form)
                where = f"{head} {sym(form[1])}" if head and len(form) > 1 and sym(form[1]) \
                    else (head or "top-level")
                env, items = {}, [form]

            def visit(node, head, scope, _where=where, _book=book, _top=line,
                      _waived=book.waiver(line)):
                _line = _book.line_of(node, _top)
                # DEPTH: the accessor's own domain.
                if head in BASE and len(node) >= 2:
                    actual = level_of(node[1], scope, levels)
                    want = BASE[head]
                    if actual is not None and actual != want:
                        findings.append(Finding(
                            "DEPTH", _book.path, _line, _where,
                            f"{head} wants a {want} session, {render(node[1])} is "
                            f"{actual}: {render(node)}", _waived))
                    inner = call_head(node[1])
                    if inner in BASE and _where not in PROJECTION:
                        findings.append(Finding(
                            "CHAIN", _book.path, _line, _where,
                            f"a hand-spelled walk {inner} then {head}: say "
                            f"{spelled(inner, head)} instead", _waived))
                # ARGUMENT: the callee's formal.
                for position, argument in enumerate(node[1:]):
                    want = levels.argument.get((head, position))
                    if want in (None, CONFLICT) or head in BASE:
                        continue
                    actual = level_of(argument, scope, levels)
                    if actual is not None and actual != want:
                        findings.append(Finding(
                            "ARGUMENT", _book.path, _line, _where,
                            f"{head} argument {position} wants a {want} session, "
                            f"{render(argument)} is {actual}", _waived))

            for item in items:
                walk(item, env, levels, visit)
    return findings


def spelled(inner: str, outer: str) -> str:
    start, end = BASE[inner], DEEPER[BASE[outer]]
    for name, level in PROJECTION.items():
        if level == end and ARGUMENTS.get((name, 0)) == start:
            return name
    return f"a named {start}-to-{end} projection"


DEFAULT_PATHS = ("books", "tests/acl2", "host")


def sources(paths: list[str]) -> list[Path]:
    out: list[Path] = []
    for entry in paths:
        path = Path(entry)
        if not path.is_absolute():
            path = ROOT / path
        if path.is_dir():
            out.extend(sorted(path.rglob("*.lisp")))
        elif path.exists():
            out.append(path)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="*")
    parser.add_argument("--strict", action="store_true",
                        help="a hand-spelled walk fails too")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    books = read_books(sources(args.paths or list(DEFAULT_PATHS)))
    levels = Levels()
    infer(books, levels)
    findings = check(books, levels)

    waived = [f for f in findings if f.waived]
    real = [f for f in findings if f.kind in ("DEPTH", "ARGUMENT") and not f.waived]
    opened = [f for f in real if open_elsewhere(f)]
    defects = [f for f in real if not open_elsewhere(f)]
    chains = [f for f in findings if f.kind == "CHAIN" and not f.waived]
    # A subset run sees only the files it was given, so a missing entry there
    # says nothing; only the full sweep can call an entry stale.
    stale = [] if args.paths else [
        entry for entry in OPEN_DEFECTS
        if not any(str(f.path).endswith(entry[0]) and entry[2] in f.text
                   and (entry[1] is None or entry[1] == f.where) for f in real)]

    if args.json:
        print(json.dumps({
            "books": len(books),
            "typed_formals": sum(1 for v in levels.argument.values() if v != CONFLICT),
            "conflicts": [{"function": n, "argument": i, "first": a, "then": b}
                          for n, i, a, b in levels.conflicts],
            "open_elsewhere": [f.as_dict() for f in opened],
            "stale_open_entries": [list(entry) for entry in stale],
            "findings": [f.as_dict() for f in findings],
        }, indent=2))
    else:
        for finding in findings:
            print(f"{finding}{' [open elsewhere]' if open_elsewhere(finding) else ''}")
        for entry in stale:
            print(f"STALE: no finding matches the OPEN_DEFECTS entry {entry}: "
                  f"delete it from tools/session_depth.py")
        print(f"session_depth: {len(books)} books, "
              f"{sum(1 for v in levels.argument.values() if v != CONFLICT)} typed formals, "
              f"{len(defects)} defects, {len(chains)} hand-spelled walks, "
              f"{len(opened)} open elsewhere, {len(waived)} waived, "
              f"{len(levels.conflicts)} conflicting formals")
        for name, index, first, then in levels.conflicts:
            print(f"  conflicting formal: {name} argument {index}: {first} and {then}")
    if defects or stale or (args.strict and chains):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
