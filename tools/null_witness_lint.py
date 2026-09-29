#!/usr/bin/env python3
"""Empty-result assertions without a non-empty witness (warn-only teeth lint).

    python3 tools/null_witness_lint.py [--strict] [FILE ...]

A test that asserts `(equal (fn-x-lace node) nil)` -- or `(null ...)`,
`(endp ...)`, `(equal (len ...) 0)` -- over a value the machine produced pins
whatever the machine produces today as the expected value.  When that value
is a DEFECT (stx-model, 2026-09-29: stx-policy's laces were empty for every
produced node, and the old test asserted the empty lace), the test certifies
the defect.  So an empty-result assertion over a function's result needs a
POSITIVE witness beside it in the same test book: an assertion that the same
function returns something non-empty (`(consp (f ...))`, `(equal (f ...)
'(...))`, `(member-equal x (f ...))`, `(< 0 (len (f ...)))`, a negated empty
check).

Scope: tests/acl2/*.lisp, the conclusions of assert-event / assert! /
defthm / thm forms (an `implies` hypothesis is not an assertion; `not`
flips polarity; must-fail is skipped).  A function with an empty-result
assertion and no positive witness in the book is named, once per book.

Warn-only (exit 0) unless --strict.  tools/null_witness_allow.json names the
accepted ones, "BOOK FUNCTION": "why the empty result is the right answer
and no non-empty case exists"; an allowlist entry that no longer matches is
reported STALE.  (obstructions-6 item 54)
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import ledger  # noqa: E402

ALLOW = ROOT / "tools" / "null_witness_allow.json"
ASSERTIONS = {"assert-event", "assert!", "assert!-stobj", "assert$", "defthm", "thm",
              "defthmd"}
SKIP = {"must-fail", "defun", "defund", "define", "defmacro", "local-defun"}
EMPTY_TESTS = {"null", "endp", "atom", "not"}
POSITIVE_TESTS = {"consp", "true-listp-nonempty", "posp"}
MEMBERS = {"member", "member-equal", "member-eq", "assoc", "assoc-equal", "assoc-eq"}
CONSTRUCTORS = {"list", "cons", "list*", "append"}
# Heads that are not "a function the machine ran": constructors, quote, the
# predicates themselves.
NOT_PRODUCERS = {"quote", "list", "cons", "list*", "len", "car", "cdr", "nth", "equal"} | MEMBERS


def name(item) -> str | None:
    return str(item).lower() if isinstance(item, ledger.Sym) else None


def is_nil(item) -> bool:
    if name(item) == "nil":
        return True
    return (isinstance(item, list) and len(item) == 2 and name(item[0]) == "quote"
            and (item[1] == [] or name(item[1]) == "nil"))


def produced(item) -> str | None:
    """The head of a call whose value a test asserts about, or None.  A
    predicate (a name ending in p, ACL2's convention) answers a question;
    asserting it false is a refusal witness, not an empty result."""
    if isinstance(item, list) and item and name(item[0]) and \
            name(item[0]) not in NOT_PRODUCERS and not name(item[0]).endswith("p") \
            and any(computed(argument) for argument in item[1:]):
        return name(item[0])
    return None


def computed(argument) -> bool:
    """A node the machine produced: a call (not a quoted literal), or a
    variable (let-bound in a test).  A literal, a *constant* or a keyword is
    an initial or junk input: a total accessor's nil on it is no defect."""
    if isinstance(argument, list):
        return bool(argument) and name(argument[0]) not in ("quote", None)
    symbol = name(argument)
    return bool(symbol) and symbol not in ("nil", "t", "state") and \
        not symbol.startswith((":", "*", "#"))


def non_empty_constant(item) -> bool:
    if isinstance(item, (int, str)) and not isinstance(item, ledger.Sym):
        return True
    if isinstance(item, list) and item:
        head = name(item[0])
        if head == "quote":
            return not is_nil(item)
        return head in CONSTRUCTORS
    return name(item) in ("t",)


def classify(form, positive: bool, empty: set, witness: set) -> None:
    """Record the heads FORM asserts empty (EMPTY) or non-empty (WITNESS)."""
    if not isinstance(form, list) or not form:
        return
    head = name(form[0])
    if head in SKIP or head == "quote":
        return
    if head == "not" and len(form) == 2:
        inner = form[1]
        # (not (consp A)) is an empty check; (not (null A)) a positive one.
        if isinstance(inner, list) and inner and name(inner[0]) == "consp" and len(inner) == 2:
            target = produced(inner[1])
            if target:
                (empty if positive else witness).add(target)
                return
        if produced(inner) and name(inner[0]) not in EMPTY_TESTS | {"consp"}:
            target = produced(inner)
            (empty if positive else witness).add(target)
            return
        classify(inner, not positive, empty, witness)
        return
    if head in ("null", "endp", "atom") and len(form) == 2:
        target = produced(form[1])
        if target:
            (empty if positive else witness).add(target)
            return
    if head in POSITIVE_TESTS and len(form) == 2:
        target = produced(form[1])
        if target:
            (witness if positive else empty).add(target)
            return
    if head in MEMBERS and len(form) == 3:
        target = produced(form[2])
        if target and positive:
            witness.add(target)
    if head in ("equal", "eq", "eql", "=") and len(form) == 3:
        for side, other in ((form[1], form[2]), (form[2], form[1])):
            target = produced(side)
            length = (side[1] if isinstance(side, list) and len(side) == 2
                      and name(side[0]) == "len" else None)
            if target and is_nil(other):
                (empty if positive else witness).add(target)
                return
            if target and non_empty_constant(other):
                (witness if positive else empty).add(target)
                return
            if length is not None and produced(length) and isinstance(other, int):
                ((empty if other == 0 else witness) if positive else witness).add(
                    produced(length))
                return
    if head in ("<", "<=") and len(form) == 3:
        right = form[2]
        if (form[1] == 0 and isinstance(right, list) and len(right) == 2
                and name(right[0]) == "len" and produced(right[1]) and positive):
            witness.add(produced(right[1]))
            return
    if head == "implies" and len(form) == 3:
        classify(form[2], positive, empty, witness)
        return
    for item in form[1:]:
        classify(item, positive, empty, witness)


def book_findings(path: Path, relative: str) -> list[tuple[str, int]]:
    """(function, line of its first empty assertion) with no positive witness."""
    empty_at: dict[str, int] = {}
    witnessed: set[str] = set()
    try:
        forms = list(ledger.Reader(path.read_text(encoding="utf-8")).top_level())
    except Exception:  # noqa: BLE001  an unreadable book is another lint's finding
        return []

    def visit(form, line: int) -> None:
        if not isinstance(form, list) or not form:
            return
        head = name(form[0])
        if head in ("local", "encapsulate", "progn"):
            for item in form[1:]:
                visit(item, line)
            return
        if head not in ASSERTIONS:
            return
        body = form[2] if head in ("defthm", "defthmd") and len(form) > 2 else \
            form[1] if len(form) > 1 else None
        empty: set[str] = set()
        classify(body, True, empty, witnessed)
        for target in empty:
            empty_at.setdefault(target, line)

    for form, line in forms:
        visit(form, line)
    return sorted((target, line) for target, line in empty_at.items()
                  if target not in witnessed)


def load_allow(path: Path | None = None) -> dict[str, str]:
    path = path or ALLOW
    if not path.is_file():
        return {}
    return {key: value for key, value in
            json.loads(path.read_text(encoding="utf-8")).get("allow", {}).items()}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("files", nargs="*", help="test books (default tests/acl2/*.lisp)")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 on an unallowed finding or a STALE allowlist entry")
    args = parser.parse_args(argv)
    paths = ([ROOT / f for f in args.files] if args.files
             else sorted((ROOT / "tests" / "acl2").glob("*.lisp")))
    allow = load_allow()
    seen: set[str] = set()
    warned = 0
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        for target, line in book_findings(path, relative):
            key = f"{relative} {target}"
            seen.add(key)
            if key in allow:
                continue
            warned += 1
            print(f"WARN {relative}:{line} {target}: asserted EMPTY (nil / null / endp / "
                  f"len 0) with no non-empty witness of {target} in this book -- add a "
                  f"positive case (a produced node where it is non-empty), or allow it in "
                  f"{ALLOW.relative_to(ROOT)} with the reason the empty value is right")
    stale = sorted(key for key in allow if key not in seen
                   and (args.files == [] or key.split()[0] in args.files))
    for key in stale:
        print(f"STALE {key}: allowed in {ALLOW.relative_to(ROOT)} but no longer found")
    print(f"null_witness_lint: {warned} empty-result assertion(s) without a non-empty "
          f"witness in {len(paths)} test book(s); {len(allow)} allowed; {len(stale)} stale"
          + ("" if args.strict else " (warn-only)"))
    return 1 if args.strict and (warned or stale) else 0


if __name__ == "__main__":
    raise SystemExit(main())
