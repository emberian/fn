#!/usr/bin/env python3
"""A test book never pins a figure a book derives (D27, PINNED-FIGURES).

tests/acl2/heap-reservation-tests pinned the small preset's run heap at 582 MB
until a producing book changed and the pin went stale (train 64): a number a
book derives is derived in the test too, from the producing function or
constant, so a change in the producer moves both.  Two flags:

  * a literal equal to the current value of a named producing constant
    (FIGURES; evaluated from the books' defconsts);
  * a heap decision with a literal figure, `(:heap 724 ...)' or
    `(:refused :machine-cannot-hold-threads 2200 ...)', or an init/reserve
    line `reservation=2197 MB', in any test book but the producer's own
    (EXEMPT, each with its reason).  A format fixture (a fixed decision
    handed to a report-line or exit-code function) says so with the comment
    `pinned-fixture' within the three lines before it.

    python3 tools/pinned_figures_check.py          # exit 1 naming each pin
"""
from __future__ import annotations

from pathlib import Path
import math
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ("*fn-heap-reclaim-record-octets*", "*fn-heap-storeless-thread-octets*")
# Test books whose heap decisions are not derived figures, with the reason.
EXEMPT = {
    "tests/acl2/heap-figure-tests.lisp": "the producer's own golden examples",
    "tests/acl2/cold-read-reservation-tests.lisp": "the extender under test: its golden and its input base",
    "tests/acl2/output-reservation-tests.lisp": "the extender under test: its golden and its input base",
    "tests/acl2/bp-heap-command-tests.lisp": "an input base reservation",
    "tests/acl2/page-read-startup-tests.lisp": "an input base reservation",
    "tests/acl2/peer-flight-reservation-tests.lisp": "an input base reservation",
    "tests/acl2/reclaim-reservation-tests.lisp": "an input base reservation",
    "tests/acl2/limits-live-tests.lisp": "decisions handed to the line and word formatters",
    "tests/acl2/native-control-line-tests.lisp": "a decision handed to the line formatter",
}
DECISION = re.compile(r"\(:heap\s+\d{3,}|:machine-cannot-hold-\w+\s+\d{3,}"
                      r"|(?:reservation|heap)=\d{3,} MB")


def sexp(text: str):
    tokens = re.findall(r"\(|\)|[^\s()]+", re.sub(r'"[^"]*"|;[^\n]*', "", text))
    stack = [[]]
    for token in tokens:
        if token == "(":
            stack.append([])
        elif token == ")" and len(stack) > 1:
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(token)
    return stack[0]


def value(expr, table):
    if isinstance(expr, str):
        return int(expr) if expr.isdigit() else value(table[expr.lower()], table)
    op, args = expr[0], [value(a, table) for a in expr[1:]]
    return {"+": sum, "*": math.prod, "-": lambda a: a[0] - sum(a[1:]),
            "floor": lambda a: a[0] // a[1]}[op](args)


def figures(root: Path) -> dict:
    table = {}
    for book in (root / "books").glob("*.lisp"):
        for form in sexp(book.read_text(errors="replace")):
            if isinstance(form, list) and len(form) == 3 and form[0].lower() == "defconst":
                table[form[1].lower()] = form[2]
    out = {}
    for name in FIGURES:
        try:
            out[value(name, table)] = name
        except (KeyError, ValueError, IndexError, TypeError):
            pass
    return out


def pins(root: Path, known: dict | None = None) -> list[str]:
    known, found = figures(root) if known is None else known, []
    for path in sorted((root / "tests/acl2").glob("*.lisp")):
        rel = path.relative_to(root).as_posix()
        lines = path.read_text(errors="replace").splitlines()
        for n, line in enumerate(lines):
            code = re.sub(r";.*", "", line)
            fixture = any("pinned-fixture" in x for x in lines[max(0, n - 3):n + 1])
            for token in re.findall(r"(?<![\w*.-])\d+(?![\w.-])", code):
                if int(token) in known and rel not in EXEMPT:
                    found.append(f"{rel}:{n + 1}: {token} is {known[int(token)]}")
            if DECISION.search(code) and not fixture and rel not in EXEMPT:
                found.append(f"{rel}:{n + 1}: a heap figure is pinned in a decision")
    return found


def main() -> int:
    found = pins(ROOT)
    for line in found:
        print(f"pinned_figures_check: {line}: derive it from the book (D27)")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
