#!/usr/bin/env python3
"""Multiple-value shapes of the ACL2-mode host files, checked without ACL2.

At 9c344d1d the production image build failed on a translate error in
host/owner-host.lisp: `fn-owner-peer-carried-event` passed
`(fn-owner-clock-observation state)` as an argument, and that function
returns an error triple `(mv erp val state)` through `(value ...)`.  ACL2
refused it ("a result of shape (MV * * STATE) where a result of shape * is
required").  `make check` was green, because nothing in it translates a host
file: they are `ld`ed only by the Python bridges and by
host/native/build.lisp, and `tools/host_check.py` loads them only when
FN_ACL2 names an ACL2 and the certificates are installed.  The image build on
hbox was the first thing to see it, hours later.

This is the static half of that translate step, for one class of error: the
NUMBER of values a form returns.  It infers, for every `defun` in the books
and in the ACL2-mode host files, whether its body returns one value or an
`mv` of k values (an error triple is k = 3), iterating to a fixpoint so a
recursive or forward-calling definition gets its callee's shape.  It then
walks every ACL2-mode host definition with the shape each position requires
and reports a finding when a known shape disagrees:

  single    a function argument, a `let`/`let*` binding, an `if`/`cond`/`case`
            test or key, an `and`/`or` argument, a `value` or `mv` argument,
            an `er-let*`/`state-global-let*` value that is not the triple,
            a `defconst` value, every `pprogn` form but the last;
  k values  the term of an `mv-let` with k variables, `mv-list k`;
  triple    each `er-progn` form, each `er-let*` binding term and body;
  branches  the two arms of an `if`, and every `cond`/`case` arm, must agree
            where both are known.

Modelled forms: `if`, `cond`, `case`, `and`, `or`, `let`, `let*`, `mv-let`,
`mv?-let`, `mv`, `mv-list`, `value`, `er`, `er-progn`, `er-let*`, `pprogn`,
`prog2$`, `progn$`, `the`, `mbe`, `ec-call`, `assert$`, `state-global-let*`,
`with-output`, `quote`, and `declare`.  A head that is none of these, not a
tree `defun`, and not a single-valued ACL2 builtin (tools/acl2-builtins.txt
plus the multiple-valued table below) is UNDECIDABLE: its shape is counted
and never guessed, and a definition whose every result arm is undecidable has
no shape.  `b*`, `case-match`, lambda applications and the tree's own macros
are undecidable on purpose; the host files use none of them in ACL2 mode
today.

It does not model stobj flow (a `state` passed where a non-stobj formal is
expected), which ACL2 also rejects; it does not check the raw Common Lisp
files, which the image loads under `(set-raw-mode t)` where ACL2 does not
translate anything; and it is not `ld`.  `make check-host-translate` is the
dynamic check, when a local ACL2 and certificates exist.

    python3 tools/host_shape_check.py            # findings + counts, exit 1 on any
    python3 tools/host_shape_check.py --json build/host-shape.json
"""
from __future__ import annotations

import argparse
import functools
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402
from tools.ledger import Sym, head  # noqa: E402

# ACL2 8.7 functions and macros that return more than one value, with the
# count.  Everything else in tools/acl2-builtins.txt returns one (a stobj
# such as `state' is one value of shape STATE).
MULTI_BUILTINS = {
    "value": 3, "er-progn": 3, "er-let*": 3, "trans-eval": 3, "ld": 3,
    "getenv$": 3, "read-object": 3, "read-acl2-oracle": 3,
    "get-output-stream-string$": 3, "simple-translate-and-eval": 3,
    "sys-call+": 3,
    "open-input-channel": 2, "open-output-channel": 2, "read-byte$": 2,
    "read-char$": 2, "peek-char$": 2, "sys-call-status": 2, "random$": 2,
    "read-run-time": 2, "fmt": 2, "fmt1": 2, "fmt!": 2, "fmt1!": 2,
    "main-timer": 2,
}
SINGLE_EXTRA = {
    "list", "list*", "cons", "quote", "fms", "fms!", "cw", "cw!", "hard-error",
    "er-hard?", "mv-nth", "f-put-global", "f-get-global", "@", "assign",
    "boundp-global", "close-input-channel", "close-output-channel",
    "princ$", "prin1$", "write-byte$", "newline", "fix", "ifix", "rfix",
    "acons", "string-append", "concatenate", "length", "len", "car", "cdr",
    "mbt", "not", "equal", "eq", "eql", "null", "endp", "atom", "binary-+",
    "cadr", "caddr", "cddr", "caar", "cdar", "rest", "first", "second",
    "third", "fourth", "fifth", "nth", "nthcdr", "take", "append", "revappend",
    "reverse", "coerce", "symbol-name", "intern$", "strip-cars", "strip-cdrs",
    "assoc-equal", "assoc", "member-equal", "member", "update-nth", "put-assoc-equal",
    "hons", "hons-copy", "hons-equal", "nfix", "natp", "posp", "zp",
    "integerp", "stringp", "symbolp", "consp", "true-listp", "character-listp",
    "floor", "mod", "expt", "ash", "logand", "logior", "min", "max",
    "+", "-", "*", "/", "<", "<=", ">", ">=", "=", "/=", "1+", "1-",
    "unsigned-byte-p", "signed-byte-p", "char-code", "code-char", "char",
    "subseq", "string", "keywordp", "alistp", "booleanp", "set-difference-equal",
    "union-equal", "intersection-equal", "remove-duplicates-equal",
    "remove-equal", "position-equal", "search", "explode-nonnegative-integer",
    "state-p", "true-list-listp", "last", "butlast", "pairlis$",
    "cadddr", "cddddr", "cdddr", "logbitp", "make-list",
}
# Forms with no shape of their own that this does not descend into.
OPAQUE = {"quote", "declare", "function", "quasiquote"}
DEFINERS = ("defun", "defund", "defun-nx")
TRANSPARENT = {"local", "progn", "with-output", "defsection", "defsection-progn",
               "encapsulate", "mutual-recursion"}

UNKNOWN = None


@dataclass
class Definition:
    name: str
    where: str
    formals: list
    body: object
    host: bool


@dataclass
class Report:
    findings: list = field(default_factory=list)
    counts: dict = field(default_factory=dict)


def definitions_in(form, where: str, host: bool, out: list, *, raw: bool = False) -> None:
    """Every `defun` a top-level form makes, outside raw-mode regions."""
    name = head(form)
    if name is None:
        return
    if name == "progn!":
        # `(progn! (set-raw-mode t) ...)` is raw Common Lisp: ACL2 does not
        # translate it, so nothing in it has an ACL2 shape.
        if any(head(item) == "set-raw-mode" for item in form[1:]):
            return
        for item in form[1:]:
            definitions_in(item, where, host, out)
        return
    if name in TRANSPARENT:
        start = 2 if name in ("encapsulate", "defsection", "with-output") else 1
        if name == "with-output":
            # (with-output :key val ... form)
            start = len(form) - 1
        for item in form[start:]:
            definitions_in(item, where, host, out)
        return
    if name in ("fn-defrecord", "fn-defrecord-export"):
        expansion = (ledger.defrecord_expansion(form) if name == "fn-defrecord"
                     else ledger.defrecord_export_expansion(form))
        for item in expansion:
            definitions_in(item, where, host, out)
        return
    if name in DEFINERS and len(form) >= 4 and isinstance(form[1], Sym):
        out.append(Definition(str(form[1]), where,
                              form[2] if isinstance(form[2], list) else [],
                              form[-1], host))


def raw_files(hosts: dict) -> set[str]:
    """Every file some host file `load`s: `load` exists only in raw mode."""
    found: set[str] = set()
    for relative, host in hosts.items():
        text = (ROOT / relative).read_text(encoding="utf-8") if (ROOT / relative).is_file() else ""
        for reference in re.findall(r'\(load\s+"([^"]+\.lisp)"', text):
            found.add(ledger.resolve(reference))
    return found


class Shapes:
    """Result arity of every definition, to a fixpoint."""

    def __init__(self, definitions: list[Definition], builtins: set[str]):
        self.definitions = {}
        for definition in definitions:
            previous = self.definitions.get(definition.name)
            # A host redefinition replaces the book's, as `ld` order does.
            if previous is None or definition.host or not previous.host:
                self.definitions[definition.name] = definition
        self.builtins = builtins
        self.arity: dict[str, int | None] = {name: UNKNOWN for name in self.definitions}
        changed = True
        while changed:
            changed = False
            for name, definition in self.definitions.items():
                if self.arity[name] is not UNKNOWN:
                    continue
                inferred = self.of(definition.body, frozenset(
                    f for f in definition.formals if isinstance(f, str)))
                if inferred is not UNKNOWN:
                    self.arity[name] = inferred
                    changed = True

    def callee(self, name: str):
        if name in self.definitions:
            return self.arity[name]
        if name in MULTI_BUILTINS:
            return MULTI_BUILTINS[name]
        if name in SINGLE_EXTRA or name in self.builtins:
            return 1
        return UNKNOWN

    def known_head(self, name: str) -> bool:
        return (name in self.definitions or name in MULTI_BUILTINS
                or name in SINGLE_EXTRA or name in self.builtins)

    def first_known(self, forms, bound) -> int | None:
        for form in forms:
            shape = self.of(form, bound)
            if shape is not UNKNOWN:
                return shape
        return UNKNOWN

    def of(self, form, bound=frozenset()):
        """How many values `form` returns, or UNKNOWN."""
        if not isinstance(form, list):
            return 1
        if not form:
            return 1
        name = head(form)
        if name is None:
            return UNKNOWN  # ((lambda ...) ...)
        body = body_of(form)
        if name in ("quote", "function"):
            return 1
        if name == "mv":
            return len(form) - 1
        if name == "er":
            return 1 if len(form) > 1 and form[1] in ("hard", "hard?", "hard!") else 3
        if name in ("if",):
            return self.first_known(form[2:4], bound)
        if name == "cond":
            return self.first_known([clause[-1] for clause in form[1:]
                                     if isinstance(clause, list) and len(clause) > 1], bound)
        if name == "case":
            return self.first_known([clause[-1] for clause in form[2:]
                                     if isinstance(clause, list) and len(clause) > 1], bound)
        if name in ("and", "or", "mv-list"):
            return 1
        if name in ("let", "let*", "mv-let", "mv?-let", "prog2$", "progn$",
                    "pprogn", "the", "ec-call", "assert$", "state-global-let*",
                    "with-output", "time$"):
            return self.of(body, bound) if body is not None else UNKNOWN
        if name == "mbe":
            options = ledger.keyword_plist(form[1:])
            return self.of(options.get(":exec"), bound) if ":exec" in options else UNKNOWN
        return self.callee(name)


def body_of(form: list):
    """The value-producing last subform of a binder or sequencer."""
    name = head(form)
    if name in ("let", "let*", "state-global-let*", "er-let*"):
        return form[-1] if len(form) >= 3 else None
    if name in ("mv-let", "mv?-let"):
        return form[-1] if len(form) >= 4 else None
    if name in ("prog2$", "progn$", "pprogn", "assert$", "time$"):
        return form[-1] if len(form) >= 2 else None
    if name == "the":
        return form[2] if len(form) >= 3 else None
    if name == "ec-call":
        return form[1] if len(form) >= 2 else None
    if name == "with-output":
        return form[-1] if len(form) >= 2 else None
    return None


def describe(n) -> str:
    if n == 1:
        return "one value"
    if n == 3:
        return "an error triple (3 values)"
    return "{} values".format(n)


class Checker:
    def __init__(self, shapes: Shapes, where: str, definition: str):
        self.shapes = shapes
        self.where = where
        self.definition = definition
        self.findings: list[dict] = []
        self.counts = {"positions": 0, "undecidable": 0, "multi_calls": 0}

    def finding(self, form, problem: str) -> None:
        self.findings.append({
            "lint": "host-shape", "where": self.where,
            "definition": self.definition,
            "callee": head(form) or "",
            "form": render(form),
            "problem": problem,
        })

    def expect(self, form, required, context: str) -> None:
        """Check `form` where `required` values are needed (None: any shape)."""
        self.walk(form)
        if required is None:
            return
        if not isinstance(form, list) or not form:
            return
        self.counts["positions"] += 1
        name = head(form)
        shape = self.shapes.of(form)
        if shape is UNKNOWN:
            # An unmodelled head, a definition with no inferred shape, or a
            # conditional whose every arm is one of those.
            self.counts["undecidable"] += 1
            return
        if shape != 1:
            self.counts["multi_calls"] += 1
        if shape != required:
            self.finding(form, "returns {} where {} requires {}".format(
                describe(shape), context, describe(required)))

    def arms(self, forms: list, context: str) -> None:
        """Every arm of a conditional must return the same number of values."""
        for arm in forms:
            self.expect(arm, None, context)
        known = [(arm, self.shapes.of(arm)) for arm in forms]
        known = [(arm, shape) for arm, shape in known if shape is not UNKNOWN]
        if len({shape for _, shape in known}) > 1:
            first = known[0][1]
            for arm, shape in known[1:]:
                if shape != first:
                    self.finding(arm, "{} arm returns {} and an earlier arm returns {}"
                                 .format(context, describe(shape), describe(first)))
                    break

    def walk(self, form) -> None:
        """Check every position inside `form` (not `form`'s own shape)."""
        if not isinstance(form, list) or not form:
            return
        name = head(form)
        if name is None:
            self.counts["undecidable"] += 1
            for item in form:
                self.walk(item)
            return
        if name in OPAQUE:
            return
        if name == "if":
            if len(form) >= 2:
                self.expect(form[1], 1, "an `if` test")
            self.arms(form[2:4], "`if`")
            return
        if name == "cond":
            bodies = []
            for clause in form[1:]:
                if isinstance(clause, list) and clause:
                    self.expect(clause[0], 1, "a `cond` test")
                    for item in clause[1:-1]:
                        self.expect(item, None, "")
                    if len(clause) > 1:
                        bodies.append(clause[-1])
            self.arms(bodies, "`cond`")
            return
        if name == "case":
            if len(form) >= 2:
                self.expect(form[1], 1, "a `case` key")
            self.arms([clause[-1] for clause in form[2:]
                       if isinstance(clause, list) and len(clause) > 1], "`case`")
            return
        if name in ("let", "let*", "state-global-let*"):
            if len(form) >= 2 and isinstance(form[1], list):
                for binding in form[1]:
                    if isinstance(binding, list) and len(binding) >= 2:
                        self.expect(binding[1], 1, "a `{}` binding".format(name))
            for item in form[2:]:
                self.expect(item, None, "")
            return
        if name in ("mv-let", "mv?-let"):
            if len(form) >= 3:
                count = len(form[1]) if isinstance(form[1], list) else None
                self.expect(form[2], count if name == "mv-let" else None,
                            "an `mv-let` of {} variables".format(count))
            for item in form[3:]:
                self.expect(item, None, "")
            return
        if name == "mv-list":
            if len(form) >= 3 and isinstance(form[1], int):
                self.expect(form[2], form[1], "`mv-list {}`".format(form[1]))
            return
        if name == "er-let*":
            if len(form) >= 2 and isinstance(form[1], list):
                for binding in form[1]:
                    if isinstance(binding, list) and len(binding) >= 2:
                        self.expect(binding[-1], 3, "an `er-let*` binding")
            for item in form[2:-1]:
                self.expect(item, None, "")
            if len(form) >= 3:
                self.expect(form[-1], 3, "the body of `er-let*`")
            return
        if name == "er-progn":
            for item in form[1:]:
                self.expect(item, 3, "an `er-progn` form")
            return
        if name == "pprogn":
            for item in form[1:-1]:
                self.expect(item, 1, "a non-final `pprogn` form")
            if len(form) >= 2:
                self.expect(form[-1], None, "")
            return
        if name in ("prog2$", "progn$", "assert$", "time$"):
            for item in form[1:-1]:
                self.expect(item, 1, "a non-final `{}` form".format(name))
            if len(form) >= 2:
                self.expect(form[-1], None, "")
            return
        if name in ("the", "ec-call", "with-output"):
            body = body_of(form)
            if body is not None:
                self.expect(body, None, "")
            return
        if name == "mbe":
            options = ledger.keyword_plist(form[1:])
            for key in (":logic", ":exec"):
                if key in options:
                    self.expect(options[key], None, "")
            return
        if name == "er":
            # (er soft ctx "fmt" args...): the format arguments are single.
            for item in form[4:]:
                self.expect(item, 1, "an `er` format argument")
            return
        if name == "mv":
            for item in form[1:]:
                self.expect(item, 1, "an `mv` argument")
            return
        if name == "value":
            for item in form[1:]:
                self.expect(item, 1, "a `value` argument")
            return
        if name in ("and", "or"):
            for item in form[1:]:
                self.expect(item, 1, "an `{}` argument".format(name))
            return
        if self.shapes.known_head(name):
            # A function call: every argument is one value.
            for item in form[1:]:
                self.expect(item, 1, "an argument of `{}`".format(name))
            return
        # A macro or name this does not model: nothing is required of its
        # arguments, but the forms inside them are still walked.
        self.counts["undecidable"] += 1
        for item in form[1:]:
            self.expect(item, None, "")


MODELLED = {"if", "cond", "case", "and", "or", "let", "let*", "mv-let", "mv?-let",
            "mv", "mv-list", "value", "er", "er-progn", "er-let*", "pprogn",
            "prog2$", "progn$", "the", "mbe", "ec-call", "assert$",
            "state-global-let*", "with-output", "time$"}


def render(form, limit: int = 100) -> str:
    def text(item) -> str:
        if isinstance(item, list):
            return "(" + " ".join(text(x) for x in item) + ")"
        if isinstance(item, Sym):
            return str(item)
        if isinstance(item, str):
            return json.dumps(item)
        return str(item)
    rendered = text(form)
    return rendered if len(rendered) <= limit else rendered[:limit - 3] + "..."


@functools.lru_cache(maxsize=1)
def book_definitions() -> tuple[Definition, ...]:
    """Every `defun` in `books/`, which the host files include."""
    definitions: list[Definition] = []
    for path, relative in ledger.book_paths():
        if not relative.startswith("books/"):
            continue
        try:
            forms = ledger.Reader(path.read_text(encoding="utf-8")).top_level()
        except ledger.ReadError:
            continue
        for form, line in forms:
            definitions_in(form, "{}:{}".format(relative, line), False, definitions)
    return tuple(definitions)


def analyze(overrides: dict[str, str] | None = None) -> Report:
    """Findings over the tree, with `overrides` replacing some host files' text."""
    overrides = overrides or {}
    hosts = {relative: host for relative, host in ledger.load_hosts().items()}
    host_forms: dict[str, list] = {}
    for relative, host in hosts.items():
        if relative in overrides:
            host_forms[relative] = ledger.Reader(overrides[relative]).top_level()
        else:
            host_forms[relative] = host.forms
    for relative, text in overrides.items():
        if relative not in host_forms:
            host_forms[relative] = ledger.Reader(text).top_level()
    raw = raw_files(hosts)
    definitions = list(book_definitions())
    checked_files = sorted(relative for relative in host_forms if relative not in raw)
    host_definitions: list[Definition] = []
    for relative in checked_files:
        for form, line in host_forms[relative]:
            definitions_in(form, "{}:{}".format(relative, line), True, host_definitions)
    shapes = Shapes(definitions + host_definitions, ledger.acl2_builtins())
    report = Report()
    counts = {"host_files": len(checked_files), "raw_files_not_checked": len(raw),
              "definitions": len(shapes.definitions),
              "host_definitions": len(host_definitions),
              "multi_valued_definitions": sum(1 for n in shapes.arity.values()
                                              if n is not UNKNOWN and n != 1),
              "definitions_without_shape": sum(1 for n in shapes.arity.values()
                                               if n is UNKNOWN),
              "positions": 0, "multi_calls": 0, "undecidable": 0}
    for definition in host_definitions:
        checker = Checker(shapes, definition.where, definition.name)
        checker.expect(definition.body, None, "")
        report.findings.extend(checker.findings)
        for key in ("positions", "multi_calls", "undecidable"):
            counts[key] += checker.counts[key]
    report.findings.sort(key=lambda row: (row["where"], row["form"]))
    report.counts = counts
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", default=None)
    parser.add_argument("--report", action="store_true", help="print and always exit 0")
    args = parser.parse_args(argv)
    report = analyze()
    print("host_shape_check: {} finding{} ({})".format(
        len(report.findings), "" if len(report.findings) == 1 else "s",
        ", ".join("{} {}".format(value, key) for key, value in report.counts.items())))
    for finding in report.findings:
        print("  {} {}: {}\n      {}".format(finding["where"], finding["definition"],
                                             finding["problem"], finding["form"]))
    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(
            {"schema": 1, "findings": report.findings, "counts": report.counts},
            indent=2, sort_keys=True) + "\n")
    return 1 if report.findings and not args.report else 0


if __name__ == "__main__":
    sys.exit(main())
