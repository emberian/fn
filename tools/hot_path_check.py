#!/usr/bin/env python3
"""The hot-path check: which host entries walk retained state (PKT-334).

gpt-6's answers of 2026-09-26, section 2: "A function invoked once per request
or arrival traverses a collection whose size is independent of that request."
This tool looks for that pattern statically.  It seeds the functions whose value
is a list that grows with retained state (tools/hot_path_dimensions.json:
N retained Store history, F held BP fragments, J queued BP jobs).  It follows
each seeded value from every host entry down the path ACL2 executes, and reports
each traversal of that value.

What "the executed path" means here:

  * A guard-verified book function runs its raw Lisp body, so an `mbe` there
    runs its `:exec` branch and `mbt` is `t`.  A function whose guards are not
    verified runs its executable counterpart (`*1*`).  There `mbe` runs its
    `:logic` branch, `mbt` is evaluated, and the guard of every function it
    calls is evaluated, so a guard that recognises the whole history is a
    walk.  The saved image runs with guard-checking t (host/native/io.lisp
    asserts it).
  * A host function is an entry.  Native host code calls a book function
    through a dispatcher (`(fnn-core 'fn-x a b)`), which calls the executable
    counterpart and so evaluates fn-x's guard.  An ACL2 host file is
    `:program` mode, so every call it makes evaluates the callee's guard.
  * A constrained function runs its `defattach` (edges from
    reach_check.attachments).  A constrained function with no attachment, or
    a `funcall` of a variable, receiving a seeded value is an UNRESOLVED edge.
    These edges are counted and named, never dropped.

A traversal is a walking primitive applied to a seeded value: len, nthcdr,
nth, member/assoc/position, append, reverse, revappend, remove, take, dolist,
loop, mapcar, list conversions (coerce, fnn-octets).  A recursive call on a
shrinking seeded formal also counts, which covers recognisers, encoders and
replay folds.  Each find is classified:

  cold            every host entry that reaches it runs at open, recovery,
                  checkpoint, install, pack or compaction (the name rule in
                  the dimensions file);
  resumable       the dimensions file names the work quantum that bounds it;
  output-proportional
                  the walked value grows only in K;
  unexpected      retained-state work on a served entry;
  unresolved      an edge the tool cannot follow, as above.

planning/hot-path-findings.json lists every find with its owning packet, or
`open`.  No baseline hides a find: `--strict` fails on an unexpected find that
the list does not name (a NEW find), and on a listed find that no longer
occurs (STALE).  A silent report is not a proof.  The analysis is
context-insensitive (a formal carries every dimension any caller passes it),
does not expand macros, and treats `equal` as constant time, which structure
sharing usually makes true.  The record lists what it cannot follow.

Run: python3 tools/hot_path_check.py [--report | --summary] [--strict] [--json FILE]
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _load(name: str):
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, ROOT / "tools" / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


session_depth = _load("session_depth")
# session_depth executes its own copy of ledger; its Reader makes that copy's
# symbols, so every shape test here must use the same module.
ledger = session_depth._ledger
reach_check = _load("reach_check")

Sym = ledger.Sym
head = ledger.head
E: frozenset = frozenset()
DIMENSIONS = ("N", "F", "J", "K", "B")
CLASSES = ("unexpected", "cold", "resumable", "output-proportional", "unresolved",
           "uncalled")

# ---------------------------------------------------------------------------
# The primitives
# ---------------------------------------------------------------------------

ALL = "all"
ALL_BUT_LAST = "all-but-last"
# name -> the argument positions it walks.
WALKS = {
    "len": [0], "length": [0], "nthcdr": [1], "nth": [1], "take": [1],
    "first-n-ac": [1], "butlast": [0], "last": [0], "car-last": [0],
    "member": [1], "member-equal": [1], "member-eq": [1], "memq": [1],
    "assoc": [1], "assoc-equal": [1], "assoc-eq": [1], "assoc-string-equal": [1],
    "rassoc": [1], "rassoc-equal": [1], "rassoc-eq": [1],
    "position": [1], "position-equal": [1], "position-eq": [1],
    "append": ALL_BUT_LAST, "binary-append": [0], "revappend": [0], "reverse": [0],
    "true-listp": [0], "list-fix": [0], "true-list-fix": [0],
    "remove": [1], "remove-equal": [1], "remove-eq": [1],
    "remove-duplicates": [0], "remove-duplicates-equal": [0],
    "remove-duplicates-eq": [0],
    "no-duplicatesp": [0], "no-duplicatesp-equal": [0], "no-duplicatesp-eq": [0],
    "subsetp": [0, 1], "subsetp-equal": [0, 1], "subsetp-eq": [0, 1],
    "intersection-equal": [0, 1], "intersection-eq": [0, 1], "intersection$": ALL,
    "union-equal": [0], "union-eq": [0], "union$": ALL_BUT_LAST,
    "set-difference-equal": [0, 1], "set-difference-eq": [0, 1],
    "set-difference$": [0, 1],
    "strip-cars": [0], "strip-cdrs": [0], "pairlis$": [0, 1],
    "coerce": [0], "string-append-lst": [0], "fnn-octets": [0],
    "mapcar": ALL, "mapc": ALL, "mapcan": ALL, "maplist": ALL, "reduce": [1],
    "find": [1], "find-if": [1], "find-if-not": [1], "position-if": [1],
    "count": [1], "count-if": [1], "remove-if": [1], "remove-if-not": [1],
    "every": ALL, "some": ALL, "notany": ALL,
    "sort": [0], "stable-sort": [0], "copy-list": [0],
}
# name -> the argument positions whose list the result shares or copies.
KEEPS = {
    "cdr": [0], "cddr": [0], "cdddr": [0], "cddddr": [0], "rest": [0],
    "nthcdr": [1], "take": [1], "first-n-ac": [1], "butlast": [0],
    "append": ALL, "binary-append": ALL, "revappend": ALL, "reverse": [0],
    "cons": [1], "list-fix": [0], "true-list-fix": [0],
    "remove": [1], "remove-equal": [1], "remove-eq": [1],
    "remove-duplicates": [0], "remove-duplicates-equal": [0],
    "remove-duplicates-eq": [0], "union-equal": ALL, "union-eq": ALL,
    "set-difference-equal": [0], "set-difference-eq": [0], "set-difference$": [0],
    "remove-if": [1], "remove-if-not": [1], "sort": [0], "stable-sort": [0],
    "copy-list": [0], "the": [1],
}
SEQUENCE = {"progn", "progn$", "prog2$", "pprogn", "time$", "return-last",
            "check-vars-not-free", "with-guard-checking", "unwind-protect",
            "ignore-errors", "locally", "block", "tagbody", "with-output",
            "er-progn", "state-global-let*"}
TRANSPARENT = {"local", "progn", "with-output", "defsection", "defsection-progn",
               "mutual-recursion", "eval-when", "when", "unless", "progn!"}
DEFINERS = {"defun", "defund", "defun-nx", "defun-inline", "defund-inline"}
SUPPRESSING = ledger.SUPPRESSING
LAMBDA_KEYWORDS = {"&optional", "&rest", "&key", "&aux", "&body", "&allow-other-keys",
                   "&whole", "&environment"}


# ---------------------------------------------------------------------------
# Reading (ledger's reader, through session_depth's line-keeping subclass)
# ---------------------------------------------------------------------------


@dataclass
class Definition:
    name: str
    file: str
    line: int
    formals: list[str]
    body: object
    guard: object
    host: bool
    native: bool
    verified: bool

    @property
    def where(self) -> str:
        return f"{self.file}:{self.line}"


@dataclass
class Tree:
    definitions: dict[str, Definition] = field(default_factory=dict)
    lines: dict[int, int] = field(default_factory=dict)
    constrained: dict[str, str] = field(default_factory=dict)
    attachments: dict[str, set[str]] = field(default_factory=dict)
    read_errors: list[str] = field(default_factory=list)


def formal_names(formals: object) -> list[str]:
    out: list[str] = []
    if not isinstance(formals, list):
        return out
    for item in formals:
        if isinstance(item, Sym):
            if str(item) not in LAMBDA_KEYWORDS:
                out.append(str(item))
        elif isinstance(item, list) and item and isinstance(item[0], Sym):
            out.append(str(item[0]))
    return out


def guard_of(rest: list) -> object:
    """The conjunction of a definition's `:guard` declarations, or None."""
    guards = []
    for item in rest:
        if head(item) != "declare":
            continue
        for declaration in item[1:]:
            if head(declaration) == "xargs":
                options = ledger.keyword_plist(declaration[1:])
                if ":guard" in options:
                    guards.append(options[":guard"])
    guards = [g for g in guards if not (isinstance(g, Sym) and str(g) == "t")]
    if not guards:
        return None
    return guards[0] if len(guards) == 1 else [Sym("and")] + guards


class FileScan:
    """The definitions one file makes, with its verification state."""

    def __init__(self, relative: str, host: bool, native: bool, tree: Tree) -> None:
        self.relative, self.host, self.native, self.tree = relative, host, native, tree
        self.eager = True
        self.verified_events: set[str] = set()
        self.found: list[tuple[Definition, str | None, bool, bool]] = []

    def scan(self, forms) -> None:
        for form, line in forms:
            self.record(form, line, in_encapsulate=False, local=False)
        for definition, setting, has_guard, program in self.found:
            if self.host or program:
                definition.verified = False
            elif definition.name in self.verified_events or setting == "t":
                definition.verified = True
            elif setting == "nil":
                definition.verified = False
            else:
                definition.verified = has_guard and self.eager
            self.tree.definitions.setdefault(definition.name, definition)

    def record(self, form, line: int, *, in_encapsulate: bool, local: bool) -> None:
        name = head(form)
        if name is None:
            return
        if name == "progn!" and self.native is False and any(
                head(item) == "set-raw-mode" for item in form[1:]):
            pass  # raw regions still define functions; read them like the rest
        if name in TRANSPARENT:
            for item in form[1:]:
                self.record(item, line, in_encapsulate=in_encapsulate,
                            local=local or name == "local")
            return
        if name == "encapsulate":
            if len(form) >= 2:
                for constrained in ledger.encapsulated_names(form[1]):
                    self.tree.constrained.setdefault(constrained, self.relative)
            for item in form[2:]:
                self.record(item, line, in_encapsulate=True, local=local)
            return
        if name in SUPPRESSING or name == "make-event":
            return
        if name == "set-verify-guards-eagerness" and len(form) == 2:
            self.eager = form[1] != 0
            return
        if name == "verify-guards" and len(form) >= 2 and isinstance(form[1], Sym):
            self.verified_events.add(str(form[1]))
            return
        if name in ("fn-defrecord", "fn-defrecord-export"):
            expansion = (ledger.defrecord_expansion(form) if name == "fn-defrecord"
                         else ledger.defrecord_export_expansion(form))
            for item in expansion:
                self.record(item, line, in_encapsulate=in_encapsulate, local=local)
            return
        if name in DEFINERS and len(form) >= 4 and isinstance(form[1], Sym):
            if in_encapsulate and local:
                return  # a witness, not what runs
            rest = list(form[3:])
            has_guard, setting = ledger.declared(rest)
            definition = Definition(
                name=str(form[1]), file=self.relative,
                line=self.tree.lines.get(id(form), line),
                formals=formal_names(form[2]), body=form[-1],
                guard=None if self.host else guard_of(rest),
                host=self.host, native=self.native, verified=False)
            if self.host and len(rest) > 1:
                # Common Lisp bodies are implicit progns.
                definition.body = [Sym("progn")] + [item for item in rest
                                                    if head(item) != "declare"
                                                    and not isinstance(item, str)]
            self.found.append((definition, setting, has_guard,
                               ledger.program_mode(rest)))


def read_tree(root: Path = ROOT) -> Tree:
    tree = Tree()
    paths: list[tuple[Path, str, bool, bool]] = []
    for path in sorted((root / "books").glob("*.lisp")):
        paths.append((path, path.relative_to(root).as_posix(), False, False))
    for directory, native in (("host", False), ("host/native", True)):
        for path in sorted((root / directory).glob("*.lisp")):
            paths.append((path, path.relative_to(root).as_posix(), True, native))
    for path, relative, host, native in paths:
        reader = session_depth.Reader(path.read_text(encoding="utf-8"))
        try:
            forms = reader.top_level()
        except ledger.ReadError as exc:
            tree.read_errors.append(f"{relative}: {exc}")
            continue
        tree.lines.update(reader.lines)
        FileScan(relative, host, native, tree).scan(forms)
    tree.attachments = dict(reach_check.attachments(
        sorted((root / "books").glob("*.lisp"))))
    return tree


# ---------------------------------------------------------------------------
# Phase A: a parametric summary of every definition
# ---------------------------------------------------------------------------
#
# A label is a frozenset of dimension letters and formal markers "#i" (the
# value derives from formal i).  A value is a tuple of labels, one per `mv`
# position.


def one(value: tuple) -> frozenset:
    out: frozenset = E
    for item in value:
        out |= item
    return out


def instantiate(label: frozenset, arguments: tuple) -> frozenset:
    out = set()
    for item in label:
        if item.startswith("#"):
            index = int(item[1:])
            if index < len(arguments):
                out |= arguments[index]
        else:
            out.add(item)
    return frozenset(out)


@dataclass
class Summary:
    ret: tuple = (E,)
    sites: list = field(default_factory=list)       # (primitive, line, label)
    calls: list = field(default_factory=list)       # (callee, line, args, kind)
    unresolved: list = field(default_factory=list)  # (what, line, label)


GUARD = "#guard"
STAR = "*1*"


def base_name(node: str) -> str:
    return node[:-len(STAR)] if node.endswith(STAR) else node


class Summarizer:
    def __init__(self, tree: Tree, seeds: dict[str, str], dispatchers: set[str],
                 formal_seeds: dict | None = None, cuts: dict | None = None) -> None:
        self.tree, self.seeds, self.dispatchers = tree, seeds, dispatchers
        self.cuts = {name: reason for name, reason in (cuts or {}).items()
                     if name != "note"}
        self.formal_seeds = {name: spec for name, spec in (formal_seeds or {}).items()
                             if isinstance(spec, dict)}
        self.definitions: dict[str, Definition] = dict(tree.definitions)
        for definition in tree.definitions.values():
            if definition.guard is not None:
                self.definitions[definition.name + GUARD] = Definition(
                    name=definition.name + GUARD, file=definition.file,
                    line=definition.line, formals=definition.formals,
                    body=definition.guard, guard=None, host=False, native=False,
                    verified=definition.verified)
        self.rets: dict[str, tuple] = {}
        self.summaries: dict[str, Summary] = {}

    def node(self, name: str, star: bool) -> str:
        """The graph node that runs `name` in the given context.

        Raw Lisp runs a function's raw body whatever its verification state;
        an executable counterpart runs the raw body only once the function's
        guards are verified, and otherwise its own *1* body."""
        definition = self.definitions[name]
        if star and not definition.verified and not definition.host:
            return name + STAR
        return name

    def run(self) -> None:
        callers: dict[str, set[str]] = collections.defaultdict(set)
        work = collections.deque(self.definitions)
        queued = set(work)
        pending_star: set[str] = set()
        rounds = 0
        while work:
            name = work.popleft()
            queued.discard(name)
            rounds += 1
            summary = self.summarize(name)
            self.summaries[name] = summary
            for callee, _line, _args, _kind in summary.calls:
                callers[callee].add(name)
                if callee not in self.summaries and callee not in queued:
                    queued.add(callee)
                    work.append(callee)
            if summary.ret != self.rets.get(name, (E,)):
                self.rets[name] = summary.ret
                for caller in callers[name]:
                    if caller not in queued:
                        queued.add(caller)
                        work.append(caller)
            if rounds > 40 * len(self.definitions):  # pragma: no cover - monotone
                raise RuntimeError("hot_path_check: summaries did not converge")

    def summarize(self, node: str) -> Summary:
        definition = self.definitions[base_name(node)]
        if base_name(node) in self.cuts:
            return Summary()
        walker = Walker(self, definition, star=node.endswith(STAR))
        env = {formal: frozenset({f"#{index}"})
               for index, formal in enumerate(definition.formals)}
        for formal, dimension in self.formal_seeds.get(definition.name, {}).items():
            if formal in env:
                env[formal] = env[formal] | {dimension}
        summary = walker.summary
        summary.ret = tuple(item for item in walker.ev(definition.body, env))
        return summary


class Walker:
    """One definition's executed body, evaluated over labels."""

    def __init__(self, summarizer: Summarizer, definition: Definition,
                 star: bool = False) -> None:
        self.s = summarizer
        self.d = definition
        self.summary = Summary()
        # raw: raw Lisp (a verified body, or anything beneath a :program host
        # wrapper: ACL2 runs a program-mode function raw once its own guard
        # holds, specs/host.md "The decimal-octet pipe"); mbe's :exec, no
        # callee guards.  star: the *1* body of a function whose guards are
        # not verified, entered from a counterpart call: mbe's :logic, and
        # every callee's guard evaluated.  native: host/native raw Lisp,
        # whose dispatchers (fnn-core 'f ...) call f's counterpart.
        if definition.native:
            self.mode = "native"
        elif star:
            self.mode = "star"
        else:
            self.mode = "raw"
        self.local_functions: set[str] = set()

    def line(self, form) -> int:
        return self.s.tree.lines.get(id(form), self.d.line)

    def site(self, primitive: str, form, label: frozenset) -> None:
        if label:
            self.summary.sites.append((primitive, self.line(form), label))

    def body(self, forms, env) -> tuple:
        value: tuple = (E,)
        for item in forms:
            if head(item) == "declare" or isinstance(item, str):
                continue
            value = self.ev(item, env)
        return value

    def ev(self, form, env: dict) -> tuple:
        if isinstance(form, Sym):
            return (env.get(str(form), E),)
        if not isinstance(form, list) or not form:
            return (E,)
        name = head(form)
        if name is None:
            first = form[0]
            if head(first) == "lambda" and len(first) >= 3:
                arguments = [one(self.ev(item, env)) for item in form[1:]]
                inner = dict(env)
                for formal, label in zip(formal_names(first[1]), arguments):
                    inner[formal] = label
                return self.body(first[2:], inner)
            for item in form:
                self.ev(item, env)
            return (E,)
        return self.special(name, form, env)

    # -- special forms ---------------------------------------------------

    def special(self, name: str, form: list, env: dict) -> tuple:
        rest = form[1:]
        if name in ("quote", "quasiquote", "function", "declare", "go"):
            return (E,)
        if name == "if":
            if rest:
                self.ev(rest[0], env)
            return merge([self.ev(item, env) for item in rest[1:3]] or [(E,)])
        if name in ("when", "unless"):
            if rest:
                self.ev(rest[0], env)
            return self.body(rest[1:], env)
        if name == "cond":
            values = []
            for clause in rest:
                if isinstance(clause, list) and clause:
                    test = self.ev(clause[0], env)
                    values.append(self.body(clause[1:], env) if len(clause) > 1 else test)
            return merge(values or [(E,)])
        if name in ("case", "ecase", "ccase", "typecase", "etypecase"):
            if rest:
                self.ev(rest[0], env)
            values = [self.body(clause[1:], env) for clause in rest[1:]
                      if isinstance(clause, list) and clause]
            return merge(values or [(E,)])
        if name in ("and", "or"):
            values = [self.ev(item, env) for item in rest]
            if not values:
                return (E,)
            return values[-1] if name == "and" else merge(values)
        if name in ("let", "let*"):
            inner = dict(env)
            bindings = rest[0] if rest and isinstance(rest[0], list) else []
            for binding in bindings:
                if isinstance(binding, list) and binding and isinstance(binding[0], Sym):
                    scope = inner if name == "let*" else env
                    label = one(self.ev(binding[1], scope)) if len(binding) > 1 else E
                    inner[str(binding[0])] = label
                elif isinstance(binding, Sym):
                    inner[str(binding)] = E
            return self.body(rest[1:], inner)
        if name in ("mv-let", "mv?-let", "multiple-value-bind"):
            if len(rest) < 2:
                return (E,)
            value = self.ev(rest[1], env)
            inner = dict(env)
            names = formal_names(rest[0])
            for index, variable in enumerate(names):
                if len(value) == 1:
                    inner[variable] = value[0]
                else:
                    inner[variable] = value[index] if index < len(value) else E
            return self.body(rest[2:], inner)
        if name == "destructuring-bind":
            if len(rest) < 2:
                return (E,)
            label = one(self.ev(rest[1], env))
            inner = dict(env)
            pattern = rest[0] if isinstance(rest[0], list) else []
            after_rest = False
            for item in pattern:
                if isinstance(item, Sym) and str(item) in ("&rest", "&body"):
                    after_rest = True
                    continue
                for variable in formal_names([item]):
                    inner[variable] = label if after_rest else E
            return self.body(rest[2:], inner)
        if name in ("flet", "labels", "macrolet"):
            bindings = rest[0] if rest and isinstance(rest[0], list) else []
            for binding in bindings:
                if isinstance(binding, list) and binding and isinstance(binding[0], Sym):
                    self.local_functions.add(str(binding[0]))
                    inner = dict(env)
                    for formal in formal_names(binding[1] if len(binding) > 1 else []):
                        inner[formal] = E
                    self.body(binding[2:], inner)
            return self.body(rest[1:], env)
        if name == "lambda":
            inner = dict(env)
            for formal in formal_names(rest[0] if rest else []):
                inner[formal] = E
            self.body(rest[1:], inner)
            return (E,)
        if name == "dolist":
            spec = rest[0] if rest and isinstance(rest[0], list) else []
            inner = dict(env)
            if len(spec) >= 2:
                self.site("dolist", form, one(self.ev(spec[1], env)))
                if isinstance(spec[0], Sym):
                    inner[str(spec[0])] = E
            self.body(rest[1:], inner)
            return (E,)
        if name == "loop":
            for index, item in enumerate(rest):
                if (isinstance(item, Sym) and str(item) in ("in", "on", "across")
                        and index + 1 < len(rest)):
                    self.site("loop", form, one(self.ev(rest[index + 1], env)))
                elif isinstance(item, list):
                    self.ev(item, env)
            return (E,)
        if name in ("setq", "setf"):
            for index in range(0, len(rest) - 1, 2):
                label = one(self.ev(rest[index + 1], env))
                if isinstance(rest[index], Sym):
                    key = str(rest[index])
                    env[key] = env.get(key, E) | label
            return (E,)
        if name == "mbe":
            options = ledger.keyword_plist(rest)
            branch = options.get(":exec" if self.mode == "raw" else ":logic")
            return self.ev(branch, env) if branch is not None else (E,)
        if name == "mbt":
            return (E,) if self.mode == "raw" else self.ev(rest[0] if rest else None, env)
        if name == "ec-call":
            inner = rest[0] if rest else None
            if isinstance(inner, list) and head(inner):
                return self.call(head(inner), inner, env, star=True)
            return (E,)
        if name in ("mv", "values"):
            return tuple(one(self.ev(item, env)) for item in rest) or (E,)
        if name == "mv-nth":
            if len(rest) == 2 and isinstance(rest[0], int):
                value = self.ev(rest[1], env)
                return (value[rest[0]] if rest[0] < len(value) else E,)
            return (one(merge([self.ev(item, env) for item in rest])),)
        if name in ("mv-list", "multiple-value-list"):
            return (one(self.ev(rest[-1], env)) if rest else E,)
        if name == "prog1":
            values = [self.ev(item, env) for item in rest]
            return values[0] if values else (E,)
        if name == "the":
            return self.ev(rest[1], env) if len(rest) >= 2 else (E,)
        if name in ("handler-case", "handler-bind", "restart-case"):
            value = self.ev(rest[0], env) if rest else (E,)
            for clause in rest[1:]:
                if isinstance(clause, list):
                    self.body(clause[2:], dict(env))
            return value
        if name == "catch":
            return self.body(rest[1:], env)
        if name in SEQUENCE:
            return self.body(rest, env)
        if name in self.s.dispatchers and rest and head(rest[0]) == "quote" \
                and len(rest[0]) == 2 and isinstance(rest[0][1], Sym):
            target = str(rest[0][1])
            return self.call(target, [Sym(target)] + rest[1:], env, star=True,
                             kind="dispatch", at=form)
        if name in ("funcall", "apply"):
            target = rest[0] if rest else None
            if head(target) in ("function", "quote") and len(target) == 2 \
                    and isinstance(target[1], Sym):
                callee = str(target[1])
                if callee in self.s.dispatchers and len(rest) >= 2 \
                        and head(rest[1]) == "quote" and isinstance(rest[1][1], Sym):
                    real = str(rest[1][1])
                    return self.call(real, [Sym(real)] + rest[2:], env, star=True,
                                     kind="dispatch", at=form)
                if callee not in self.s.dispatchers:
                    return self.call(callee, [Sym(callee)] + rest[1:], env,
                                     star=self.mode == "star", at=form)
            labels = [one(self.ev(item, env)) for item in rest]
            carried = frozenset().union(*labels) if labels else E
            what = f"{name} of {render(target)}"
            self.summary.unresolved.append((what, self.line(form), carried))
            return (E,)
        return self.call(name, form, env, star=self.mode == "star")

    # -- calls -------------------------------------------------------------

    def call(self, name: str, form: list, env: dict, *, star: bool,
             kind: str = "call", at=None) -> tuple:
        at = form if at is None else at
        arguments = tuple(one(self.ev(item, env)) for item in form[1:])
        if name in WALKS:
            positions = WALKS[name]
            if positions == ALL:
                positions = range(len(arguments))
            elif positions == ALL_BUT_LAST:
                positions = range(max(len(arguments) - 1, 0))
            for position in positions:
                if position < len(arguments):
                    self.site(name, at, arguments[position])
        if name in KEEPS:
            positions = KEEPS[name]
            if positions == ALL:
                positions = range(len(arguments))
            return (frozenset().union(*(arguments[p] for p in positions
                                        if p < len(arguments))),)
        if name in WALKS:
            return (E,)
        definitions = self.s.definitions
        if name in self.local_functions:
            return (E,)
        if name in self.s.seeds:
            self.summary.calls.append((name, self.line(at), arguments, kind))
            return (frozenset({self.s.seeds[name]}),)
        if name == self.d.name:
            for index, argument in enumerate(form[1:]):
                marker = f"#{index}"
                label = arguments[index] if index < len(arguments) else E
                if marker in label and not (isinstance(argument, Sym)
                                            and index < len(self.d.formals)
                                            and str(argument) == self.d.formals[index]):
                    self.site("recursion", at, frozenset({marker}))
        targets = []
        if name in definitions:
            targets.append((name, kind))
        for impl in sorted(self.s.tree.attachments.get(name, ())):
            if impl in definitions:
                targets.append((impl, "attachment"))
        if not targets:
            if name in self.s.tree.constrained:
                carried = frozenset().union(*arguments) if arguments else E
                self.summary.unresolved.append(
                    (f"constrained {name} has no attachment", self.line(at), carried))
            return (E,)
        value: tuple = (E,)
        for target, edge in targets:
            self.summary.calls.append((target, self.line(at), arguments, edge))
            node = self.s.node(target, star)
            self.summary.calls[-1] = (node, self.line(at), arguments, edge)
            if star and target + GUARD in definitions:
                self.summary.calls.append((self.s.node(target + GUARD, star),
                                           self.line(at), arguments, "guard"))
            ret = self.s.rets.get(node, (E,))
            value = merge([value, tuple(instantiate(label, arguments) for label in ret)])
        return value


def merge(values: list) -> tuple:
    width = max(len(value) for value in values)
    out = []
    for index in range(width):
        label: frozenset = E
        for value in values:
            if len(value) == 1 and width > 1:
                label |= value[0]
            elif index < len(value):
                label |= value[index]
        out.append(label)
    return tuple(out)


def render(form, limit: int = 60) -> str:
    if isinstance(form, list):
        text = "(" + " ".join(render(item, limit) for item in form) + ")"
    elif isinstance(form, str) and not isinstance(form, Sym):
        text = json.dumps(form)
    else:
        text = str(form)
    return text if len(text) <= limit else text[:limit - 3] + "..."


# ---------------------------------------------------------------------------
# Phase B: concrete dimensions from the host entries
# ---------------------------------------------------------------------------


@dataclass
class Find:
    function: str
    primitive: str
    dimension: str
    lines: set = field(default_factory=set)
    file: str = ""
    entries: dict = field(default_factory=dict)   # host function -> (file, line)
    via: set = field(default_factory=set)         # functions carrying it there
    path: list = field(default_factory=list)
    klass: str = "unexpected"
    bound: str | None = None

    @property
    def key(self) -> str:
        return f"{self.function} {self.primitive} {self.dimension}"


@dataclass
class Analysis:
    tree: Tree
    summaries: dict
    reached: dict
    finds: dict
    unresolved: list
    cold: set
    entries: list
    uncalled: set = field(default_factory=set)
    cuts: dict = field(default_factory=dict)


def propagate(tree: Tree, summarizer: Summarizer) -> tuple[dict, dict, dict]:
    definitions = summarizer.definitions
    summaries = summarizer.summaries
    reached: dict[str, list] = {}            # function -> [(caller, line, kind)]
    carried: dict[tuple[str, int], dict[str, list]] = collections.defaultdict(dict)
    work = collections.deque()
    for name, definition in definitions.items():
        if definition.host and not name.endswith(GUARD):
            reached[name] = []
            work.append(name)
    queued = set(work)
    while work:
        name = work.popleft()
        queued.discard(name)
        summary = summaries.get(name)
        if summary is None:
            continue
        for callee, line, arguments, kind in summary.calls:
            changed = False
            if callee not in reached:
                reached[callee] = []
                changed = True
            if (name, line, kind) not in reached[callee]:
                reached[callee].append((name, line, kind))
            for index, label in enumerate(arguments):
                for dimension, source in concrete(label, name, carried):
                    slot = carried[(callee, index)]
                    if dimension not in slot:
                        slot[dimension] = []
                        changed = True
                    edge = (name, line, kind, source)
                    if edge not in slot[dimension]:
                        slot[dimension].append(edge)
            if changed and callee not in queued and callee in summaries:
                queued.add(callee)
                work.append(callee)
    return reached, carried, {}


def concrete(label: frozenset, function: str, carried) -> list[tuple[str, object]]:
    out = []
    for item in sorted(label):
        if item.startswith("#"):
            index = int(item[1:])
            for dimension in carried.get((function, index), {}):
                out.append((dimension, ("formal", index)))
        else:
            out.append((item, ("seed",)))
    return out


def cold_hosts(definitions: dict, summaries: dict, words: set[str],
               served: set[str]) -> set[str]:
    hosts = {name for name, d in definitions.items() if d.host}

    def named_cold(name: str) -> bool:
        tokens = set(name.split("-"))
        return bool(tokens & words) and not tokens & served

    callers: dict[str, set[str]] = collections.defaultdict(set)
    for name in hosts:
        for callee, _line, _args, _kind in summaries.get(name, Summary()).calls:
            if callee in hosts and callee != name:
                callers[callee].add(name)
    cold = {name for name in hosts if named_cold(name)}
    changed = True
    while changed:
        changed = False
        for name in hosts - cold:
            if callers[name] and callers[name] <= cold:
                cold.add(name)
                changed = True
    return cold


def uncalled_hosts(root: Path, definitions: dict) -> set[str]:
    """Host functions no other code names: not a host line, only a definition.

    A host function counts as called when its name occurs outside a comment in
    any host file other than at its own definition, or anywhere in a
    tools/*.py or tests/*.py file (a bridge builds its calls as text).
    """
    import re
    counts: collections.Counter = collections.Counter()
    token = re.compile(r"[a-z0-9*%<>=/+!?$&.-]+")
    for directory in ("host", "host/native"):
        for path in sorted((root / directory).glob("*.lisp")):
            for line in path.read_text(encoding="utf-8").lower().splitlines():
                counts.update(token.findall(line.split(";", 1)[0]))
    python = collections.Counter()
    for directory in ("tools", "tests"):
        for path in sorted((root / directory).glob("*.py")):
            python.update(token.findall(path.read_text(encoding="utf-8").lower()))
    return {name for name, d in definitions.items()
            if d.host and counts[name] <= 1 and not python[name]}


def boundary(tree_defs: dict, reached: dict, carried: dict, function: str,
             start: list, via: set | None = None) -> tuple[dict, list]:
    """Host functions whose calls carry the dimension to `function`'s site.

    `start` is a list of backward nodes: ("dim", f, index, D) or ("reach", f).
    Returns {host function: (file, line)} and one shortest path, host first.
    """
    entries: dict[str, tuple[str, int]] = {}
    parent: dict = {}
    seen = set(start)
    queue = collections.deque(start)
    first_path: list = []
    while queue:
        node = queue.popleft()
        name = node[1]
        if via is not None:
            via.add(name)
        definition = tree_defs.get(name)
        if definition is not None and definition.host:
            continue
        if node[0] == "dim":
            _, f, index, dimension = node
            edges = carried.get((f, index), {}).get(dimension, [])
            nexts = []
            for caller, line, kind, source in edges:
                if source[0] == "seed":
                    nexts.append((("reach", caller), caller, line, kind))
                else:
                    nexts.append((("dim", caller, source[1], dimension), caller, line, kind))
        else:
            nexts = [(("reach", caller), caller, line, kind)
                     for caller, line, kind in reached.get(name, [])]
        for nxt, caller, line, kind in nexts:
            caller_def = tree_defs.get(caller)
            if caller_def is not None and caller_def.host:
                if caller not in entries:
                    entries[caller] = (caller_def.file, line)
                    if not first_path:
                        chain = [(caller, line, kind)]
                        cursor = node
                        while cursor is not None:
                            chain.append((cursor[1], None, None))
                            cursor = parent.get(cursor)
                        first_path = chain
                continue
            if nxt not in seen:
                seen.add(nxt)
                parent[nxt] = node
                queue.append(nxt)
    return entries, first_path


def analyze(root: Path = ROOT, dimensions_path: Path | None = None) -> Analysis:
    dims = json.loads((dimensions_path or root / "tools" / "hot_path_dimensions.json")
                      .read_text(encoding="utf-8"))
    tree = read_tree(root)
    summarizer = Summarizer(tree, dict(dims["seeds"]),
                            set(dims["host_dispatchers"]["names"]),
                            dims.get("formal_seeds"), dims.get("cuts"))
    summarizer.run()
    reached, carried, _ = propagate(tree, summarizer)
    definitions = summarizer.definitions
    summaries = summarizer.summaries
    cold = cold_hosts(definitions, summaries, set(dims["cold_entries"]["words"]),
                      set(dims["cold_entries"].get("served_words", [])))
    uncalled = uncalled_hosts(root, definitions)
    resumable = {key: reason for key, reason in dims.get("resumable", {}).items()
                 if key != "note"}

    finds: dict[str, Find] = {}
    unresolved: list = []
    for name in sorted(reached):
        summary = summaries.get(name)
        if summary is None:
            continue
        definition = definitions[base_name(name)]
        for primitive, line, label in summary.sites:
            for dimension, source in concrete(label, name, carried):
                key = f"{name} {primitive} {dimension}"
                find = finds.get(key)
                if find is None:
                    find = finds[key] = Find(name, primitive, dimension,
                                             file=definition.file)
                find.lines.add(line)
                node = (("dim", name, source[1], dimension) if source[0] == "formal"
                        else ("reach", name))
                if definition.host:
                    find.entries.setdefault(name, (definition.file, line))
                    if not find.path:
                        find.path = [(name, line, "site")]
                    continue
                entries, path = boundary(definitions, reached, carried, name, [node],
                                         find.via)
                for host, where in entries.items():
                    find.entries.setdefault(host, where)
                if path and not find.path:
                    find.path = path
        for what, line, label in summary.unresolved:
            dims_here = sorted({d for d, _ in concrete(label, name, carried)})
            unresolved.append((name, definition.file, line, what, dims_here))

    for find in finds.values():
        if find.key in resumable or find.function in resumable:
            find.klass = "resumable"
            find.bound = resumable.get(find.key) or resumable.get(find.function)
        elif find.dimension == "K":
            find.klass = "output-proportional"
        elif find.entries and all(host in uncalled for host in find.entries):
            find.klass = "uncalled"
        elif find.entries and all(host in cold or host in uncalled
                                  for host in find.entries):
            find.klass = "cold"
        else:
            find.klass = "unexpected"
    entries = sorted({host for find in finds.values() for host in find.entries})
    return Analysis(tree, summaries, reached, finds, unresolved, cold, entries, uncalled,
                    dict(summarizer.cuts))


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

FINDINGS = ROOT / "planning" / "hot-path-findings.json"


def load_findings(path: Path = FINDINGS) -> dict:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8")).get("findings", {})


def path_text(find: Find) -> str:
    names = []
    for name, _line, _kind in find.path:
        if name and (not names or names[-1] != name):
            names.append(name)
    return " -> ".join(names) + f" [{find.primitive}]"


def where_text(find: Find, definitions: dict) -> str:
    lines = sorted(find.lines)
    return f"{find.file}:{','.join(str(n) for n in lines[:4])}" + (
        "..." if len(lines) > 4 else "")


def by_class(analysis: Analysis) -> collections.Counter:
    counts = collections.Counter(find.klass for find in analysis.finds.values())
    counts["unresolved"] = sum(1 for row in analysis.unresolved if row[4])
    return counts


def compare(analysis: Analysis, listed: dict) -> tuple[list, list]:
    fresh = sorted(key for key, find in analysis.finds.items()
                   if find.klass == "unexpected" and key not in listed)
    stale = sorted(key for key in listed if key not in analysis.finds)
    return fresh, stale


def report(analysis: Analysis, listed: dict, out) -> None:
    definitions = analysis.tree.definitions
    grouped: dict[str, list[Find]] = collections.defaultdict(list)
    for find in analysis.finds.values():
        for host in find.entries:
            grouped[host].append(find)
    for host in sorted(grouped, key=lambda h: (definitions[h].file, definitions[h].line)):
        definition = definitions[host]
        print(f"{definition.where} {host} [{entry_state(analysis, host)}]", file=out)
        for find in sorted(grouped[host], key=lambda f: (f.klass, f.file, f.function)):
            file, line = find.entries[host]
            owner = listed.get(find.key, {}).get("packet", "NEW")
            print(f"  {find.dimension} {find.primitive:<10} {where_text(find, definitions)}"
                  f"  {find.function}  {find.klass}  {owner}  (host line {file}:{line})",
                  file=out)
    print("", file=out)
    print("Unresolved edges (a seeded value handed to something this tool cannot follow):",
          file=out)
    for name, file, line, what, dims in sorted(analysis.unresolved):
        print(f"  {'/'.join(dims)} {file}:{line} {name}: {what}", file=out)


def entry_state(analysis: Analysis, host: str) -> str:
    if host in analysis.uncalled:
        return "uncalled"
    return "cold" if host in analysis.cold else "served"


def why(analysis: Analysis, function: str, out) -> None:
    """Every host entry reaching `function`, each with one shortest call path."""
    definitions = analysis.tree.definitions
    if function not in analysis.reached:
        print(f"{function}: no host entry reaches it", file=out)
        return
    parent: dict = {function: None}
    queue = collections.deque([function])
    found = []
    while queue:
        name = queue.popleft()
        for caller, line, kind in analysis.reached.get(name, []):
            if caller in parent:
                continue
            parent[caller] = (name, line, kind)
            definition = definitions.get(caller)
            if definition is not None and definition.host:
                found.append(caller)
            else:
                queue.append(caller)
    print(f"{function}: reached from {len(found)} host entries", file=out)
    for host in found:
        chain, cursor = [host], host
        while parent[cursor] is not None:
            name, line, kind = parent[cursor]
            chain.append(f"{name} ({kind} at {line})")
            cursor = name
        state = entry_state(analysis, host)
        print(f"  {definitions[host].where} [{state}] " + " -> ".join(chain), file=out)


def as_json(analysis: Analysis, listed: dict) -> dict:
    definitions = analysis.tree.definitions
    return {
        "schema": 1,
        "counts": dict(by_class(analysis)),
        "finds": {
            key: {"function": f.function, "primitive": f.primitive,
                  "dimension": f.dimension, "where": where_text(f, definitions),
                  "class": f.klass, "bound": f.bound,
                  "packet": listed.get(key, {}).get("packet"),
                  "entries": {host: f"{file}:{line}" for host, (file, line)
                              in sorted(f.entries.items())},
                  "path": path_text(f), "via": sorted(f.via)}
            for key, f in sorted(analysis.finds.items())},
        "unresolved": [{"function": n, "where": f"{file}:{line}", "what": w,
                        "dimensions": d}
                       for n, file, line, w, d in sorted(analysis.unresolved)],
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--report", action="store_true",
                        help="every find, grouped by host entry, with its path")
    parser.add_argument("--summary", action="store_true",
                        help="the counts, and every NEW or STALE find")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 on a NEW unexpected find or a STALE listed one")
    parser.add_argument("--json", default=None, help="write every find as JSON here")
    parser.add_argument("--why", default=None, metavar="FUNCTION",
                        help="the host entries that reach FUNCTION, each with one shortest path")
    parser.add_argument("--find", default=None,
                        help="print the finds whose function contains this text")
    arguments = parser.parse_args(argv)

    analysis = analyze()
    listed = load_findings()
    fresh, stale = compare(analysis, listed)
    counts = by_class(analysis)
    if arguments.report:
        report(analysis, listed, sys.stdout)
    if arguments.why:
        why(analysis, arguments.why, sys.stdout)
    if arguments.find:
        for key, find in sorted(analysis.finds.items()):
            if arguments.find in find.function:
                print(f"{key}: {find.klass} {where_text(find, analysis.tree.definitions)}"
                      f" entries={len(find.entries)} path={path_text(find)}")
    reached_books = sum(1 for name in analysis.reached
                        if base_name(name) in analysis.tree.definitions
                        and not analysis.tree.definitions[base_name(name)].host)
    print(f"hot_path_check: {len(analysis.finds)} traversals of retained state on "
          f"paths from {len(analysis.entries)} host entries ("
          + ", ".join(f"{counts.get(k, 0)} {k}" for k in CLASSES)
          + f"); {reached_books} book functions reached; "
          f"{len(fresh)} NEW, {len(stale)} STALE against "
          f"{FINDINGS.relative_to(ROOT)}")
    edges = sorted({row[3] for row in analysis.unresolved})
    print(f"hot_path_check: {len(analysis.unresolved)} unresolved edge sites on reached "
          f"functions ({len(edges)} distinct; "
          f"{sum(1 for row in analysis.unresolved if row[4])} carrying a seeded value): "
          + "; ".join(edges[:12]) + (" ..." if len(edges) > 12 else ""))
    for name, reason in sorted(analysis.cuts.items()):
        print(f"hot_path_check: cut (not descended; a named claim) -- {name}: {reason}")
    for key in fresh:
        find = analysis.finds[key]
        print(f"hot_path_check: NEW unexpected find -- {key} at "
              f"{where_text(find, analysis.tree.definitions)} via {path_text(find)}")
    for key in stale:
        print(f"hot_path_check: STALE listed find (no longer occurs) -- {key}")
    if arguments.json:
        Path(arguments.json).write_text(json.dumps(as_json(analysis, listed), indent=1,
                                                   sort_keys=True) + "\n")
    return 1 if arguments.strict and (fresh or stale) else 0


if __name__ == "__main__":
    sys.exit(main())
