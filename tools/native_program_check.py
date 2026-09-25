#!/usr/bin/env python3
"""Check the native host's write paths against the byte model's programs.

For each byte-model program the native cut table names
(`tests/campaign/native_cuts.py`, `ALL_CUTS`, fields `.program` and
`.follows`), find the host function in `host/native/io.lisp` that performs it
(`PROGRAM_HOSTS` below) and compare, statically over the source text:

* SEQUENCE.  The host's durable syscalls, ACL2 file-kernel observations and
  `fnn-at` cuts on the straight-line success path, read in source order,
  must equal the program's step list in `books/byte-store-programs.lisp`,
  step for step.  A step compares by kind AND directory: `(fnn-fsync-dir
  (fnn-transactions store))` is `(:fsync-dir :transactions)`, never
  `:root`.  A file name compares only where the host expression is a fixed
  name (config.json, allocation-frontier.json); a `stage`/`final` variable
  matches a model variable and nothing else.  File contents are not compared.
  Calls to other `io.lisp` functions that reach a step primitive are expanded
  from the callee's own defun with its parameters bound to the call's
  arguments (so `fnn-write-staged-at`'s cuts are the caller's keywords).
  Observations compare by the fn-sf transition they dispatch to: the host's
  operation through `fn-sn-file-step` (books/store-node.lisp), the model's
  event through `fn-sf-dispatch` (books/store-files-traces.lisp); two names
  are aliases iff they reach the same fn-sf function, so the alias table is
  derived, and a host operation `fn-sn-file-step` does not dispatch is a
  mismatch.  A host cut compares through the table's `model_name` and
  `occurrence` (`recover-barrier-3` is the third `recover-barrier`).
* ERROR ARMS.  Every `fnn-observe` inside a `handler-case` clause is an
  error-arm observation; each must be (after aliasing) the event of one of
  the program's declared error-arm constants (the `defconst`s after the
  program's defun).  One that is not is a mismatch.  A declared arm the host
  never observes is reported, not failed.
* INJECTION SITES.  A success-path `fnn-at` that is no cut of the program is
  an injection-only site (reported); if it is also listed in
  `+fnn-post-model-cuts+` or `+fnn-recovery-model-cuts+` it is a mismatch.

It CANNOT decide, and does not claim: runtime control flow -- which arm of a
`handler-case`, `ignore-errors`, `when`/`unless`/`if` runs; every form is read
as executed once, in source order, and a `loop`/`dolist` other than
`fnn-recover`'s barrier loop (expanded to its five lambdas) is read as one
iteration; whether an opaque ACL2 call (`OPAQUE_CALLS`) performs the
transitions it is declared to; what a `funcall` of any other callback or a
function defined outside io.lisp does; operating-system semantics of the
syscalls; that the running image executes the source read here; and
anything in the callers of these functions.  Parsing is a small
s-expression scanner over the defun text: no Lisp reader, no evaluation.

Exit status: 1 on any mismatch, 0 otherwise.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, field
import difflib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tests.campaign.native_cuts import ALL_CUTS  # noqa: E402

HOST = "host/native/io.lisp"
BOOK = "books/byte-store-programs.lisp"
NODE = "books/store-node.lisp"
TRACES = "books/store-files-traces.lisp"

# Which host function performs which program (the book's own comments and
# tests/campaign/native_cuts.py name the same pairs).
PROGRAM_HOSTS = {
    "fn-bs-frontier-program": "fnn-advance-frontier",
    "fn-bs-record-program": "fnn-publish",
    "fn-bs-finish-program": "fnn-finish",
    "fn-bs-recover-program": "fnn-recover",
    "fn-bs-recover-stage-cleanup-program": "fnn-sweep-staging",
    "fn-bs-marker-program": "fnn-mark-committed",
}

# Opaque ACL2 calls: the check trusts that the callee performs the named
# transitions.  Key: a called function name, or "funcall <variable>".
OPAQUE_CALLS = {
    "fnn-bridge-recover": (
        ["(:recover)"],
        "the host's replay: submits the recovered records to fn-sf-recover "
        "through the store-node bridge (host/store-node-host.lisp)"),
    "funcall *fnn-finish-callback*": (
        ["(:core-completion sequence txid)", "(:emit-success sequence txid)"],
        "one ACL2 call, fn-sn-finish (books/store-node.lisp), which performs "
        "the core completion and then the success emission"),
}

# A call that begins a following program, checked separately; it must come
# after every step of the calling program.
SEQUELS = {
    "fnn-sweep-staging": "fn-bs-recover-stage-cleanup-program",
}

# Model directory ids for host directory expressions.
DIR_ACCESSORS = {
    "fnn-store-root": ":root",
    "fnn-transactions": ":transactions",
    "fnn-staging": ":staging",
}

SYSCALLS = {"fnn-open", "fnn-write-all", "fnn-fsync-file", "fnn-fsync-regular",
            "fnn-fsync-dir", "fnn-replace", "fnn-link", "fnn-unlink", "fnn-mkdir"}
PRIMITIVES = SYSCALLS | {"fnn-observe", "fnn-at"}


# ---------------------------------------------------------------------------
# S-expression scanning (no reader, no evaluation).

class Str(str):
    """A string literal, as distinct from a symbol."""


def tokenize(text: str):
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ";":
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("#|", i):
            j = text.find("|#", i)
            i = n if j < 0 else j + 2
        elif c in "()":
            yield c
            i += 1
        elif c == "'":
            yield "'"
            i += 1
        elif c == "`":
            yield "`"
            i += 1
        elif c == ",":
            if text.startswith(",@", i):
                yield ",@"
                i += 2
            else:
                yield ","
                i += 1
        elif text.startswith("#'", i):
            yield "#'"
            i += 2
        elif text.startswith("#\\", i):
            j = i + 3
            while j < n and (text[j].isalnum() or text[j] in "-_"):
                j += 1
            yield text[i:j]
            i = j
        elif c == '"':
            j, buf = i + 1, []
            while j < n and text[j] != '"':
                if text[j] == "\\":
                    j += 1
                buf.append(text[j])
                j += 1
            yield Str("".join(buf))
            i = j + 1
        elif c == "|":
            j = text.find("|", i + 1)
            yield text[i:j + 1]
            i = j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in "()'\";`,":
                j += 1
            yield text[i:j].lower()
            i = j


_PREFIX = {"'": "quote", "`": "quasiquote", ",": "unquote", ",@": "unquote",
           "#'": "function"}


def read_one(tokens):
    tok = next(tokens)
    if tok == "(":
        out = []
        while True:
            try:
                out.append(read_one(tokens))
            except _Close:
                return out
    if tok == ")":
        raise _Close()
    if not isinstance(tok, Str) and tok in _PREFIX:
        return [_PREFIX[tok], read_one(tokens)]
    return tok


class _Close(Exception):
    pass


def parse_at(text: str, offset: int):
    return read_one(tokenize(text[offset:]))


def show(form, limit: int = 90) -> str:
    def render(f):
        if isinstance(f, Str):
            return '"{}"'.format(f)
        if isinstance(f, list):
            if len(f) == 2 and f[0] == "quote":
                return "'" + render(f[1])
            return "(" + " ".join(render(x) for x in f) + ")"
        return str(f)
    s = render(form)
    return s if len(s) <= limit else s[:limit - 3] + "..."


def is_sym(x) -> bool:
    return isinstance(x, str) and not isinstance(x, Str)


def is_kw(x) -> bool:
    return is_sym(x) and x.startswith(":")


def definitions(text: str, kind: str) -> dict:
    """Top-level (KIND NAME ...) forms, by name, parsed lazily."""
    out = {}
    for m in re.finditer(r"^\({} (\S+)".format(kind), text, re.M):
        out[m.group(1).lower()] = m.start()
    return out


# ---------------------------------------------------------------------------
# Steps.

@dataclass
class Step:
    kind: str
    key: str
    text: str
    cut: str | None = None


def dir_key(d) -> str:
    return d if isinstance(d, str) else "?"


def name_key(n) -> str:
    return "<var>" if n is None else n


def path_step(kind, paths, text) -> Step:
    parts = []
    for p in paths:
        if isinstance(p, tuple):
            parts.append("{} {}".format(dir_key(p[0]), name_key(p[1])))
        else:
            parts.append("? ?")
    return Step(kind, "{} {}".format(kind, " -> ".join(parts)), text)


def dir_step(d, text) -> Step:
    return Step(":fsync-dir", ":fsync-dir {}".format(dir_key(d)), text)


def observe_key(fn: str, result: str | None) -> str:
    return "observe {}".format(fn) if result == "*" else "observe {} {}".format(fn, result)


# ---------------------------------------------------------------------------
# The model side.

class Model:
    def __init__(self, book: str, node: str, traces: str):
        self.book = book
        self.defuns = definitions(book, "defun")
        self.consts = {}
        for name, off in definitions(book, "defconst").items():
            form = parse_at(book, off)
            self.consts[name] = form[2]
        self.host_ops = self._case_table(node, "fn-sn-file-step")
        self.events = self._cond_table(traces, "fn-sf-dispatch")

    @staticmethod
    def _body(text, name):
        off = definitions(text, "defun").get(name)
        if off is None:
            raise AssertionError("{} not found".format(name))
        return parse_at(text, off)

    def _case_table(self, text, name):
        table = {}

        def walk(f):
            if isinstance(f, list) and f and f[0] == "case":
                for clause in f[2:]:
                    if (isinstance(clause, list) and is_kw(clause[0])
                            and isinstance(clause[1], list)):
                        table[clause[0]] = clause[1][0]
            elif isinstance(f, list):
                for x in f:
                    walk(x)
        walk(self._body(text, name))
        if not table:
            raise AssertionError("no case table in {}".format(name))
        return table

    def _cond_table(self, text, name):
        table = {}

        def walk(f):
            if isinstance(f, list) and f and f[0] == "cond":
                for clause in f[1:]:
                    test = clause[0]
                    if (isinstance(test, list) and test[:1] == ["equal"]
                            and is_kw(test[2]) and isinstance(clause[1], list)):
                        table[test[2]] = clause[1][0]
            elif isinstance(f, list):
                for x in f:
                    walk(x)
        walk(self._body(text, name))
        if not table:
            raise AssertionError("no dispatch table in {}".format(name))
        return table

    def event(self, ev) -> tuple[str, str]:
        """(fn-sf function, result) of a model event list."""
        name = ev[0]
        fn = self.events.get(name, "undispatched-event:" + name)
        if len(ev) == 1:
            return fn, ":ok"
        return fn, ev[1] if is_kw(ev[1]) else "*"

    def value(self, x):
        if isinstance(x, list) and x and x[0] == "quote":
            return x[1]
        if isinstance(x, list) and x and x[0] == "list":
            return [self.value(y) for y in x[1:]]
        if is_sym(x) and x.startswith("*") and x in self.consts:
            return self.value(self.consts[x])
        return x

    def steps(self, program: str) -> list[Step]:
        form = self._body(self.book, program)
        body = form[-1]
        if not (isinstance(body, list) and body[:1] == ["list"]):
            raise AssertionError("{} is not a literal step list".format(program))
        out, seen = [], {}
        for raw in body[1:]:
            s = [self.value(x) for x in raw[1:]]
            kind, text = s[0], show(raw)

            def p(d, n):
                return (d, n if isinstance(n, Str) else None)
            if kind == ":cut":
                seen[s[1]] = seen.get(s[1], 0) + 1
                out.append(Step(kind, "cut {}#{}".format(s[1], seen[s[1]]), text, s[1]))
            elif kind == ":observe":
                out.append(Step(kind, observe_key(*self.event(s[1])), text))
            elif kind == ":fsync-dir":
                out.append(dir_step(s[1], text))
            elif kind in (":create", ":write-all", ":fsync-file", ":unlink"):
                out.append(path_step(kind, [p(s[1], s[2])], text))
            elif kind in (":rename", ":link", ":link-eexist"):
                out.append(path_step(kind, [p(s[1], s[2]), p(s[3], s[4])], text))
            else:
                out.append(Step(kind, "{} {}".format(kind, show(s[1:])), text))
        return out

    def error_arms(self, program: str) -> dict:
        """{(fn, result): constant name} for the defconsts after the program."""
        start = self.defuns[program]
        later = [o for o in self.defuns.values() if o > start]
        end = min(later) if later else len(self.book)
        arms = {}
        for m in re.finditer(r"^\(defconst (\*\S+\*)", self.book[start:end], re.M):
            for step in self.value(self.consts[m.group(1).lower()]):
                if step[0] == ":observe":
                    arms[self.event(step[1])] = m.group(1).lower()
        return arms


# ---------------------------------------------------------------------------
# The host side.

@dataclass
class Dir:
    id: str


@dataclass
class Fd:
    path: object


@dataclass
class Lambda:
    body: list


NIL = "nil"  # an unsupplied &optional parameter with no default


class Walk:
    def __init__(self, host: str, model: Model, root_fn: str):
        self.host = host
        self.model = model
        self.root_fn = root_fn
        self.defuns = definitions(host, "defun")
        self.forms = {}
        self.file_paths = self._file_accessors()
        self.reaches = self._reaches()
        self.success: list[Step] = []
        self.errors: list[tuple[tuple[str, str], str, str]] = []
        self.error_syscalls: list[str] = []
        self.opaque: list[str] = []
        self.unmapped: list[str] = []
        self.one_iteration: list[str] = []
        self.expanded: list[str] = []
        self.undispatched: list[str] = []
        self.sequels: list[tuple[int, str]] = []
        self.cut_seen: dict = {}
        self.table = {c.name: (c.model_name or c.name, c.occurrence) for c in ALL_CUTS}

    def form(self, name):
        if name not in self.forms:
            self.forms[name] = parse_at(self.host, self.defuns[name])
        return self.forms[name]

    def _file_accessors(self):
        """(defun fnn-X (s) (fnn-join (DIR-ACCESSOR s) "literal")) -> path."""
        out = {}
        pat = re.compile(r'^\(defun (fnn-[\w-]+) \((\w+)\) \(fnn-join \((fnn-[\w-]+) \2\) "([^"]+)"\)\)',
                         re.M)
        for m in pat.finditer(self.host):
            name, acc, lit = m.group(1), m.group(3), m.group(4)
            if name not in DIR_ACCESSORS and acc in DIR_ACCESSORS:
                out[name] = (DIR_ACCESSORS[acc], lit)
        return out

    def _reaches(self):
        roots = PRIMITIVES | {k for k in OPAQUE_CALLS if " " not in k} | set(SEQUELS)
        opaque_vars = {k.split()[1] for k in OPAQUE_CALLS if " " in k}
        calls = {}
        for name, off in self.defuns.items():
            nxt = self.host.find("\n(defun ", off + 1)
            words = set(re.findall(r"[\w*+:-]+", self.host[off:nxt if nxt > 0 else None].lower()))
            calls[name] = words
        reach = {n for n, w in calls.items() if (w & (roots | opaque_vars))}
        changed = True
        while changed:
            changed = False
            for n, w in calls.items():
                if n not in reach and w & reach:
                    reach.add(n)
                    changed = True
        return reach - PRIMITIVES

    # -- evaluation of path / cut expressions

    def value(self, x, env):
        if isinstance(x, Str):
            return x
        if is_kw(x):
            return x
        if is_sym(x):
            if x in env:
                return env[x]
            return None
        if not isinstance(x, list) or not x:
            return None
        head = x[0]
        if head in DIR_ACCESSORS:
            return Dir(DIR_ACCESSORS[head])
        if head == "fnn-parent":
            inner = self.value(x[1], env)
            if isinstance(inner, Dir) and inner.id == ":root":
                return Dir(":parent")
            return None
        if head in self.file_paths:
            return self.file_paths[head]
        if head == "fnn-join":
            d = self.value(x[1], env)
            n = x[2]
            return (d.id if isinstance(d, Dir) else None,
                    str(n) if isinstance(n, Str) else None)
        if head == "fnn-open":
            return Fd(self.value(x[1], env))
        if head == "format" and len(x) >= 3 and isinstance(x[2], Str):
            args = [self.value(a, env) for a in x[3:]]
            if all(isinstance(a, int) for a in args):
                s = str(x[2])
                for a in args:
                    s = re.sub(r"~[da]", str(a), s, count=1)
                return Str(s)
            return None
        if head == "intern":
            s = self.value(x[1], env)
            return ":" + s.lower() if isinstance(s, Str) else None
        return None

    def path(self, x, env):
        v = self.value(x, env)
        if isinstance(v, Fd):
            v = v.path
        return v if isinstance(v, tuple) else None

    # -- the walk

    def emit(self, step: Step, mode: str):
        if mode == "success":
            self.success.append(step)
        else:
            self.error_syscalls.append(step.text)

    def walk_body(self, forms, env, mode, stack):
        for f in forms:
            self.walk(f, env, mode, stack)

    def walk(self, f, env, mode, stack):
        if not isinstance(f, list) or not f:
            return
        head = f[0]
        if head in ("quote", "function", "declare"):
            return
        text = show(f)
        if head in ("let", "let*"):
            env = dict(env)
            for b in f[1]:
                if isinstance(b, list):
                    if len(b) > 1:
                        self.walk(b[1], env, mode, stack)
                        env[b[0]] = self.value(b[1], env)
                    else:
                        env[b[0]] = None
                else:
                    env[b] = None
            self.walk_body(f[2:], env, mode, stack)
        elif head == "multiple-value-bind":
            self.walk(f[2], env, mode, stack)
            env = dict(env, **{v: None for v in f[1]})
            self.walk_body(f[3:], env, mode, stack)
        elif head == "handler-case":
            self.walk(f[1], env, mode, stack)
            for clause in f[2:]:
                inner = dict(env, **{v: None for v in (clause[1] or [])})
                self.walk_body(clause[2:], inner, "error", stack)
        elif (head in ("when", "unless", "if") and is_sym(f[1]) and f[1] in env
              and env[f[1]] == NIL):
            # A parameter statically nil (unsupplied &optional): the arm is dead.
            if mode == "success":
                self.one_iteration.append("static nil, arm skipped: {}".format(show(f, 60)))
            live = {"when": [], "unless": f[2:], "if": f[3:]}[head]
            self.walk_body(live, env, mode, stack)
        elif head == "dolist":
            self.walk(f[1][1], env, mode, stack)
            if mode == "success":
                self.one_iteration.append("dolist over {}".format(show(f[1][1], 50)))
            self.walk_body(f[2:], dict(env, **{f[1][0]: None}), mode, stack)
        elif head == "loop":
            self.walk_loop(f, env, mode, stack)
        elif head == "lambda":
            if mode == "success":
                self.one_iteration.append("lambda body read in place: {}".format(text))
            self.walk_body(f[2:], env, mode, stack)
        elif head == "funcall":
            self.walk_funcall(f, env, mode, stack)
        elif head == "fnn-observe":
            op = f[2]
            result = f[3] if len(f) > 3 else ":ok"
            fn = self.model.host_ops.get(op)
            if fn is None:
                fn = "undispatched-host-operation:" + op
                self.undispatched.append(text)
            if mode == "success":
                self.success.append(Step(":observe", observe_key(fn, result), text))
            else:
                self.errors.append(((fn, result), op + " " + result, text))
        elif head == "fnn-at":
            point = self.value(f[2], env)
            if mode != "success":
                return
            if not is_kw(point):
                self.success.append(Step(":cut", "cut ?", text, "?"))
                return
            name = point[1:]
            if name in self.table:
                mn, occ = self.table[name]
            else:
                self.cut_seen[name] = self.cut_seen.get(name, 0) + 1
                mn, occ = name, self.cut_seen[name]
            self.success.append(Step(":cut", "cut {}#{}".format(mn, occ), text, name))
        elif head in SYSCALLS:
            self.walk_body(f[1:], env, mode, stack)
            self.syscall(f, env, mode)
        elif head in OPAQUE_CALLS:
            self.walk_body(f[1:], env, mode, stack)
            self.opaque_call(head, text, mode)
        elif head in SEQUELS and head != self.root_fn:
            if mode == "success":
                self.sequels.append((len(self.success), text))
        elif head in self.reaches and head in self.defuns and head not in stack:
            self.walk_body(f[1:], env, mode, stack)
            self.expand(head, f[1:], env, mode, stack)
        else:
            self.walk_body(f[1:], env, mode, stack)

    def syscall(self, f, env, mode):
        head, text = f[0], show(f)
        if head == "fnn-open":
            flags = set(re.findall(r"[\w:+-]+", show(f[2], 10**6))) if len(f) > 2 else set()
            if "sb-posix:o-creat" in flags and "sb-posix:o-excl" in flags:
                self.emit(path_step(":create", [self.path(f[1], env)], text), mode)
            elif "sb-posix:o-creat" in flags:
                self.emit(Step(":open-creat", "open-creat", text), mode)
            # An open without O_CREAT is a read: no step.
        elif head in ("fnn-write-all", "fnn-fsync-file", "fnn-fsync-regular", "fnn-unlink"):
            kind = {"fnn-write-all": ":write-all", "fnn-fsync-file": ":fsync-file",
                    "fnn-fsync-regular": ":fsync-file", "fnn-unlink": ":unlink"}[head]
            self.emit(path_step(kind, [self.path(f[1], env)], text), mode)
        elif head == "fnn-fsync-dir":
            d = self.value(f[1], env)
            self.emit(dir_step(d.id if isinstance(d, Dir) else None, text), mode)
        elif head in ("fnn-replace", "fnn-link"):
            kind = ":rename" if head == "fnn-replace" else ":link"
            self.emit(path_step(kind, [self.path(f[1], env), self.path(f[2], env)], text), mode)
        elif head == "fnn-mkdir":
            self.emit(Step(":mkdir", "mkdir " + show(f[1:]), text), mode)

    def opaque_call(self, key, text, mode):
        events, _ = OPAQUE_CALLS[key]
        if mode == "success":
            self.opaque.append(key)
        for ev in events:
            parsed = parse_at(ev, 0)
            fn, result = self.model.event(parsed)
            step = Step(":observe", observe_key(fn, result), "{} [opaque: {}]".format(text, ev))
            if mode == "success":
                self.success.append(step)
            else:
                self.errors.append(((fn, result), ev, text))

    def walk_funcall(self, f, env, mode, stack):
        target = f[1]
        self.walk_body(f[2:], env, mode, stack)
        key = "funcall {}".format(target) if is_sym(target) else None
        bound = env.get(target) if is_sym(target) else None
        if isinstance(bound, Lambda):
            self.walk_body(bound.body, env, mode, stack)
        elif key in OPAQUE_CALLS:
            self.opaque_call(key, show(f), mode)
        elif mode == "success":
            self.unmapped.append(show(f))

    def walk_loop(self, f, env, mode, stack):
        # (loop for V in (list (lambda () ...) ...) for O from 1 do BODY...)
        if (len(f) > 9 and f[1] == "for" and f[3] == "in"
                and isinstance(f[4], list) and f[4][:1] == ["list"]
                and all(isinstance(x, list) and x[:1] == ["lambda"] for x in f[4][1:])
                and f[5] == "for" and f[7] == "from" and f[8] == "1" and f[9] == "do"):
            var, ordinal = f[2], f[6]
            for i, lam in enumerate(f[4][1:], start=1):
                inner = dict(env, **{var: Lambda(lam[2:]), ordinal: i})
                self.walk_body(f[10:], inner, mode, stack)
            return
        if mode == "success":
            self.one_iteration.append("loop read as one iteration: {}".format(show(f, 60)))
        self.walk_body(f[1:], env, mode, stack)

    def expand(self, name, args, env, mode, stack):
        d = self.form(name)
        inner, i, optional = {}, 0, False
        for p in d[2]:
            if p in ("&rest", "&key", "&body"):
                break
            if p == "&optional":
                optional = True
                continue
            param = p[0] if isinstance(p, list) else p
            if i < len(args):
                inner[param] = self.value(args[i], env)
            elif optional:
                default = p[1] if isinstance(p, list) and len(p) > 1 else None
                inner[param] = NIL if default in (None, "nil") else self.value(default, {})
            else:
                inner[param] = None
            i += 1
        before = len(self.success) + len(self.errors) + len(self.error_syscalls)
        body = d[3:]
        self.walk_body(body, inner, mode, stack | {name})
        if len(self.success) + len(self.errors) + len(self.error_syscalls) > before:
            if name not in self.expanded:
                self.expanded.append(name)

    def run(self):
        d = self.form(self.root_fn)
        env = {}
        self.walk_body(d[3:], env, "success", frozenset({self.root_fn}))


# ---------------------------------------------------------------------------
# The comparison.

@dataclass
class ProgramResult:
    program: str
    host_function: str
    model_steps: int
    host_steps: int
    matched: int
    verdict: str
    mismatches: list = field(default_factory=list)
    missing: list = field(default_factory=list)
    extra: list = field(default_factory=list)
    injection_only: list = field(default_factory=list)
    opaque: list = field(default_factory=list)
    error_arms: list = field(default_factory=list)
    error_arms_unobserved: list = field(default_factory=list)
    unmapped_calls: list = field(default_factory=list)
    read_once: list = field(default_factory=list)
    expanded_helpers: list = field(default_factory=list)
    error_arm_syscalls: list = field(default_factory=list)


@dataclass
class Report:
    programs: list
    opaque_calls: dict
    ok: bool


def declared_model_cuts(host: str) -> set:
    names = set()
    for param in ("fnn-post-model-cuts", "fnn-recovery-model-cuts"):
        m = re.search(r"\(defparameter \+{}\+\s+'\((.*?)\)\)".format(param), host, re.S)
        if not m:
            raise AssertionError("native cut declaration not found: " + param)
        names |= {s.lower() for s in re.findall(r':([A-Za-z0-9-]+)', m.group(1))}
        names |= {s.lower() for s in re.findall(r'"([A-Za-z0-9-]+)"', m.group(1))}
    return names


def programs_named() -> list[str]:
    out = []
    for c in ALL_CUTS:
        for p in (c.program, c.follows):
            if p and p not in out:
                out.append(p)
    return out


def check_program(program, host, model, declared) -> ProgramResult:
    fn = PROGRAM_HOSTS.get(program)
    if fn is None:
        return ProgramResult(program, "?", 0, 0, 0, "FAIL",
                             mismatches=["no host function declared for this program"])
    w = Walk(host, model, fn)
    if fn not in w.defuns:
        return ProgramResult(program, fn, 0, 0, 0, "FAIL",
                             mismatches=["host function {} not found".format(fn)])
    w.run()
    msteps = model.steps(program)
    model_cuts = {s.cut for s in msteps if s.kind == ":cut"}
    r = ProgramResult(program, fn, len(msteps), 0, 0, "PASS")

    hsteps = []
    for s in w.success:
        if s.kind == ":cut" and s.cut != "?":
            mn = w.table.get(s.cut, (s.cut, 1))[0]
            if mn not in model_cuts:
                if s.cut in declared:
                    r.mismatches.append("declared model cut {} is no cut of {}: {}".format(
                        s.cut, program, s.text))
                else:
                    r.injection_only.append(s.cut)
                continue
        hsteps.append(s)
    r.host_steps = len(hsteps)

    hk, mk = [s.key for s in hsteps], [s.key for s in msteps]
    sm = difflib.SequenceMatcher(None, hk, mk, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            r.matched += i2 - i1
            continue
        r.missing += ["model step {}: {}".format(j + 1, msteps[j].text) for j in range(j1, j2)]
        r.extra += ["host: {}".format(hsteps[i].text) for i in range(i1, i2)]
        r.mismatches.append("{} at model step {}: host [{}] vs model [{}]".format(
            tag, j1 + 1, "; ".join(hk[i1:i2]) or "-", "; ".join(mk[j1:j2]) or "-"))

    arms = model.error_arms(program)
    seen = set()
    for event, label, text in w.errors:
        if event in arms:
            line = "{} -> {}".format(label, arms[event])
            count = sum(1 for e, l, _ in w.errors if (e, l) == (event, label))
            line += " (x{})".format(count) if count > 1 else ""
            if line not in r.error_arms:
                r.error_arms.append(line)
            seen.add(event)
        else:
            r.mismatches.append("error-arm observation with no model constant: {}".format(text))
    r.error_arms_unobserved = sorted(c for e, c in arms.items() if e not in seen)
    for text in w.undispatched:
        r.mismatches.append("host operation fn-sn-file-step does not dispatch: {}".format(text))
    for index, text in w.sequels:
        if index < len(w.success):
            r.mismatches.append("sequel {} precedes steps of {}".format(text, program))
    r.opaque = sorted(set(w.opaque))
    r.unmapped_calls = w.unmapped
    r.read_once = w.one_iteration
    r.expanded_helpers = w.expanded
    r.error_arm_syscalls = w.error_syscalls
    if r.mismatches:
        r.verdict = "FAIL"
    return r


def read(rel):
    return (ROOT / rel).read_text()


def model_books_text() -> str:
    """BOOK, then every other book a cut of the table names (NativeCut.book:
    books/byte-store-marker-program.lisp for the committed-history marker),
    read as one text: definitions and constants are found by name."""
    books = [BOOK] + sorted({"books/" + c.book for c in ALL_CUTS} - {BOOK})
    return "\n".join(read(b) for b in books)


def check(host_text: str | None = None, book_text: str | None = None,
          node_text: str | None = None, traces_text: str | None = None) -> Report:
    host = host_text if host_text is not None else read(HOST)
    model = Model(book_text if book_text is not None else model_books_text(),
                  node_text if node_text is not None else read(NODE),
                  traces_text if traces_text is not None else read(TRACES))
    declared = declared_model_cuts(host)
    results = [check_program(p, host, model, declared) for p in programs_named()]
    opaque = {k: {"events": v[0], "reason": v[1]} for k, v in OPAQUE_CALLS.items()}
    return Report(results, opaque, all(r.verdict == "PASS" for r in results))


def render(report: Report) -> str:
    lines = ["native program check: {} against {} (source text only)".format(HOST, BOOK)]
    for r in report.programs:
        lines.append("{} <- {}: model {} steps, host {}, matched {}: {}".format(
            r.program, r.host_function, r.model_steps, r.host_steps, r.matched, r.verdict))
        for label, items in (("MISMATCH", r.mismatches), ("model step the host lacks", r.missing),
                             ("host step the model lacks", r.extra),
                             ("injection-only site (no model cut)", r.injection_only),
                             ("opaque ACL2 call", r.opaque),
                             ("error arm", r.error_arms),
                             ("declared error arm the host never observes", r.error_arms_unobserved),
                             ("syscall in an error arm (not compared)", r.error_arm_syscalls),
                             ("unmapped call on the success path (not a step here)", r.unmapped_calls),
                             ("note", r.read_once),
                             ("expanded helper", r.expanded_helpers)):
            for item in items:
                lines.append("  {}: {}".format(label, item))
    lines.append("opaque ACL2 calls: the check trusts that the callee performs the named transitions:")
    for k, v in report.opaque_calls.items():
        lines.append("  {} -> {}: {}".format(k, " ".join(v["events"]), v["reason"]))
    lines.append("not decided: which runtime arm runs (handler-case, ignore-errors, when/unless),"
                 " loops beyond fnn-recover's barrier loop, what opaque or unmapped callbacks do,"
                 " file contents, OS semantics, that the image runs this source, callers.")
    bad = sum(len(r.mismatches) for r in report.programs)
    lines.append("result: {} ({} mismatches over {} programs)".format(
        "PASS" if report.ok else "FAIL", bad, len(report.programs)))
    return "\n".join(lines)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    report = check()
    if args.json:
        print(json.dumps(asdict(report), indent=2))
    else:
        print(render(report))
    return 0 if report.ok else 1


if __name__ == "__main__":
    sys.exit(main())
