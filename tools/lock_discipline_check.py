#!/usr/bin/env python3
"""tools/lock_discipline_check.py -- the host's lock, lease, thread and failure discipline.

The first landing of the whole-system plan (build/coordinator/decisions/
whole-system-correctness-2026-10-03.md section 10.5; Astra's round-2 section 4
and its decision D1).  It reads host/native/*.lisp with the ledger's
non-evaluating reader (tools/ledger.py `Reader'; nothing is interned, evaluated
or macro-expanded), builds a contextual call graph of the native host, follows
ACL2 core calls through the books' call graph into the raw realizers they
reach (attach-stobj and defabsstobj exports included), and reports each
finding with file:line, its rule and the path that reaches it.

THE BOUNDED CLAIM (Astra D1, stated exactly).  A clean report means: every
SITE THE CHECK ANALYZED matches the declarations in
tools/lock_discipline_contracts.json under the syntactic rules R1-R10 below,
and every site it could NOT analyze is listed as UNRESOLVED.  It does not mean
the host is free of races, deadlocks, leaks or swallowed faults: the analysis
is syntactic and path-insensitive (except the one `*fnn-extent-no-io*' branch
below), it trusts the declarations it is given (a declaration closes an
analysis gap, never the obligation to prove the declared contract), it
cannot see aliasing through data, computed calls or runtime callbacks it
cannot resolve, and it says nothing about liveness or time bounds.  It does
not establish "T2 on every hand-written line"; a schedule-level property (the
adopt-versus-stop race, B2/r71 F9) is reported only as a SHAPE (R8), never
proved absent.  Zero NEW findings is not zero findings: the report prints the
total, the baselined, the new, the unresolved and the declared exceptions
separately.

THE RULES (the deputy's numbering, reconciled with Astra's section 4):
  R1   owner (and every declared protected) state is touched only under its
       protector.  Region accessors (`fnn-live-arena', the guarded-by globals,
       declared struct slots) require their lock; a function that touches one
       without holding it lexically passes the requirement to its callers (a
       docstring "caller holds" is the same precondition, never an exemption);
       a requirement that reaches a thread root or a serving entry unmet is a
       finding with its path.  Startup/offline roots are a declared phase.
  R1b  cross-actor state with no consistent protector: a global or struct slot
       written from two actors under disjoint locksets, or written by one actor
       with no lock while another reads it, needs a publication row.
  R2   no blocking effect while a lock is held: every leaf is classified
       (io, await, sleep, runtime); a lock region whose closure reaches one,
       through host calls and through the ACL2 attachment closure of a core
       call (realizers: fn-durable-realize-*, fn-pgs-fill-*, fn-arena-stored),
       is refused unless the lock is declared io-ok or the site is a declared
       exception.  `(if *fnn-extent-no-io* A B)' is followed: under a dynamic
       binding of the flag to T only A runs (effect-sensitive, Astra D6).
  R3   every physical read names a row or a lease: `fnn-extent-pread' and
       `fnn-extent-window-pread' run either inside the extent-lock region that
       looked up their descriptor, or in a declared borrow whose protocol the
       check verifies (acquire before the read, release after it).
  R4   every thread is declared: its registry, its join site, its fault
       policy; the registered value is the make-thread result itself; a thread
       that removes itself from its registry does no shared work afterwards.
  R5   every nested lock edge is declared and the edges are acyclic; direct
       owner-mutex acquisitions outside the gate are a declared list.
  R6   dispatch administration (fnn-call up to the target invocation) takes no
       lock and touches no synchronized table except the declared caches.
  R7   failure scope: a handler that can consume a core fault or an
       indeterminate outcome must route it to the fence (re-signal, or reach
       `fnn-owner-stop-service-locked') unless its scope is declared private;
       a handler that routes to the fence must not also consume connection-local
       conditions (socket errors, refusals); a gated body that can signal a
       fault or indeterminate runs inside the shared-action boundary.
  R8   cross-lock handoff: a push into a declared hand-off queue must check the
       receiver's lifecycle under the receiving lock (shape only).
  R9   actor rules: an actor declared to enter no gate does not; an I/O loop
       does not park in an await; a :reader quantum does not reach the commit
       pipeline.
  R10  the host closes only descriptors it owns: an fnn-close is of a
       descriptor this function opened, or a declared close site; a close
       wrapped in ignore-errors is refused (an ambiguous close is swallowed).

OUTPUT: three categories -- VIOLATION, UNRESOLVED (the analysis could not
decide: an unknown macro that hides a primitive, a callback value, an
unknown lock object), EXCEPTION (a declared, justified scoped exception).

SCOPES: the ENCLAVE (contracts "enclave": functions whose discipline is
migrated) is strict: any violation or unresolved site there fails.  Outside
it the baseline tools/lock_discipline_baseline.json only shrinks: a finding
not in it is new; a baseline row no longer found must be removed
(--write-baseline, which refuses to add rows unless --initial).

    python3 tools/lock_discipline_check.py                 # report (exit 0)
    python3 tools/lock_discipline_check.py --check         # gate: enclave + baseline
    python3 tools/lock_discipline_check.py --json          # machine output
    python3 tools/lock_discipline_check.py --rule R3 -v    # one rule, with paths
    python3 tools/lock_discipline_check.py --root DIR      # another checkout (a pre-fix commit)
    python3 tools/lock_discipline_check.py --write-baseline [--initial]
    python3 tools/lock_discipline_check.py --emit-realization  # planning/host-realization.json
"""
from __future__ import annotations

import argparse
import bisect
import collections
import hashlib
import json
import os
import re
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402
from ledger import Sym  # noqa: E402

TOOL_ROOT = Path(__file__).resolve().parents[1]
CONTRACTS = TOOL_ROOT / "tools" / "lock_discipline_contracts.json"
BASELINE = TOOL_ROOT / "tools" / "lock_discipline_baseline.json"
REALIZATION = "planning/host-realization.json"

RULES = ("R1", "R1b", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10")


# --------------------------------------------------------------------------
# reading: the ledger's reader, with a line on every list
# --------------------------------------------------------------------------


class Node(list):
    """A read list that remembers the line it starts on."""

    __slots__ = ("line", "identity")


class SpanReader(ledger.Reader):
    def __init__(self, source: str) -> None:
        super().__init__(source)
        self._newlines = [i for i, c in enumerate(source) if c == "\n"]

    def line(self, position: int) -> int:
        return bisect.bisect_left(self._newlines, position) + 1

    def form(self):  # noqa: D401 - same contract as the ledger's
        self.skip_space()
        start = self.pos
        value = super().form()
        if isinstance(value, list) and not isinstance(value, Node):
            node = Node(value)
            node.line = self.line(start)
            return node
        return value


def symbols_of(forms) -> frozenset:
    out = set()
    stack = list(forms)
    while stack:
        x = stack.pop()
        if isinstance(x, Sym):
            out.add(str(x))
        elif isinstance(x, list):
            stack.extend(x)
    return frozenset(out)


def direct_symbols(forms) -> frozenset:
    """Symbols of FORMS outside the clauses of a nested handler-case or an
    ignore-errors (a fence called only for a NESTED failure does not route
    this clause's condition)."""
    out = set()
    stack = list(forms)
    while stack:
        x = stack.pop()
        if isinstance(x, Sym):
            out.add(str(x))
        elif isinstance(x, list):
            if head(x) == "handler-case":
                stack.extend(x[:2])
            elif head(x) == "ignore-errors":
                continue
            else:
                stack.extend(x)
    return frozenset(out)


def read_forms(text: str) -> list:
    return SpanReader(text).top_level()


def sym(x) -> str | None:
    return str(x) if isinstance(x, Sym) else None


def head(form) -> str | None:
    if isinstance(form, list) and form and isinstance(form[0], Sym):
        return str(form[0])
    return None


def line_of(form, default: int) -> int:
    return getattr(form, "line", default)


def quoted_symbol(form) -> str | None:
    if isinstance(form, list) and len(form) == 2 and head(form) == "quote" and isinstance(form[1], Sym):
        return str(form[1])
    return None


def render(form, limit: int = 80) -> str:
    def go(f):
        if isinstance(f, list):
            if head(f) == "quote" and len(f) == 2:
                return "'" + go(f[1])
            return "(" + " ".join(go(x) for x in f) + ")"
        if isinstance(f, str) and not isinstance(f, Sym):
            return json.dumps(f)
        return str(f)
    text = go(form)
    return text if len(text) <= limit else text[: limit - 3] + "..."


# --------------------------------------------------------------------------
# the tree's definitions
# --------------------------------------------------------------------------


@dataclass
class Def:
    name: str
    path: str
    line: int
    params: list
    body: list
    kind: str = "function"  # function | macro | lambda
    doc: str = ""
    loaded: bool = True


@dataclass
class Tree:
    root: Path
    defs: dict = field(default_factory=dict)          # name -> Def (functions)
    macros: dict = field(default_factory=dict)        # name -> Def
    structs: dict = field(default_factory=dict)       # accessor -> (struct, slot)
    globals: dict = field(default_factory=dict)       # name -> (path, line, guarded-by or None)
    synchronized: set = field(default_factory=set)    # globals holding :synchronized tables
    conditions: dict = field(default_factory=dict)    # name -> [parents]
    aliens: set = field(default_factory=set)          # define-alien-routine lisp names
    raw_replaced: set = field(default_factory=set)    # ACL2 names the host replaces
    files: dict = field(default_factory=dict)         # path -> loaded?
    unreadable: dict = field(default_factory=dict)
    sections: dict = field(default_factory=dict)      # def-section name -> (path, line, actors, classes, admits)


GUARDED = re.compile(r"guarded-by:\s*([^(;]+?)\s*(?:\(|\.\s|\.$|$)")


def loaded_native_files(root: Path) -> set[str]:
    found = set()
    for build in sorted((root / "host" / "native").glob("build*.lisp")):
        for m in re.finditer(r'\(load\s+"(host/native/[^"]+\.lisp)"', build.read_text(errors="replace")):
            found.add(m.group(1))
    return found


def lambda_params(lst) -> list[str]:
    out = []
    if not isinstance(lst, list):
        return out
    for item in lst:
        if isinstance(item, Sym):
            if not str(item).startswith("&"):
                out.append(str(item))
        elif isinstance(item, list) and item and isinstance(item[0], Sym):
            out.append(str(item[0]))
    return out


def identify_nodes(form, owner):
    """Lexical IDs survive formatting; distinct same-line lambdas stay distinct.

    Inserting/removing a lambda within a function can change its ordinals and is
    reviewed as a source change. Never alias unrelated callbacks by body text.
    """
    nodes = lambdas = 0
    stack = [form]
    while stack:
        item = stack.pop()
        if not isinstance(item, list):
            continue
        nodes += 1
        if head(item) == "lambda":
            lambdas += 1
            identity = f"{owner}#lambda{lambdas}"
        else:
            identity = f"{owner}#form{nodes}"
        if isinstance(item, Node):
            item.identity = identity
        stack.extend(reversed(item))


def collect_tree(root: Path, files: list[str] | None = None) -> Tree:
    tree = Tree(root=root)
    loaded = loaded_native_files(root)
    paths = files if files is not None else sorted(
        p.relative_to(root).as_posix() for p in (root / "host" / "native").glob("*.lisp"))
    for rel in paths:
        text = (root / rel).read_text(encoding="utf-8", errors="replace")
        tree.files[rel] = rel in loaded or files is not None
        try:
            forms = read_forms(text)
        except ledger.ReadError as exc:
            tree.unreadable[rel] = str(exc)
            continue
        lines = text.split("\n")
        for form, line in forms:
            visit_top(tree, form, line, rel, lines)
    return tree


# def-section (host/native/owner.lisp, lane WRAPPER): a declared owner section
# is a generated function.  The check reads the declaration and analyzes the
# function the macro emits, written here exactly as the macro's template
# writes it (tests/test_lock_discipline_check.py holds the two together).
SECTION_TEMPLATE = ("(defun {name} (service cid thunk &optional (class {default})) "
                    "({run} service class cid '{admits} '{classes} '{name} thunk))")


def _at_line(form, line: int):
    if isinstance(form, list):
        node = Node(_at_line(x, line) for x in form)
        node.line = line
        return node
    return form


def section_definition(form, line: int):
    """The defun a (def-section NAME :actors A :classes C :admits X) emits,
    and its declaration (actors, classes, admits)."""
    name = sym(form[1]) if len(form) > 1 else None
    keys = {}
    rest = list(form[2:])
    for k in range(0, len(rest) - 1, 2):
        if isinstance(rest[k], Sym):
            keys[str(rest[k])] = rest[k + 1]
    classes = keys.get(":classes")
    admits = keys.get(":admits")
    if not name or not isinstance(classes, list) or not classes or admits is None:
        return None, None
    runner = "fnn-section-run" if render(admits) == ":live" else "fnn-section-run-cleanup"
    text = SECTION_TEMPLATE.format(run=runner, name=name, default=render(classes[0], 10_000),
                                   admits=render(admits, 10_000),
                                   classes=render(classes, 10_000))
    defun = _at_line(read_forms(text)[0][0], line)
    actors = keys.get(":actors")
    decl = ([str(x) for x in actors] if isinstance(actors, list) else [],
            [str(x) for x in classes], render(admits, 200))
    return defun, decl


def visit_top(tree: Tree, form, line: int, rel: str, lines: list[str]) -> None:
    h = head(form)
    if h is None:
        return
    if h == "def-section":
        defun, decl = section_definition(form, line)
        if defun is not None:
            tree.sections[str(form[1])] = (rel, line) + decl
            visit_top(tree, defun, line, rel, lines)
        return
    if h in ("progn", "eval-when", "locally"):
        for sub in form[1:]:
            visit_top(tree, sub, line_of(sub, line), rel, lines)
        return
    if h in ("defun", "defmacro") and len(form) >= 3 and isinstance(form[1], Sym):
        name = str(form[1])
        identify_nodes(form, name)
        if name.startswith("acl2_*1*_acl2::"):
            tree.raw_replaced.add(name.split("::", 1)[1])
            return
        body = list(form[3:])
        doc = ""
        if len(body) > 1 and isinstance(body[0], str) and not isinstance(body[0], Sym):
            doc = body[0]
        d = Def(name, rel, line, form[2] if isinstance(form[2], list) else [], body,
                "macro" if h == "defmacro" else "function", doc, tree.files.get(rel, True))
        (tree.macros if h == "defmacro" else tree.defs)[name] = d
        return
    if h in ("defvar", "defparameter") and len(form) >= 2 and isinstance(form[1], Sym):
        name = str(form[1])
        guard = None
        # the annotation is a comment on the same line or the lines after it
        for k in range(line - 1, min(line + 2, len(lines))):
            m = GUARDED.search(lines[k])
            if m and (k == line - 1 or lines[k].lstrip().startswith(";")):
                guard = m.group(1).rstrip(".")
                break
            if k > line - 1 and lines[k].lstrip().startswith("("):
                break
        tree.globals[name] = (rel, line, guard)
        if len(form) >= 3 and isinstance(form[2], list) and head(form[2]) == "make-hash-table":
            if ":synchronized" in [str(x) for x in form[2] if isinstance(x, Sym)]:
                tree.synchronized.add(name)
        return
    if h == "defstruct" and len(form) >= 2:
        spec = form[1]
        sname = str(spec[0]) if isinstance(spec, list) else str(spec)
        conc = sname + "-"
        if isinstance(spec, list):
            for opt in spec[1:]:
                if isinstance(opt, list) and head(opt) == ":conc-name":
                    conc = (str(opt[1]) if len(opt) > 1 and opt[1] is not None else "")
                    if conc == "nil":
                        conc = ""
        for slot in form[2:]:
            sl = slot[0] if isinstance(slot, list) and slot else slot
            if isinstance(sl, Sym):
                tree.structs[conc + str(sl)] = (sname, str(sl))
        return
    if h == "define-condition" and len(form) >= 3 and isinstance(form[1], Sym):
        tree.conditions[str(form[1])] = [str(p) for p in form[2] if isinstance(p, Sym)] if isinstance(form[2], list) else []
        return
    if h == "sb-alien:define-alien-routine" and len(form) >= 2:
        spec = form[1]
        if isinstance(spec, list) and len(spec) >= 2 and isinstance(spec[1], Sym):
            tree.aliens.add(str(spec[1]))
        elif isinstance(spec, Sym):
            tree.aliens.add(str(spec))
        return


# --------------------------------------------------------------------------
# the ACL2 side: which core subjects reach a raw realizer
# --------------------------------------------------------------------------


def acl2_realizer_reach(root: Path, realizers: set[str]) -> dict[str, dict[str, str]]:
    """subject -> {realizer: next-hop} for every ACL2 name whose closure reaches
    a host-replaced realizer.  Edges are the callgraph's MENTIONS over books/
    and host/*.lisp, plus defabsstobj export -> :exec and attach-stobj
    generic export -> attached export (position-wise)."""
    import callgraph  # noqa: E402  (same directory)
    saved = callgraph.ROOT
    files = []
    for directory in ("books", "host"):
        for path in sorted((root / directory).glob("*.lisp")):
            files.append((path, path.relative_to(root).as_posix()))
    definitions: dict[str, list] = collections.defaultdict(list)
    absstobj_exports: dict[str, list] = {}
    attachments: list = []
    for path, rel in files:
        found, error = callgraph.read_file(path, rel)
        for d in found:
            definitions[d.name].append(d.form)
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        if "defabsstobj" in text or "attach-stobj" in text:
            try:
                forms = ledger.Reader(text).top_level()
            except ledger.ReadError:
                continue
            for form, _ in forms:
                if head(form) == "defabsstobj" and len(form) > 2:
                    items = list(form[2:])
                    for k, item in enumerate(items):
                        if isinstance(item, Sym) and str(item) == ":exports" and k + 1 < len(items):
                            rows = []
                            for row in items[k + 1]:
                                if isinstance(row, list) and row and isinstance(row[0], Sym):
                                    plist = {str(row[i]): row[i + 1] for i in range(1, len(row) - 1, 2)
                                             if isinstance(row[i], Sym)}
                                    rows.append((str(row[0]), sym(plist.get(":exec"))))
                            absstobj_exports[str(form[1])] = rows
                elif head(form) == "attach-stobj" and len(form) == 3:
                    attachments.append((str(form[1]), str(form[2])))
    callgraph.ROOT = saved
    edges: dict[str, set] = collections.defaultdict(set)
    known = set(definitions)
    for rows in absstobj_exports.values():
        for export, ex in rows:
            known.add(export)
            if ex:
                known.add(ex)
                edges[export].add(ex)
    for generic, impl in attachments:
        for (g, _), (i, iex) in zip(absstobj_exports.get(generic, []), absstobj_exports.get(impl, [])):
            edges[g].add(i)
            if iex:
                edges[g].add(iex)
    known |= realizers
    for name, forms in definitions.items():
        mentioned: set[str] = set()
        for f in forms:
            callgraph.symbols(executable_part(f[2:]), mentioned)
        edges[name] |= (mentioned & known) - {name}
    backwards: dict[str, set] = collections.defaultdict(set)
    for a, bs in edges.items():
        for b in bs:
            backwards[b].add(a)
    reach = Reach()
    for r in realizers:
        reach.setdefault(r, {})[r] = r
        frontier = [r]
        seen = {r}
        while frontier:
            nxt = []
            for n in frontier:
                for p in backwards.get(n, ()):
                    if p not in seen and p not in realizers:
                        seen.add(p)
                        reach.setdefault(p, {})[r] = n
                        nxt.append(p)
            frontier = nxt
    reach.known = known  # type: ignore[attr-defined]
    return reach


class Reach(dict):
    """subject -> {realizer: next hop}; .known: every ACL2 name read."""
    known: set = set()


def executable_part(form):
    """FORM without what raw execution never runs: `declare' (guards, xargs)
    and the :logic half of an `mbe'."""
    if isinstance(form, list):
        h = head(form)
        if h == "declare":
            return []
        if h == "mbe":
            for k in range(1, len(form) - 1):
                if isinstance(form[k], Sym) and str(form[k]) == ":exec":
                    return executable_part(form[k + 1])
        return [executable_part(x) for x in form]
    return form


def acl2_path(reach: dict, subject: str, realizer: str, limit: int = 12) -> list[str]:
    path = [subject]
    cur = subject
    while cur != realizer and len(path) < limit:
        cur = reach.get(cur, {}).get(realizer)
        if cur is None:
            break
        path.append(cur)
    return path


# --------------------------------------------------------------------------
# contracts
# --------------------------------------------------------------------------


@dataclass
class Contracts:
    raw: dict

    def __getattr__(self, key):
        try:
            return self.raw[key]
        except KeyError as exc:
            raise AttributeError(key) from exc


def load_contracts(path: Path) -> Contracts:
    raw = json.loads(path.read_text())
    return Contracts(raw)


# --------------------------------------------------------------------------
# the walk
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Ctx:
    locks: frozenset = frozenset()
    noio: bool | None = None          # None: unbound (may be either)
    scope: str | None = None          # "shared" inside the fence boundary
    gated: str | None = None          # gate class of the innermost gated body
    ignore: bool = False              # inside ignore-errors


@dataclass
class Event:
    kind: str
    name: str
    line: int
    ctx: Ctx
    extra: object = None


@dataclass
class FnInfo:
    name: str
    path: str
    line: int
    loaded: bool
    events: list = field(default_factory=list)
    handlers: list = field(default_factory=list)   # (line, protected SigX, clauses, ctx)
    gated: list = field(default_factory=list)      # (line, class form, body SigX, ctx)
    sig: object = None                             # SigX of the whole body
    thread_of: tuple | None = None                 # (creator, line, name) for a thread root
    params: list = field(default_factory=list)


# SigX: a small expression for the conditions a form can signal.
#   ("u", leaves:frozenset, calls:tuple, parts:tuple)
#   ("h", protected, clauses)  clauses: [(types:tuple, rethrows:bool, body SigX)]
EMPTY_SIG = ("u", frozenset(), (), ())


def sig_union(parts) -> tuple:
    leaves: set = set()
    calls: list = []
    subs: list = []
    for p in parts:
        if p is None or p == EMPTY_SIG:
            continue
        if p[0] == "u":
            leaves |= p[1]
            calls.extend(p[2])
            subs.extend(p[3])
        else:
            subs.append(p)
    if not leaves and not calls and not subs:
        return EMPTY_SIG
    return ("u", frozenset(leaves), tuple(dict.fromkeys(calls)), tuple(subs))


SIG_CLASSES = ("fault", "indet", "refusal", "os", "socket", "connection", "other")
CLASS_TYPE = {"fault": "fnn-store-fault", "indet": "fnn-store-indeterminate",
              "refusal": "fnn-store-error", "os": "fnn-os-error",
              "socket": "sb-bsd-sockets:socket-error", "connection": "fnn-owner-connection-fault",
              "other": "simple-error"}
BUILTIN_PARENTS = {"error": ["serious-condition"], "serious-condition": ["condition"],
                   "storage-condition": ["serious-condition"], "warning": ["condition"],
                   "simple-error": ["error"], "type-error": ["error"], "stream-error": ["error"],
                   "end-of-file": ["stream-error"], "sb-bsd-sockets:socket-error": ["error"],
                   "sb-posix:syscall-error": ["error"], "sb-int:simple-stream-error": ["stream-error"],
                   "fnn-tls-error": ["error"], "condition": [], "t": []}


SPECIAL_SKIP = {"declare", "quote", "go", "the-environment"}
BINDING_FORMS = {"let", "let*", "sb-int:dx-let"}
FUNCALLERS = {"funcall", "apply", "multiple-value-call"}
SYNC_HOFS = {"mapc", "mapcar", "mapcan", "maplist", "mapl", "mapcon", "maphash", "remove-if",
             "remove-if-not", "delete-if", "delete-if-not", "find-if", "find-if-not", "position-if",
             "count-if", "some", "every", "notany", "notevery", "sort", "stable-sort", "reduce",
             "member-if", "assoc-if", "rassoc-if", "remove", "delete", "find", "position", "member",
             "assoc", "count", "subst-if", "handler-bind", "funcall", "apply", "map", "map-into",
             "sb-ext:with-timeout", "fnn-owner-measured"}
STORE_HOFS = {"push", "pushnew", "setf", "setq", "list", "list*", "cons", "vector", "acons", "values"}
WRITE_FORMS = {"setq", "setf", "psetf", "psetq", "incf", "decf", "push", "pushnew", "pop", "remf"}


class Analyzer:
    def __init__(self, tree: Tree, contracts: Contracts, realizer_reach: dict) -> None:
        self.tree = tree
        self.c = contracts
        self.reach = realizer_reach
        self.infos: dict[str, FnInfo] = {}
        self.lock_patterns = []
        for lock, row in contracts.locks.items():
            for m in row["match"]:
                self.lock_patterns.append((m, lock))
        self.templates = set(contracts.raw.get("expand_templates", []))
        self.unknown_macros = self._macros_hiding_primitives()
        self.param_ctx: dict = {}     # (fn, param) -> Ctx (the context its funcall runs in) | "async"
        self.leaf_kinds = self._leaf_table()
        self.region_of = {}
        for region, row in contracts.regions.items():
            for acc in row.get("accessors", []):
                self.region_of[acc] = row["lock"]
        for name, (path, line, guard) in tree.globals.items():
            if guard:
                lock = self.resolve_guard(guard)
                if lock:
                    self.region_of[name] = lock
        self.write_regions = {}
        for region, row in contracts.regions.items():
            for g in row.get("write_globals", []):
                self.write_regions[g] = row["lock"]
                self.region_of[g] = row["lock"]
        for acc, lock in contracts.raw.get("slots", {}).items():
            self.region_of[acc] = lock["lock"] if isinstance(lock, dict) else lock

    # -- tables ------------------------------------------------------------
    def resolve_guard(self, text: str) -> str | None:
        for lock, row in self.c.locks.items():
            if text in row.get("guard_names", []) or text in row["match"]:
                return lock
        return None

    def _leaf_table(self) -> dict:
        table = {}
        for kind, names in self.c.leaves.items():
            for n in names:
                table[n] = kind
        return table

    def leaf_kind(self, name: str) -> str | None:
        if name in self.leaf_kinds:
            return self.leaf_kinds[name]
        if name in self.tree.defs:
            return None
        if name in self.tree.aliens:
            return None  # an FFI compute routine unless the leaf table names it
        for prefix, kind in self.c.leaf_prefixes.items():
            if name.startswith(prefix):
                if name in self.c.raw.get("pure_externals", []):
                    return None
                return kind
        return None

    def _macros_hiding_primitives(self) -> set:
        prims = {"sb-thread:with-mutex", "sb-thread:with-recursive-lock", "handler-case",
                 "handler-bind", "ignore-errors", "sb-thread:make-thread", "sb-thread:condition-wait",
                 "unwind-protect", "sb-thread:grab-mutex"}
        hidden = set()
        for name, d in self.tree.macros.items():
            found: set = set()
            stack = list(d.body)
            while stack:
                x = stack.pop()
                if isinstance(x, Sym) and str(x) in prims:
                    found.add(str(x))
                elif isinstance(x, list):
                    stack.extend(x)
            if found and name not in self.templates:
                hidden.add(name)
        return hidden

    def lock_of(self, expr, env: dict) -> str:
        for _ in range(3):
            if isinstance(expr, Sym) and str(expr) in env and env[str(expr)] is not None:
                expr = env[str(expr)]
            else:
                break
        if isinstance(expr, Sym):
            key = str(expr)
        elif head(expr):
            key = "(" + head(expr) + ")"
        else:
            key = render(expr)
        for m, lock in self.lock_patterns:
            if m == key:
                return lock
        return "?" + key

    # -- macro templates (declared wrappers only) ----------------------------
    def expand(self, form, d: Def):
        """Substitute FORM's arguments into D's backquote template.  Nothing is
        evaluated: an unquote of a macro parameter becomes the argument form, any
        other unquote an opaque symbol."""
        binding: dict = {}

        def bind(pattern, value):
            if isinstance(pattern, Sym):
                binding[str(pattern)] = ("one", value)
                return
            if not isinstance(pattern, list):
                return
            vals = list(value) if isinstance(value, list) else []
            mode = None
            i = 0
            for p in pattern:
                ps = sym(p)
                if ps in ("&body", "&rest"):
                    mode = "rest"
                    continue
                if ps == "&optional":
                    mode = "opt"
                    continue
                if ps == "&key":
                    mode = "key"
                    continue
                if mode == "rest":
                    binding[ps] = ("many", vals[i:])
                    i = len(vals)
                    continue
                if mode == "key":
                    # a keyword argument binds by its name, wherever it stands
                    kname = sym(p[0]) if isinstance(p, list) and p else ps
                    kval = Sym("nil")
                    for k in range(i, len(vals) - 1, 2):
                        if sym(vals[k]) == ":" + str(kname):
                            kval = vals[k + 1]
                            break
                    binding[str(kname)] = ("one", kval)
                    continue
                if isinstance(p, list) and mode == "opt":
                    p = p[0]
                bind(p, vals[i] if i < len(vals) else Sym("nil"))
                i += 1
        bind(d.params, form[1:])
        template = None
        stack = list(d.body)
        while stack:
            x = stack.pop()
            if isinstance(x, list) and head(x) == "quasiquote":
                template = x[1]
                break
            if isinstance(x, list):
                stack.extend(reversed(x))
        if template is None:
            return None

        def sub(t):
            if isinstance(t, list):
                h = head(t)
                if h == "unquote" and len(t) == 2:
                    if isinstance(t[1], Sym) and str(t[1]) in binding and binding[str(t[1])][0] == "one":
                        return binding[str(t[1])][1]
                    return Sym("#:opaque")
                out = Node()
                out.line = getattr(form, "line", 0)
                out.identity = (getattr(form, "identity", self.cur.name) + "::" + d.name
                                + "::" + getattr(t, "identity", "template"))
                for item in t:
                    if isinstance(item, list) and head(item) == "unquote-splicing" and len(item) == 2:
                        name = sym(item[1])
                        if name in binding and binding[name][0] == "many":
                            if d.name in self.c.raw.get("gated_macros", {}) and name == "body":
                                marker = Node([Sym("%gated-body")] + list(binding[name][1]))
                                marker.line = getattr(form, "line", 0)
                                out.append(marker)
                            else:
                                out.extend(binding[name][1])
                        continue
                    out.append(sub(item))
                return out
            return t
        return sub(template)

    # -- walking -----------------------------------------------------------
    def analyze(self) -> None:
        # pass 1: how each function runs the callables its parameters hold
        for name, d in self.tree.defs.items():
            self.top_name = name
            self.walk_def(name, d, record=False)
        self.solve_param_ctx()
        self.infos = {}
        self.lambda_count = 0
        for name, d in self.tree.defs.items():
            self.top_name = name
            self.walk_def(name, d, record=True)

    def walk_def(self, name: str, d: Def, record: bool, ctx: Ctx | None = None,
                 thread_of=None, env=None) -> FnInfo:
        info = FnInfo(name, d.path, d.line, d.loaded, params=lambda_params(d.params))
        info.thread_of = thread_of
        self.cur = info
        self.recording = record
        if not record:
            self.pass1_name = name
        env = dict(env or {})
        for p in info.params:
            env[p] = None
        parts = []
        body = d.body
        if body and isinstance(body[0], str) and not isinstance(body[0], Sym) and len(body) > 1:
            body = body[1:]
        for f in body:
            parts.append(self.walk(f, ctx or Ctx(), env, d.line))
        info.sig = sig_union(parts)
        if record:
            # a template that splices its body twice (fnn-owner-measured's two
            # branches) walks the same source twice: keep one of each
            seen = set()
            unique = []
            for e in info.events:
                k = (e.kind, e.name, e.line, e.ctx, render(e.extra, 200) if isinstance(e.extra, list) else repr(e.extra))
                if k not in seen:
                    seen.add(k)
                    unique.append(e)
            info.events = unique
            hs = {}
            for h in info.handlers:
                hs.setdefault((h[0], tuple(c[4] for c in h[2]), h[3]), h)
            info.handlers = list(hs.values())
            gs = {}
            for g in info.gated:
                gs.setdefault((g[0], g[1], g[3]), g)
            info.gated = list(gs.values())
            self.infos[name] = info
        return info

    def ev(self, kind, name, line, ctx, extra=None):
        if self.recording:
            self.cur.events.append(Event(kind, name, line, ctx, extra))

    def walk_body(self, forms, ctx, env, line):
        return sig_union([self.walk(f, ctx, env, line_of(f, line)) for f in forms])

    def walk(self, form, ctx: Ctx, env: dict, line: int):
        if isinstance(form, Sym):
            name = str(form)
            if name in self.tree.globals and name not in env:
                self.ev("acc", name, line, ctx, "r")
            return EMPTY_SIG
        if not isinstance(form, list) or not form:
            return EMPTY_SIG
        line = line_of(form, line)
        h = head(form)
        if h is None:
            if isinstance(form[0], list) and head(form[0]) == "lambda":
                return sig_union([self.walk_lambda_inline(form[0], ctx, env, line)] +
                                 [self.walk(a, ctx, env, line) for a in form[1:]])
            return self.walk_body(form, ctx, env, line)
        if h in SPECIAL_SKIP:
            return EMPTY_SIG
        if h == "function":
            target = sym(form[1]) if len(form) > 1 else None
            if target and target in self.tree.defs:
                self.ev("call", target, line, ctx, "ref")
                return ("u", frozenset(), (target,), ())
            if len(form) > 1 and head(form[1]) == "lambda":
                return self.walk_stored_lambda(form[1], ctx, env, line)
            return EMPTY_SIG
        if h == "lambda":
            # a lambda in a VALUE position (stored, bound, returned): it runs
            # later, in whatever context calls it -- a fresh lockset
            return self.walk_stored_lambda(form, ctx, env, line)
        if h == "%gated-body":
            return self.walk_gated_body(form, ctx, env, line)
        if h in BINDING_FORMS or h in ("multiple-value-bind", "destructuring-bind", "symbol-macrolet"):
            return self.walk_binding(form, h, ctx, env, line)
        if h in ("flet", "labels", "macrolet"):
            env2 = dict(env)
            parts = []
            for fdef in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
                if isinstance(fdef, list) and len(fdef) >= 2:
                    e3 = dict(env2)
                    for p in lambda_params(fdef[1]):
                        e3[p] = None
                    parts.append(self.walk_body(fdef[2:], ctx, e3, line))
            parts.append(self.walk_body(form[2:], ctx, env2, line))
            return sig_union(parts)
        if h in ("dolist", "dotimes", "do-symbols"):
            spec = form[1] if len(form) > 1 else []
            env2 = dict(env)
            parts = []
            if isinstance(spec, list) and spec:
                env2[str(spec[0])] = None
                parts.extend(self.walk(x, ctx, env, line) for x in spec[1:])
            parts.append(self.walk_body(form[2:], ctx, env2, line))
            return sig_union(parts)
        if h in ("do", "do*"):
            env2 = dict(env)
            parts = []
            for v in (form[1] if isinstance(form[1], list) else []):
                if isinstance(v, list) and v:
                    env2[str(v[0])] = None
                    parts.extend(self.walk(x, ctx, env, line) for x in v[1:])
            parts.append(self.walk_body(form[2:], ctx, env2, line))
            return sig_union(parts)
        if h in ("cond",):
            return sig_union([self.walk_body(cl, ctx, env, line) for cl in form[1:] if isinstance(cl, list)])
        if h in ("case", "ecase", "ccase", "typecase", "etypecase", "ctypecase"):
            parts = [self.walk(form[1], ctx, env, line)] if len(form) > 1 else []
            for cl in form[2:]:
                if isinstance(cl, list) and cl:
                    parts.append(self.walk_body(cl[1:], ctx, env, line))
            return sig_union(parts)
        if h == "if":
            return self.walk_if(form, ctx, env, line)
        if h == "handler-case":
            return self.walk_handler_case(form, ctx, env, line)
        if h == "ignore-errors":
            inner = self.walk_body(form[1:], Ctx(ctx.locks, ctx.noio, ctx.scope, ctx.gated, True), env, line)
            self.add_handler(line, inner, [(("error",), False, EMPTY_SIG, frozenset(), "ignore-errors")], ctx)
            return ("h", inner, ((("error",), False, EMPTY_SIG),))
        if h == "handler-bind":
            parts = []
            for b in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
                if isinstance(b, list) and len(b) >= 2:
                    parts.append(self.walk(b[1], ctx, env, line))
            parts.append(self.walk_body(form[2:], ctx, env, line))
            return sig_union(parts)
        if h in ("sb-thread:with-mutex", "sb-thread:with-recursive-lock"):
            return self.walk_with_lock(form, ctx, env, line)
        if h == "sb-thread:make-thread":
            return self.walk_make_thread(form, ctx, env, line)
        if h == "sb-thread:condition-wait":
            lock = self.lock_of(form[2], env) if len(form) > 2 else "?"
            self.ev("leaf", "sb-thread:condition-wait", line, ctx, ("await", lock))
            return self.walk_body(form[1:], ctx, env, line)
        if h in ("sb-thread:grab-mutex",):
            lock = self.lock_of(form[1], env) if len(form) > 1 else "?"
            self.ev("acq", lock, line, ctx, "grab")
            self.ev("unresolved", "manual grab-mutex of " + lock, line, ctx)
            return EMPTY_SIG
        if h in ("error", "signal", "cerror", "warn", "sb-int:bug"):
            return self.walk_signal(form, ctx, env, line)
        if h in WRITE_FORMS:
            return self.walk_write(form, h, ctx, env, line)
        if h == "loop":
            return self.walk_loop(form, ctx, env, line)
        if h in ("block", "return-from", "catch", "throw", "the", "tagbody", "progv"):
            start = 2 if h in ("block", "return-from", "the") else 1
            return self.walk_body(form[start:], ctx, env, line)
        if h in self.tree.macros:
            return self.walk_macro_use(form, h, ctx, env, line)
        return self.walk_call(form, h, ctx, env, line)

    def walk_stored_lambda(self, lam, ctx, env, line):
        rid = self.spawn_lambda(lam, line, None, env)
        self.ev("async", rid, line, ctx, "stored")
        return EMPTY_SIG

    def walk_lambda_inline(self, lam, ctx, env, line):
        env2 = dict(env)
        for p in lambda_params(lam[1] if len(lam) > 1 else []):
            env2[p] = None
        return self.walk_body(lam[2:], ctx, env2, line_of(lam, line))

    def walk_binding(self, form, h, ctx, env, line):
        env2 = dict(env)
        parts = []
        noio = ctx.noio
        if h in BINDING_FORMS:
            for b in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
                if isinstance(b, list) and b:
                    name = str(b[0])
                    init = b[1] if len(b) > 1 else None
                    parts.append(self.walk(init, ctx if h != "let*" else Ctx(ctx.locks, noio, ctx.scope, ctx.gated, ctx.ignore), env2 if h == "let*" else env, line))
                    if name == "*fnn-extent-no-io*":
                        noio = not (init is None or (isinstance(init, Sym) and str(init) == "nil"))
                    elif name.startswith("*") and name in self.tree.globals:
                        pass
                    else:
                        env2[name] = init
                elif isinstance(b, Sym):
                    env2[str(b)] = None
            body = form[2:]
        else:
            vars_ = form[1] if len(form) > 1 else []
            for v in (lambda_params(vars_) if isinstance(vars_, list) else []):
                env2[v] = None
            if len(form) > 2:
                parts.append(self.walk(form[2], ctx, env, line))
            body = form[3:]
        ctx2 = Ctx(ctx.locks, noio, ctx.scope, ctx.gated, ctx.ignore)
        parts.append(self.walk_body(body, ctx2, env2, line))
        return sig_union(parts)

    def walk_if(self, form, ctx, env, line):
        test = form[1] if len(form) > 1 else None
        if isinstance(test, Sym) and str(test) == "*fnn-extent-no-io*":
            parts = []
            if ctx.noio is not False and len(form) > 2:
                parts.append(self.walk(form[2], Ctx(ctx.locks, True, ctx.scope, ctx.gated, ctx.ignore), env, line))
            if ctx.noio is not True and len(form) > 3:
                parts.append(self.walk_body(form[3:], Ctx(ctx.locks, False, ctx.scope, ctx.gated, ctx.ignore), env, line))
            return sig_union(parts)
        return self.walk_body(form[1:], ctx, env, line)

    def walk_loop(self, form, ctx, env, line):
        env2 = dict(env)
        items = list(form[1:])
        for k, x in enumerate(items):
            if isinstance(x, Sym) and str(x) in ("for", "with", "as") and k + 1 < len(items):
                v = items[k + 1]
                for name in (lambda_params(v) if isinstance(v, list) else [str(v)]):
                    env2[name] = None
        return sig_union([self.walk(x, ctx, env2, line) for x in items if isinstance(x, list)])

    def walk_signal(self, form, ctx, env, line):
        arg = form[1] if len(form) > 1 else None
        parts = [self.walk_body(form[2:], ctx, env, line)]
        q = quoted_symbol(arg)
        if q:
            self.ev("signal", q, line, ctx)
            return sig_union(parts + [("u", frozenset([("type", q)]), (), ())])
        if isinstance(arg, str) and not isinstance(arg, Sym):
            return sig_union(parts + [("u", frozenset([("type", "simple-error")]), (), ())])
        if isinstance(arg, Sym):
            return sig_union(parts + [("u", frozenset([("rethrow", str(arg))]), (), ())])
        parts.append(self.walk(arg, ctx, env, line))
        return sig_union(parts + [("u", frozenset([("type", "error")]), (), ())])

    def walk_write(self, form, h, ctx, env, line):
        parts = []
        if h in ("setq", "setf", "psetf", "psetq"):
            pairs = form[1:]
            for k in range(0, len(pairs) - 1, 2):
                parts.append(self.note_place(pairs[k], ctx, env, line, value=pairs[k + 1]))
                parts.append(self.walk(pairs[k + 1], ctx, env, line))
            return sig_union(parts)
        if h in ("push", "pushnew"):
            if len(form) > 2:
                parts.append(self.walk(form[1], ctx, env, line))
                parts.append(self.note_place(form[2], ctx, env, line, pushed=form[1]))
                parts.extend(self.walk(x, ctx, env, line) for x in form[3:])
            return sig_union(parts)
        if len(form) > 1:
            parts.append(self.note_place(form[1], ctx, env, line))
            parts.extend(self.walk(x, ctx, env, line) for x in form[2:])
        return sig_union(parts)

    def note_place(self, place, ctx, env, line, value=None, pushed=None):
        if isinstance(place, Sym):
            name = str(place)
            if name in self.write_regions and name not in env:
                self.ev("acc", name, line, ctx, "w")
            elif name in self.tree.globals and name not in env:
                self.ev("acc", name, line, ctx, "w")
            elif name in env and value is not None:
                env[name] = value
            return EMPTY_SIG
        if isinstance(place, list) and place:
            h = head(place)
            if h in self.tree.structs or h in self.region_of:
                self.ev("acc", h, line, ctx, "w")
                if pushed is not None:
                    self.ev("push", h, line, ctx, pushed)
                return self.walk_body(place[1:], ctx, env, line)
            if h in ("gethash", "svref", "aref", "car", "cdr", "first", "second", "third", "nth",
                     "getf", "slot-value", "elt", "cadr", "cddr", "rest", "fourth", "fifth"):
                parts = []
                for x in place[1:]:
                    if isinstance(x, Sym) and str(x) in self.tree.globals and str(x) not in env:
                        self.ev("acc", str(x), line, ctx, "w")
                    elif isinstance(x, list) and (head(x) in self.tree.structs):
                        self.ev("acc", head(x), line, ctx, "w")
                        parts.append(self.walk_body(x[1:], ctx, env, line))
                    else:
                        parts.append(self.walk(x, ctx, env, line))
                return sig_union(parts)
            return self.walk(place, ctx, env, line)
        return EMPTY_SIG

    def walk_with_lock(self, form, ctx, env, line):
        spec = form[1] if len(form) > 1 else []
        lockexpr = spec[0] if isinstance(spec, list) and spec else spec
        lock = self.lock_of(lockexpr, env)
        self.ev("acq", lock, line, ctx, head(form))
        if lock.startswith("?"):
            self.ev("unresolved", "lock object " + lock[1:], line, ctx)
        inner = Ctx(ctx.locks | {lock}, ctx.noio, ctx.scope, ctx.gated, ctx.ignore)
        return self.walk_body(form[2:], inner, env, line)

    def walk_gated_body(self, form, ctx, env, line):
        cls = self.gate_class
        inner = Ctx(ctx.locks, ctx.noio, None, cls, ctx.ignore)
        sig = self.walk_body(form[1:], inner, env, line)
        # a gated macro declared "fenced" wraps its body in the shared-action
        # boundary by its own template (fnn-section-envelope): the body runs
        # inside the fence by construction, not by what it calls.
        if self.recording and not getattr(self, "gate_fenced", False):
            self.cur.gated.append((line, cls, sig, ctx))
        return sig

    def walk_make_thread(self, form, ctx, env, line):
        fn = form[1] if len(form) > 1 else None
        tname = None
        for k in range(2, len(form) - 1):
            if isinstance(form[k], Sym) and str(form[k]) == ":name":
                tname = form[k + 1] if isinstance(form[k + 1], str) else render(form[k + 1])
        self.ev("leaf", "sb-thread:make-thread", line, ctx, ("runtime", None))
        creator = self.cur
        if isinstance(fn, list) and head(fn) == "lambda":
            rid = self.spawn_lambda(fn, line, (creator.name, line, tname), env)
            self.ev("thread", rid, line, ctx, tname)
        elif isinstance(fn, list) and head(fn) == "function" and sym(fn[1]) in self.tree.defs:
            rid = "thread:" + sym(fn[1]) + "@" + creator.path + ":" + getattr(form, "identity", creator.name)
            if self.recording:
                lam = Def(rid, creator.path, line, [], [Node([fn[1]])], "lambda", "", creator.loaded)
                lam.body[0].line = line
                saved = (self.cur, self.recording)
                info = self.walk_def(rid, lam, True, thread_of=(creator.name, line, tname))
                self.cur, self.recording = saved
            self.ev("thread", rid, line, ctx, tname)
        else:
            self.ev("unresolved", "make-thread of a computed function " + render(fn, 40), line, ctx)
        return EMPTY_SIG

    def spawn_lambda(self, lam, line, thread_of, env):
        identity = getattr(lam, "identity", None)
        if identity is None:
            raise ValueError(f"lambda lacks a lexical identity at {self.cur.path}:{line_of(lam, line)}")
        rid = "lambda@" + self.cur.path + ":" + identity

        if not self.recording:
            return rid
        d = Def(rid, self.cur.path, line_of(lam, line), lam[1] if len(lam) > 1 else [], list(lam[2:]),
                "lambda", "", self.cur.loaded)
        saved = (self.cur, self.recording, getattr(self, "gate_class", None))
        self.walk_def(rid, d, True, thread_of=thread_of, env={k: None for k in env})
        self.cur, self.recording, self.gate_class = saved
        return rid

    def walk_handler_case(self, form, ctx, env, line):
        inner = self.walk(form[1], ctx, env, line) if len(form) > 1 else EMPTY_SIG
        clauses = []
        recorded = []
        for cl in form[2:]:
            if not (isinstance(cl, list) and cl):
                continue
            tspec = cl[0]
            if isinstance(tspec, list) and head(tspec) == "or":
                types = tuple(str(x) for x in tspec[1:])
            elif isinstance(tspec, Sym):
                types = (str(tspec),)
            else:
                types = ("t",)
            if types == (":no-error",):
                clauses.append((types, False, self.walk_body(cl[2:], ctx, env, line)))
                continue
            var = None
            if len(cl) > 1 and isinstance(cl[1], list) and cl[1] and isinstance(cl[1][0], Sym):
                var = str(cl[1][0])
            env2 = dict(env)
            if var:
                env2[var] = None
            body = self.walk_body(cl[2:], ctx, env2, line_of(cl, line))
            rethrows = False
            if var:
                for leaf in body[1] if body[0] == "u" else ():
                    if leaf == ("rethrow", var):
                        rethrows = True
                # a rethrow nested deeper (inside a let/when) is still a rethrow
                if not rethrows:
                    rethrows = self.mentions_rethrow(cl[2:], var)
            clauses.append((types, rethrows, body))
            recorded.append((types, rethrows, body, direct_symbols(cl[2:]), render(tspec, 60)))
        self.add_handler(line, inner, recorded, ctx)
        return ("h", inner, tuple(clauses))

    @staticmethod
    def mentions_rethrow(forms, var) -> bool:
        stack = list(forms)
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                if head(x) in ("error", "signal") and len(x) == 2 and sym(x[1]) == var:
                    return True
                stack.extend(x)
        return False

    def add_handler(self, line, inner, clauses, ctx):
        if self.recording:
            self.cur.handlers.append((line, inner, clauses, ctx))

    def walk_macro_use(self, form, h, ctx, env, line):
        d = self.tree.macros[h]
        if h in self.templates:
            gated = self.c.raw.get("gated_macros", {}).get(h)
            expansion = self.expand(form, d)
            if expansion is None:
                self.ev("unresolved", "declared template macro " + h + " has no template", line, ctx)
                return self.walk_body(form[1:], ctx, env, line)
            saved = getattr(self, "gate_class", None)
            saved_fenced = getattr(self, "gate_fenced", False)
            if gated:
                self.gate_class = self.class_value(form, gated, env)
                self.gate_fenced = bool(gated.get("fenced"))
                self.ev("gate", h, line, ctx, self.gate_class)
            sig = self.walk(expansion, ctx, env, line)
            self.gate_class = saved
            self.gate_fenced = saved_fenced
            return sig
        if h in self.unknown_macros:
            self.ev("unresolved", "macro " + h + " hides a synchronization or handler primitive", line, ctx)
        return self.walk_body(form[1:], ctx, env, line)

    def class_value(self, form, gated: dict, env) -> str:
        spec = form[1] if len(form) > 1 else None
        val = None
        if isinstance(spec, list) and len(spec) > gated.get("class_position", 1):
            val = spec[gated.get("class_position", 1)]
        if isinstance(val, Sym) and str(val).startswith(":"):
            return str(val)
        if isinstance(val, Sym):
            return "$" + str(val)
        return "?"

    def walk_call(self, form, h, ctx, env, line):
        args = form[1:]
        parts = []
        # an ACL2 core call: a quoted subject in first position
        subject = quoted_symbol(args[0]) if args else None
        if subject and (h in self.c.core_callers or subject in self.reach):
            self.ev("core", subject, line, ctx, h)
        kind = self.leaf_kind(h)
        if kind:
            self.ev("leaf", h, line, ctx, (kind, args[0] if args else None))
            if kind in ("io", "socket"):
                parts.append(("u", frozenset([("class", "socket" if kind == "socket" else "os")]), (), ()))
        if h in self.region_of and h not in self.tree.globals:
            self.ev("acc", h, line, ctx, "r")
        elif h in self.tree.structs:
            self.ev("acc", h, line, ctx, "r")
        if h in FUNCALLERS and args:
            target = args[0]
            if isinstance(target, Sym) and str(target) in env:
                pname = str(target)
                if not self.recording and pname in self.cur.params:
                    self.param_sites.setdefault((self.pass1_name, pname), []).append(("run", ctx))
                elif self.recording and pname not in self.cur.params:
                    self.ev("callback", pname, line, ctx)
                elif self.recording:
                    self.ev("callback-param", pname, line, ctx)
            elif quoted_symbol(target) and quoted_symbol(target) in self.tree.defs:
                self.ev("call", quoted_symbol(target), line, ctx, "funcall")
                parts.append(("u", frozenset(), (quoted_symbol(target),), ()))
        if h in self.tree.defs:
            self.ev("call", h, line, ctx)
            parts.append(("u", frozenset(), (h,), ()))
            callee = self.tree.defs[h]
            cparams = lambda_params(callee.params)
            for k, a in enumerate(args):
                pname = cparams[k] if k < len(cparams) else None
                if isinstance(a, list) and head(a) == "lambda":
                    pctx = self.param_ctx.get((h, pname)) if pname else None
                    if pctx == "async" or pctx is None and self.recording and not self.runs_param(h, pname):
                        rid = self.spawn_lambda(a, line, None, env)
                        self.ev("async", rid, line, ctx, h)
                    else:
                        extra = pctx if isinstance(pctx, Ctx) else Ctx()
                        inner = Ctx(ctx.locks | extra.locks, ctx.noio, extra.scope or ctx.scope,
                                    self.resolve_class(extra.gated, callee, args) or ctx.gated, ctx.ignore)
                        parts.append(self.walk_lambda_inline(a, inner, env, line))
                    continue
                if isinstance(a, list) and head(a) == "function" and sym(a[1]) in self.tree.defs:
                    pctx = self.param_ctx.get((h, pname)) if pname else None
                    extra = pctx if isinstance(pctx, Ctx) else Ctx()
                    inner = Ctx(ctx.locks | extra.locks, ctx.noio, extra.scope or ctx.scope,
                                extra.gated or ctx.gated, ctx.ignore)
                    self.ev("call", sym(a[1]), line, inner, "ref")
                    parts.append(("u", frozenset(), (sym(a[1]),), ()))
                    continue
                if not self.recording and isinstance(a, Sym) and str(a) in self.cur.params and pname:
                    self.param_sites.setdefault((self.pass1_name, str(a)), []).append(("pass", ctx, h, pname))
                parts.append(self.walk(a, ctx, env, line))
            return sig_union(parts)
        # an external function: lambdas passed to a known synchronous HOF run here
        for a in args:
            if isinstance(a, list) and head(a) == "function" and len(a) > 1 and head(a[1]) == "lambda":
                a = a[1]
            if isinstance(a, list) and head(a) == "lambda":
                if h in SYNC_HOFS or h.startswith("fnn-") is False and h not in STORE_HOFS:
                    parts.append(self.walk_lambda_inline(a, ctx, env, line))
                else:
                    rid = self.spawn_lambda(a, line, None, env)
                    self.ev("async", rid, line, ctx, h)
            else:
                parts.append(self.walk(a, ctx, env, line))
        return sig_union(parts)

    def resolve_class(self, gated, callee: Def, args) -> str | None:
        """A thunk wrapper's gate class is one of its parameters: read it
        from this call's argument (a keyword, or the caller's variable)."""
        if not gated or not gated.startswith("$"):
            return gated
        pname = gated[1:]
        position = 0
        default = None
        for p in callee.params:
            ps = sym(p)
            if ps and ps.startswith("&"):
                continue
            name = sym(p[0]) if isinstance(p, list) and p else ps
            if name == pname:
                if isinstance(p, list) and len(p) > 1 and isinstance(p[1], Sym):
                    default = str(p[1])
                break
            position += 1
        value = args[position] if position < len(args) else (Sym(default) if default else None)
        if isinstance(value, Sym):
            v = str(value)
            return v if v.startswith(":") else "$" + v
        return "?"

    def runs_param(self, fn, pname) -> bool:
        return (fn, pname) in self.param_ctx

    def solve_param_ctx(self) -> None:
        sites = self.param_sites
        result: dict = {}
        changed = True
        rounds = 0
        while changed and rounds < 20:
            changed = False
            rounds += 1
            for key, rows in sites.items():
                ctxs = []
                for row in rows:
                    if row[0] == "run":
                        ctxs.append(row[1])
                    else:
                        _, ctx, callee, cparam = row
                        sub = result.get((callee, cparam))
                        if isinstance(sub, Ctx):
                            ctxs.append(Ctx(ctx.locks | sub.locks, None, sub.scope or ctx.scope,
                                            sub.gated or ctx.gated))
                if not ctxs:
                    continue
                locks = frozenset.intersection(*[c.locks for c in ctxs])
                scope = ctxs[0].scope if all(c.scope == ctxs[0].scope for c in ctxs) else None
                gated = ctxs[0].gated if all(c.gated == ctxs[0].gated for c in ctxs) else None
                new = Ctx(locks, None, scope, gated)
                if result.get(key) != new:
                    result[key] = new
                    changed = True
        for name in self.c.raw.get("fence_boundaries", []):
            d = self.tree.defs.get(name)
            if d:
                for p in lambda_params(d.params):
                    old = result.get((name, p))
                    if isinstance(old, Ctx):
                        result[(name, p)] = Ctx(old.locks, None, "shared", old.gated)
        self.param_ctx = result


# --------------------------------------------------------------------------
# summaries over the call graph
# --------------------------------------------------------------------------


class Model:
    def __init__(self, an: Analyzer) -> None:
        self.an = an
        self.tree = an.tree
        self.c = an.c
        self.infos = an.infos
        self.callers: dict[str, list] = collections.defaultdict(list)
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind == "call" and e.name in self.infos:
                    self.callers[e.name].append((name, e))
        self.roots = self.find_roots()
        self.entry_requirements = 0
        self.compute_blocking()
        self.compute_acquires()
        self.compute_signals()
        self.compute_requirements()
        self.compute_actors()
        self.compute_mustheld()

    # roots ---------------------------------------------------------------
    def find_roots(self) -> dict:
        roots = {}
        startup = set(self.c.raw.get("startup_roots", []))
        serving = self.c.raw.get("serving_roots", {})
        for name, info in self.infos.items():
            if info.thread_of is not None:
                roots[name] = "thread"
            elif name in serving:
                roots[name] = "serving"
            elif name.startswith("lambda@"):
                roots[name] = "async"
            elif not self.callers.get(name):
                roots[name] = "startup" if name in startup else "entry"
        return roots

    # R2: may-block --------------------------------------------------------
    def compute_blocking(self) -> None:
        """blk[(f, noio)] = {leafsite: (kind, line, via)}: every blocking leaf
        site F reaches with the dynamic no-I/O flag NOIO.  A leafsite is
        "function:line:leaf"; VIA is the callee (or core:SUBJECT->REALIZER)
        at LINE, None at the leaf itself."""
        overrides = self.c.raw.get("effect_overrides", {})
        blk: dict = {}
        for flag in (False, True):
            for name in self.infos:
                blk[(name, flag)] = {}
        # local leaves
        for name, info in self.infos.items():
            if name in overrides:
                continue
            for e in info.events:
                if e.kind == "leaf" and e.extra and e.extra[0] in ("io", "await", "sleep", "socket"):
                    for flag in (False, True):
                        if e.ctx.noio is not None and e.ctx.noio != flag:
                            continue  # the other arm of (if *fnn-extent-no-io* ...)
                        blk[(name, flag)][f"{name}:{e.line}:{e.name}"] = (e.extra[0], e.line, None)
        # edges: (caller, flag) <- (callee, site-flag)
        deps: dict = collections.defaultdict(list)
        for name, info in self.infos.items():
            if name in overrides:
                continue
            for e in info.events:
                targets = []
                if e.kind == "call" and e.name in self.infos and e.name not in overrides:
                    targets.append((e.name, e.name))
                elif e.kind == "core":
                    for r in self.an.reach.get(e.name, {}):
                        if r in self.infos and r not in overrides:
                            targets.append((r, "core:" + e.name + "->" + r))
                for flag in (False, True):
                    site = self.site_noio(e, flag)
                    for callee, via in targets:
                        deps[(callee, site)].append(((name, flag), e.line, via))
        work = collections.deque(k for k, v in blk.items() if v)
        queued = set(work)
        while work:
            key = work.popleft()
            queued.discard(key)
            leaves = blk[key]
            for (caller_key, line, via) in deps.get(key, ()):
                mine = blk[caller_key]
                grew = False
                for leaf, (kind, _, _) in leaves.items():
                    if leaf not in mine:
                        mine[leaf] = (kind, line, via)
                        grew = True
                if grew and caller_key not in queued:
                    queued.add(caller_key)
                    work.append(caller_key)
        self.blk = blk

    def site_noio(self, e: Event, inherited: bool) -> bool:
        return inherited if e.ctx.noio is None else e.ctx.noio

    def block_path(self, start: str, noio: bool, leaf: str, limit=16) -> list[str]:
        out = []
        cur, flag = start, noio
        seen = set()
        while cur and len(out) < limit and (cur, flag) not in seen:
            seen.add((cur, flag))
            row = self.blk.get((cur, flag), {}).get(leaf)
            if not row:
                break
            kind, line, via = row
            info = self.infos[cur]
            if via is None:
                out.append(f"{cur} ({info.path}:{line}) -> {leaf.split(':')[-1]}")
                break
            nflag = flag
            for e in info.events:
                if e.line == line and e.ctx.noio is not None:
                    nflag = e.ctx.noio
                    break
            if via.startswith("core:"):
                subject, realizer = via[5:].split("->")
                out.append(f"{cur} ({info.path}:{line}) -> ACL2 " + " -> ".join(acl2_path(self.an.reach, subject, realizer)))
                cur = realizer
            else:
                out.append(f"{cur} ({info.path}:{line})")
                cur = via
            flag = nflag
        return out

    # R5: locks a function acquires ---------------------------------------
    def compute_acquires(self) -> None:
        acq: dict[str, dict] = {n: {} for n in self.infos}
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind == "acq":
                    acq[name].setdefault(e.name, (e.line, None))
        changed = True
        while changed:
            changed = False
            for name, info in self.infos.items():
                mine = acq[name]
                for e in info.events:
                    if e.kind == "call" and e.name in acq:
                        for lock in acq[e.name]:
                            if lock not in mine:
                                mine[lock] = (e.line, e.name)
                                changed = True
                    elif e.kind == "core":
                        for r in self.an.reach.get(e.name, {}):
                            for lock in acq.get(r, {}):
                                if lock not in mine:
                                    mine[lock] = (e.line, "core:" + e.name + "->" + r)
                                    changed = True
        self.acq = acq

    def acq_path(self, start: str, lock: str, limit=12) -> list[str]:
        out = []
        cur = start
        while cur in self.acq and lock in self.acq[cur] and len(out) < limit:
            line, hop = self.acq[cur][lock]
            out.append(f"{cur} ({self.infos[cur].path}:{line})")
            if hop is None:
                break
            cur = hop.split("->")[-1] if hop.startswith("core:") else hop
        return out

    # R7: conditions a function can signal -------------------------------
    def subtype(self, a: str, b: str) -> bool:
        if b in ("t", "condition"):
            return True
        seen = set()
        stack = [a]
        while stack:
            x = stack.pop()
            if x == b:
                return True
            if x in seen:
                continue
            seen.add(x)
            stack.extend(self.tree.conditions.get(x, BUILTIN_PARENTS.get(x, ["error"] if x != "condition" else [])))
        return False

    def classify(self, ctype: str) -> str:
        for cls in ("indet", "fault", "connection", "os", "socket"):
            if self.subtype(ctype, CLASS_TYPE[cls]):
                return cls
        if self.subtype(ctype, "fnn-store-error"):
            return "refusal"
        if ctype in ("stream-error", "end-of-file", "sb-int:simple-stream-error"):
            return "socket"
        return "other"

    def eval_sig(self, s, sums) -> frozenset:
        if s[0] == "u":
            out = set()
            for leaf in s[1]:
                if leaf[0] == "type":
                    out.add(self.classify(leaf[1]))
                elif leaf[0] == "class":
                    out.add(leaf[1])
            for c in s[2]:
                out |= sums.get(c, frozenset())
            for p in s[3]:
                out |= self.eval_sig(p, sums)
            return frozenset(out)
        _, inner, clauses = s
        remaining = set(self.eval_sig(inner, sums))
        out = set()
        for types, rethrows, body in clauses:
            if types == (":no-error",):
                out |= self.eval_sig(body, sums)
                continue
            caught = {c for c in remaining if any(self.subtype(CLASS_TYPE[c], t) for t in types)}
            remaining -= caught
            if rethrows:
                out |= caught
            out |= self.eval_sig(body, sums)
        return frozenset(out | remaining)

    def compute_signals(self) -> None:
        sums: dict = {n: frozenset() for n in self.infos}
        core_fault = frozenset(["fault"])
        for _ in range(30):
            changed = False
            for name, info in self.infos.items():
                s = self.eval_sig(info.sig, sums)
                if any(e.kind == "core" for e in info.events) and "fault" not in s:
                    s = s | core_fault
                if s != sums[name]:
                    sums[name] = s
                    changed = True
            if not changed:
                break
        self.signals = sums

    # R7 helper: does a form's body reach the fence ----------------------
    def fences(self) -> set:
        if hasattr(self, "_fences"):
            return self._fences
        targets = set(self.c.raw.get("fence_functions", []))
        found = set(targets)
        changed = True
        while changed:
            changed = False
            for name, info in self.infos.items():
                if name in found:
                    continue
                if any(e.kind == "call" and e.name in found for e in info.events):
                    found.add(name)
                    changed = True
        self._fences = found
        return found

    # R1: requirements ------------------------------------------------------
    def compute_requirements(self) -> None:
        """req[f][lock][leaf] = (line, via): F needs LOCK held by its caller
        for the region access LEAF ("function:line:accessor"), reached through
        VIA (a callee, or the access itself)."""
        req: dict[str, dict] = {n: {} for n in self.infos}
        region = self.an.region_of
        lock_owner_free = set(self.c.raw.get("region_primitives", []))
        for name, info in self.infos.items():
            if name in lock_owner_free:
                continue
            for e in info.events:
                if e.kind == "acc" and e.name in region:
                    lock = region[e.name]
                    if lock not in e.ctx.locks:
                        leaf = f"{name}:{e.line}:{e.name}"
                        req[name].setdefault(lock, {}).setdefault(leaf, (e.line, None))
        changed = True
        while changed:
            changed = False
            for name, info in self.infos.items():
                mine = req[name]
                for e in info.events:
                    if e.kind == "call" and e.name in req and e.name not in lock_owner_free:
                        for lock, leaves in req[e.name].items():
                            if lock in e.ctx.locks:
                                continue
                            slot = mine.setdefault(lock, {})
                            for leaf in leaves:
                                if leaf not in slot:
                                    slot[leaf] = (e.line, e.name)
                                    changed = True
        self.req = req

    def req_path(self, start: str, lock: str, leaf: str, limit=16) -> list[str]:
        out = []
        cur = start
        seen = set()
        while cur and len(out) < limit and cur not in seen:
            seen.add(cur)
            row = self.req.get(cur, {}).get(lock, {}).get(leaf)
            if row is None:
                break
            line, via = row
            out.append(f"{cur} ({self.infos[cur].path}:{line})")
            cur = via
        fn, lline, acc = leaf.rsplit(":", 2)
        out.append(f"access {acc} at {fn}:{lline}")
        return out

    # actors ----------------------------------------------------------------
    def compute_actors(self) -> None:
        """actors[f] = set of root names whose synchronous closure reaches F."""
        actors: dict[str, set] = collections.defaultdict(set)
        for r, kind in self.roots.items():
            if kind not in ("thread", "serving", "async", "entry", "startup"):
                continue
            stack = [r]
            seen = {r}
            while stack:
                n = stack.pop()
                actors[n].add(r)
                for e in self.infos[n].events:
                    if e.kind == "call" and e.name in self.infos and e.name not in seen:
                        seen.add(e.name)
                        stack.append(e.name)
        self.actors = actors

    def actor_of(self, root: str) -> str:
        kind = self.roots.get(root)
        if kind == "startup":
            return "startup"
        if kind == "entry":
            return "main"
        return root

    # must-held locks (for R1b) ------------------------------------------
    def compute_mustheld(self) -> None:
        top = None
        held: dict[str, frozenset | None] = {n: top for n in self.infos}
        for n, kind in self.roots.items():
            held[n] = frozenset(["STARTUP"]) if kind == "startup" else frozenset()
        changed = True
        rounds = 0
        while changed and rounds < 50:
            changed = False
            rounds += 1
            for name in self.infos:
                if name in self.roots:
                    continue
                acc = None
                for caller, e in self.callers.get(name, ()):
                    h = held.get(caller)
                    if h is None:
                        continue
                    here = h | e.ctx.locks
                    acc = here if acc is None else acc & here
                if acc is not None and acc != held[name]:
                    held[name] = acc
                    changed = True
        self.mustheld = {n: (h if h is not None else frozenset()) for n, h in held.items()}


# --------------------------------------------------------------------------
# findings
# --------------------------------------------------------------------------


@dataclass
class Finding:
    rule: str
    category: str      # violation | unresolved | exception
    function: str
    path: str
    line: int
    message: str
    key: str
    trail: list = field(default_factory=list)
    loaded: bool = True
    weight: int = 1    # sites the finding stands for (R2: lock regions reaching the leaf)

    def baseline_key(self) -> str:
        return f"{self.rule}|{self.function}|{self.key}"


class Checker:
    def __init__(self, model: Model) -> None:
        self.m = model
        self.an = model.an
        self.c = model.c
        self.infos = model.infos
        self.findings: list[Finding] = []
        self.excepted = {(r["rule"], r["function"], r.get("key", "*")): r["why"]
                         for r in self.c.raw.get("exceptions", [])}

    def add(self, rule, info: FnInfo, line, message, key, trail=None, category="violation", weight=1):
        exc = (self.excepted.get((rule, info.name, key)) or self.excepted.get((rule, info.name, "*")))
        if exc and category == "violation":
            category = "exception"
            message = message + " [declared: " + exc + "]"
        self.findings.append(Finding(rule, category, info.name, info.path, line, message, key,
                                     trail or [], info.loaded, weight))

    def rule_unresolved(self, only):
        """An event the walk could not decide is reported, never assumed safe."""
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind == "unresolved":
                    rule = "R5" if ("lock" in e.name or "grab-mutex" in e.name) else (
                        "R4" if "make-thread" in e.name else "R1")
                elif e.kind == "callback" and e.ctx.locks:
                    rule = "R2"
                else:
                    continue
                if only and rule not in only:
                    continue
                what = e.name if e.kind == "unresolved" else (
                    f"a callable value {e.name} is called while holding {sorted(e.ctx.locks)}")
                self.add(rule, info, e.line, what, "unresolved:" + e.name, [], "unresolved")

    def run(self, only=None) -> list[Finding]:
        self.rule_unresolved(only)
        for rule in RULES:
            if only and rule not in only:
                continue
            getattr(self, "rule_" + rule)()
        self.findings.sort(key=lambda f: (f.rule, f.path, f.line, f.key))
        return self.findings

    # R1 ----------------------------------------------------------------------
    def rule_R1(self):
        for root, kind in self.m.roots.items():
            if kind in ("startup",):
                continue
            info = self.infos[root]
            for lock, leaves in self.m.req.get(root, {}).items():
                if kind == "entry" and not self.c.raw.get("entries_are_actors", False):
                    # an uncalled function (a command, an attachment, a hook):
                    # its caller is outside the analyzed host; inventoried only
                    self.m.entry_requirements += len(leaves)
                    continue
                for leaf, (line, via) in sorted(leaves.items()):
                    fn, lline, acc = leaf.rsplit(":", 2)
                    trail = self.m.req_path(root, lock, leaf)
                    # a stored callback runs in its CALLER's context, which
                    # the walk cannot name: unresolved, never assumed safe
                    self.add("R1", info, line,
                             f"{kind} root reaches {lock}-protected {acc} in {fn}:{lline} without holding {lock}"
                             + (" (a stored callback: its calling context is unknown)" if kind == "async" else ""),
                             f"{lock}:{fn}:{acc}", trail, "unresolved" if kind == "async" else "violation")

    # R1b -----------------------------------------------------------------------
    def rule_R1b(self):
        protected = self.an.region_of
        declared = self.c.raw.get("unlocked_publication", {})
        shared_structs = set(self.c.raw.get("shared_structs", []))
        sites: dict[str, list] = collections.defaultdict(list)
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind != "acc" or e.name in protected:
                    continue
                if e.name in self.an.tree.structs:
                    if self.an.tree.structs[e.name][0] not in shared_structs:
                        continue
                elif e.name not in self.an.tree.globals:
                    continue
                g = self.an.tree.globals.get(e.name)
                if g and e.name.startswith("+"):
                    continue
                held = e.ctx.locks | self.m.mustheld.get(name, frozenset())
                actors = {self.m.actor_of(r) for r in self.m.actors.get(name, ())}
                if not actors or actors == {"startup"} or "STARTUP" in held:
                    continue
                sites[e.name].append((info, e, held, actors - {"startup"}))
        for var, rows in sorted(sites.items()):
            writes = [r for r in rows if r[1].extra == "w"]
            if not writes:
                continue
            actors = set().union(*(r[3] for r in rows))
            if len(actors) < 2:
                continue
            common = frozenset.intersection(*[r[2] for r in rows])
            if common:
                continue
            wlocks = [r[2] for r in writes]
            if var in declared:
                row = declared[var]
                writers = set(row.get("writers", []))
                extra = sorted({r[0].name for r in writes} - writers)
                if not extra:
                    continue
                info, e = writes[0][0], writes[0][1]
                self.add("R1b", info, e.line, f"{var}: writer(s) outside its publication row: {extra}",
                         var + ":undeclared-writer")
                continue
            info, e, _, _ = writes[0]
            unlocked = [r for r in writes if not r[2]]
            if unlocked:
                w = unlocked[0]
                detail = (f"{var} written with no lock at {w[0].path}:{w[1].line} ({w[0].name}); "
                          f"{len(writes)} write site(s), {len(rows)} access site(s) across "
                          f"{len(actors)} actor(s), no common lock")
                self.add("R1b", w[0], w[1].line, detail, var + ":unlocked-write",
                         [f"{r[0].name} {r[0].path}:{r[1].line} {r[1].extra} under {sorted(r[2]) or '-'}" for r in rows[:12]])
            else:
                pairs = {tuple(sorted(x)) for x in wlocks}
                kind = "mixed-locks" if len(pairs) > 1 and not frozenset.intersection(*wlocks) else "unlocked-read"
                detail = f"{var}: {kind}; writes under {sorted(pairs)}, {len(rows)} access site(s), no common lock"
                self.add("R1b", info, e.line, detail, var + ":" + kind,
                         [f"{r[0].name} {r[0].path}:{r[1].line} {r[1].extra} under {sorted(r[2]) or '-'}" for r in rows[:12]])

    # R2 ----------------------------------------------------------------------
    def rule_R2(self):
        """One finding per (lock, blocking leaf site): the leaf runs while the
        lock is held, reached from N lock regions (one path shown)."""
        io_ok = {l for l, row in self.c.locks.items() if row.get("io_ok")}
        overrides = self.c.raw.get("effect_overrides", {})
        found: dict = {}
        for name, info in self.infos.items():
            for e in info.events:
                held = e.ctx.locks - io_ok
                if not held:
                    continue
                noio = e.ctx.noio if e.ctx.noio is not None else False
                cands = []
                if e.kind == "leaf" and e.extra and e.extra[0] in ("io", "await", "sleep", "socket"):
                    h2 = held - {e.extra[1]} if e.extra[0] == "await" and e.name == "sb-thread:condition-wait" else held
                    if h2:
                        cands.append((f"{name}:{e.line}:{e.name}", e.extra[0], h2,
                                      [f"{name} ({info.path}:{e.line}) -> {e.name}"]))
                elif e.kind == "call" and e.name in self.infos and e.name not in overrides:
                    for leaf, (kind, _, _) in self.m.blk.get((e.name, noio), {}).items():
                        cands.append((leaf, kind, held, (e.name, noio)))
                elif e.kind == "core":
                    for r in sorted(self.an.reach.get(e.name, {})):
                        if r in self.infos and r not in overrides:
                            for leaf, (kind, _, _) in self.m.blk.get((r, noio), {}).items():
                                cands.append((leaf, kind, held, ("core", e.name, r, noio)))
                for leaf, kind, locks, how in cands:
                    for lock in sorted(locks):
                        k = (lock, leaf)
                        row = found.get(k)
                        if row is None:
                            found[k] = [kind, info, e, how, 1]
                        else:
                            row[4] += 1
        for (lock, leaf), (kind, info, e, how, n) in sorted(found.items(), key=lambda kv: kv[0]):
            lfn, lline, lname = leaf.split(":", 2)
            if isinstance(how, list):
                trail = how
            elif how[0] == "core":
                _, subject, r, noio = how
                trail = [f"{info.name} ({info.path}:{e.line}) core call " + " -> ".join(
                    acl2_path(self.an.reach, subject, r)) + " (ACL2 closure, path-insensitive)"] + \
                    self.m.block_path(r, noio, leaf)
            else:
                callee, noio = how
                trail = [f"{info.name} ({info.path}:{e.line})"] + self.m.block_path(callee, noio, leaf)
            leaf_info = self.infos.get(lfn, info)
            self.add("R2", leaf_info, int(lline),
                     f"{kind} leaf {lname} runs while holding {lock}; reached from {n} site(s) under {lock}, "
                     f"e.g. {info.name} ({info.path}:{e.line})",
                     f"{lock}:{lname}", trail, weight=n)

    # R3 ----------------------------------------------------------------------
    def rule_R3(self):
        sinks = set(self.c.read_sinks)
        borrows = self.c.raw.get("borrows", {})
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind != "leaf" or e.name not in sinks:
                    continue
                if "E" in (e.ctx.locks | self.m.mustheld.get(name, frozenset())):
                    continue
                row = borrows.get(name)
                if row is None:
                    trail = self.callers_trail(name)
                    self.add("R3", info, e.line,
                             f"{e.name} outside the extent lock with no row or lease: the descriptor "
                             f"was captured under the lock and used after it", "naked:" + e.name, trail)
                    continue
                problem = self.verify_borrow(info, e, row)
                if problem:
                    self.add("R3", info, e.line, f"declared {row['kind']} borrow broken: {problem}",
                             "borrow:" + e.name, self.callers_trail(name))

    def callers_trail(self, name, depth=4) -> list[str]:
        out = []
        frontier = [name]
        seen = {name}
        for _ in range(depth):
            nxt = []
            for n in frontier:
                for caller, e in self.m.callers.get(n, ())[:4]:
                    if caller not in seen:
                        seen.add(caller)
                        out.append(f"{caller} ({self.infos[caller].path}:{e.line}) -> {n}")
                        nxt.append(caller)
            frontier = nxt
        return out

    def verify_borrow(self, info, sink, row) -> str | None:
        """The finite protocols the first landing checks (Astra R3)."""
        kind = row["kind"]
        if kind in ("issued-row", "window-lease"):
            # reachable only through the declared activation, whose loop
            # announces the actual return after the job returns
            allowed = set(row["callers"])
            bad = [c for c, _ in self.m.callers.get(info.name, ()) if c not in allowed]
            if bad or not self.m.callers.get(info.name):
                return f"called from {bad or 'nothing'}; only {sorted(allowed)} hold the {kind}"
            act = self.infos.get(row["activation"])
            if act is None:
                return f"activation {row['activation']} is missing"
            job_line = ret_line = None
            for e in act.events:
                if e.kind == "call" and e.name == row["job"] and job_line is None:
                    job_line = e.line
                if e.kind == "call" and e.name == row["release"]:
                    ret_line = e.line if ret_line is None else ret_line
            if job_line is None:
                return f"{row['activation']} no longer runs {row['job']}"
            if ret_line is None:
                return f"{row['activation']} never calls {row['release']} (the hold is never settled)"
            if ret_line < job_line:
                return f"{row['release']} precedes {row['job']} in {row['activation']} (released before return)"
            issue = self.infos.get(row["issue"])
            if issue is None or not any(e.kind == "core" and e.name == row["issue_core"] for e in issue.events):
                return f"{row['issue']} no longer issues the row through {row['issue_core']}"
            return None
        if kind == "file-pin":
            acquire = release = None
            for e in info.events:
                if e.kind == "core" and e.name == row["acquire_core"] and acquire is None:
                    acquire = e.line
                if e.kind == "call" and e.name == row["release"]:
                    release = e.line if release is None else min(release, e.line)
            if acquire is None or acquire > sink.line:
                return f"no {row['acquire_core']} before the read"
            if release is None:
                return f"no {row['release']} on the failure path"
            if release < sink.line:
                return f"{row['release']} precedes the read"
            if not self.in_unwind_protect(info.name, sink.line, row["release"]):
                return "the read is not inside an unwind-protect whose cleanup releases the lease"
            return None
        return f"unknown borrow kind {kind}"

    def in_unwind_protect(self, fname, sink_line, release) -> bool:
        d = self.an.tree.defs.get(fname)
        if d is None:
            return False
        stack = list(d.body)
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                if head(x) == "unwind-protect" and len(x) > 2:
                    def lines(f):
                        out = set()
                        st = [f]
                        while st:
                            y = st.pop()
                            if isinstance(y, list):
                                out.add(line_of(y, -1))
                                st.extend(y)
                        return out

                    def names(f):
                        out = set()
                        st = [f]
                        while st:
                            y = st.pop()
                            if isinstance(y, Sym):
                                out.add(str(y))
                            elif isinstance(y, list):
                                st.extend(y)
                        return out
                    if sink_line in lines(x[1]) and any(release in names(c) for c in x[2:]):
                        return True
                stack.extend(x)
        return False

    # R4 ----------------------------------------------------------------------
    def rule_R4(self):
        declared = self.c.raw.get("threads", {})
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind != "thread":
                    continue
                key = f"{name}"
                row = declared.get(key)
                if row is None:
                    self.add("R4", info, e.line,
                             f"make-thread {e.extra!r} has no declared registry, join site or fault policy",
                             "undeclared:" + str(e.extra), [])
                    continue
                self.check_registration(info, e, row)
                self.check_fault_policy(info, e, row)
        # deregistration before terminal shared cleanup
        for name, info in self.infos.items():
            self.check_deregistration(info)

    def check_registration(self, info, e, row):
        d = self.an.tree.defs.get(info.name)
        if d is None or not row.get("registry"):
            return
        reg = row["registry"]
        # find (push X (REG ...)) or (setf (REG ...) X)
        stack = list(d.body)
        pushes = []
        binds = {}
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                if head(x) in ("let", "let*") and len(x) > 1 and isinstance(x[1], list):
                    for b in x[1]:
                        if isinstance(b, list) and len(b) == 2 and isinstance(b[0], Sym):
                            binds[str(b[0])] = b[1]
                if head(x) in ("push", "pushnew") and len(x) > 2 and head(x[2]) == reg:
                    pushes.append(x)
                if head(x) == "setf":
                    for k in range(1, len(x) - 1, 2):
                        if head(x[k]) == reg:
                            pushes.append(Node([Sym("setf"), x[k + 1], x[k]]))
                stack.extend(x)
        if not pushes:
            self.add("R4", info, e.line, f"thread is never registered in {reg}", "unregistered:" + reg)
            return
        reported = set()
        for p in pushes:
            v = p[1]
            if isinstance(v, Sym) and str(v) in binds:
                v = binds[str(v)]
            if isinstance(v, list) and head(v) == "sb-thread:make-thread":
                continue
            if isinstance(v, list) and head(v) in ("and", "if", "when", "or") and reg not in reported:
                reported.add(reg)
                self.add("R4", info, line_of(p, e.line),
                         f"registered value in {reg} is {render(v, 50)}: it can be NIL, not the thread",
                         "nil-registered:" + reg)
            elif isinstance(v, list) and head(v) == "cons":
                continue

    def check_fault_policy(self, info, e, row):
        """The thread's top level (its root or the function the root runs)
        must handle serious-condition: a condition that escapes a thread ends
        it silently (and with --disable-debugger, the process)."""
        policy = row.get("fault_policy")
        join = row.get("join")
        if join and not (self.infos.get(join) and any(
                x.kind == "leaf" and x.name == "sb-thread:join-thread" for x in self.infos[join].events)):
            self.add("R4", info, e.line, f"declared join site {join} does not join a thread", "no-join:" + str(join))
        root = self.infos.get(e.name)
        if root is None or policy is None:
            return
        tops = [root] + [self.infos[x.name] for x in root.events[:3]
                         if x.kind == "call" and x.name in self.infos][:1]
        for top in tops:
            for (line, inner, clauses, ctx) in top.handlers:
                if any(any(self.m.subtype("serious-condition", t) or t in ("serious-condition", "t", "condition")
                           for t in types) for types, *_ in clauses):
                    return
        self.add("R4", info, e.line,
                 f"thread {e.extra!r} (fault policy {policy}) has no top-level serious-condition handler: "
                 f"an escaping condition ends it silently", "no-handler:" + str(e.extra))

    def check_deregistration(self, info):
        d = self.an.tree.defs.get(info.name)
        if d is None:
            return
        cleanup_ok = set(self.c.raw.get("after_deregistration_ok", []))
        flat = []

        def walk(f, depth):
            if isinstance(f, list):
                flat.append((f, depth))
                for x in f:
                    walk(x, depth + 1)
        for f in d.body:
            walk(f, 0)
        for f, depth in flat:
            if head(f) == "delete" and len(f) > 2 and sym(f[1]) == "sb-thread:*current-thread*":
                reg = head(f[2])
                line = line_of(f, d.line)
                later = [e for e in info.events if e.kind == "call" and e.line > line
                         and e.name not in cleanup_ok
                         and (self.m.acq.get(e.name) or self.m.req.get(e.name))]
                if later:
                    first = later[0]
                    self.add("R4", info, line,
                             f"removes itself from {reg} before terminal shared work: "
                             f"{first.name} at :{first.line} ({len(later)} call(s) after)",
                             "dereg-before-cleanup:" + str(reg),
                             [f"{x.name} :{x.line}" for x in later[:8]])

    # R5 ----------------------------------------------------------------------
    def rule_R5(self):
        allowed = set()
        for a, bs in self.c.lock_order.items():
            for b in bs:
                allowed.add((a, b))
        recursive = {l for l, row in self.c.locks.items() if row.get("recursive")}
        closure = set(allowed)
        changed = True
        while changed:
            changed = False
            for (a, b) in list(closure):
                for (c, d) in list(closure):
                    if b == c and (a, d) not in closure:
                        closure.add((a, d))
                        changed = True
        observed: dict = {}
        direct_o = set(self.c.raw.get("direct_owner_sites", []))
        for name, info in self.infos.items():
            for e in info.events:
                held = e.ctx.locks
                if e.kind == "acq":
                    if e.name == "O" and name not in direct_o and not e.ctx.gated and e.extra != "gate":
                        if not self.is_gate_expansion(info, e):
                            self.add("R5", info, e.line, "direct owner-mutex acquisition outside the gate, "
                                     "not in the declared list", "direct-O")
                    for h in held:
                        observed.setdefault((h, e.name), (info, e, [f"{name} ({info.path}:{e.line})"]))
                elif e.kind == "call" and e.name in self.m.acq:
                    for lock in self.m.acq[e.name]:
                        for h in held:
                            observed.setdefault((h, lock), (info, e, [f"{name} ({info.path}:{e.line})"]
                                                            + self.m.acq_path(e.name, lock)))
                elif e.kind == "core":
                    for r in self.an.reach.get(e.name, {}):
                        for lock in self.m.acq.get(r, {}):
                            for h in held:
                                observed.setdefault((h, lock), (info, e, [f"{name} ({info.path}:{e.line}) core "
                                                                          + e.name] + self.m.acq_path(r, lock)))
        for (a, b), (info, e, trail) in sorted(observed.items(), key=lambda kv: kv[0]):
            if a == b:
                if a in recursive:
                    continue
                self.add("R5", info, e.line, f"{a} acquired while already held (non-recursive self-deadlock)",
                         f"{a}->{b}", trail)
                continue
            if a.startswith("?") or b.startswith("?"):
                self.add("R5", info, e.line, f"edge {a} -> {b} with an unknown lock object",
                         f"{a}->{b}", trail, "unresolved")
                continue
            if (a, b) not in closure:
                cat = "violation"
                msg = f"undeclared lock edge {a} -> {b}"
                if (b, a) in closure or (b, a) in observed:
                    msg = f"lock edge {a} -> {b} INVERTS the declared/observed order {b} -> {a}"
                self.add("R5", info, e.line, msg, f"{a}->{b}", trail, cat)
        self.observed_edges = observed

    def is_gate_expansion(self, info, e) -> bool:
        return any(x.kind == "gate" and x.line == e.line for x in info.events)

    # R6 ----------------------------------------------------------------------
    def rule_R6(self):
        starts = self.c.dispatch["roots"]
        stop = set(self.c.dispatch.get("stop", []))
        allowed = self.c.dispatch.get("allowed", {})
        seen = {}
        stack = [(s, [s]) for s in starts if s in self.infos]
        while stack:
            n, trail = stack.pop()
            if n in seen:
                continue
            seen[n] = trail
            for e in self.infos[n].events:
                if e.kind == "call" and e.name in self.infos and e.name not in stop and e.name not in seen:
                    stack.append((e.name, trail + [e.name]))
        for n, trail in seen.items():
            info = self.infos[n]
            for e in info.events:
                what = None
                if e.kind == "acq":
                    what = "takes lock " + e.name
                elif e.kind == "acc" and e.name in self.an.tree.synchronized:
                    what = "touches synchronized table " + e.name
                elif e.kind == "leaf" and e.name == "make-hash-table":
                    what = "constructs a hash table"
                if what is None:
                    continue
                key = e.name
                if key in allowed:
                    self.add("R6", info, e.line, what + " on the fnn-call path", key, trail, "exception")
                    self.findings[-1].message += " [declared: " + allowed[key] + "]"
                    continue
                self.add("R6", info, e.line, what + " on the fnn-call path", key, trail)

    # R7 ----------------------------------------------------------------------
    def rule_R7(self):
        fences = set(self.c.raw.get("fence_functions", []))
        scopes = self.c.raw.get("failure_scopes", {})
        for name, info in self.infos.items():
            actors = {self.m.actor_of(r) for r in self.m.actors.get(name, ())}
            if not (actors - {"startup", "main"}) and self.m.roots.get(name) not in ("thread", "serving", "async"):
                continue  # offline/command code: inventoried, not a served failure scope
            for (line, inner, clauses, ctx) in info.handlers:
                can = set(self.m.eval_sig(inner, self.m.signals))
                row = scopes.get(f"{name}:{line}") or scopes.get(name)
                scope = row["scope"] if isinstance(row, dict) else row
                remaining = set(can)
                for types, rethrows, body, names, spec in clauses:
                    caught = {c for c in remaining if any(self.m.subtype(CLASS_TYPE[c], t) for t in types)}
                    remaining -= caught
                    if not caught:
                        continue
                    routes = rethrows or bool(names & fences)
                    core = caught & {"fault", "indet"}
                    local = caught & {"socket", "refusal", "connection"}
                    if core and not routes and scope not in ("private", "result", "converts", "fence"):
                        self.add("R7", info, line,
                                 f"handler clause {spec} consumes {sorted(core)} without routing it to the fence",
                                 f"swallow:{spec}:{','.join(sorted(core))}",
                                 [f"protected form can signal {sorted(can)}"])
                    if local and routes and not rethrows and scope != "shared-only":
                        self.add("R7", info, line,
                                 f"handler clause {spec} routes connection-local {sorted(local)} to the fence "
                                 f"(a client/peer event stops the node)",
                                 f"overfence:{spec}:{','.join(sorted(local))}",
                                 [f"protected form can signal {sorted(can)}"])
            for (line, cls, body, ctx) in info.gated:
                can = self.m.eval_sig(body, self.m.signals) & {"fault", "indet"}
                if not can:
                    continue
                if self.body_in_shared(body):
                    continue

                self.add("R7", info, line,
                         f"gated body (class {cls}) can signal {sorted(can)} outside the shared-action fence",
                         "unfenced-gated", [])

    def body_fences(self, body, fences) -> bool:
        if body[0] == "u":
            if any(c in fences for c in body[2]):
                return True
            return any(self.body_fences(p, fences) for p in body[3])
        return self.body_fences(body[1], fences) or any(self.body_fences(b, fences) for _, _, b in body[2])

    def body_in_shared(self, body) -> bool:
        names = set(self.c.raw.get("fence_boundaries", []))
        if body[0] == "u":
            return bool(set(body[2]) & names)
        return False

    # R8 ----------------------------------------------------------------------
    def rule_R8(self):
        queues = self.c.raw.get("handoff_queues", {})
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind != "push" or e.name not in queues:
                    continue
                row = queues[e.name]
                lock = row["lock"]
                flag = row.get("lifecycle")
                checked = flag and any(x.kind == "acc" and x.name == flag and lock in x.ctx.locks
                                       and x.extra == "r" for x in info.events)
                if not checked:
                    self.add("R8", info, e.line,
                             f"push into {e.name} under {sorted(e.ctx.locks)} with no lifecycle check of the "
                             f"receiver under {lock}" + ("" if flag else " (no lifecycle flag is declared)"),
                             "push:" + e.name, [row.get("why", "")])

    # R9 ----------------------------------------------------------------------
    def rule_R9(self):
        actors = self.c.raw.get("actors", {})
        for actor, row in actors.items():
            roots = [r for r in row["roots"] if r in self.infos]
            reach: dict[str, list] = {}
            stack = [(r, [r]) for r in roots]
            while stack:
                n, trail = stack.pop()
                if n in reach:
                    continue
                reach[n] = trail
                for e in self.infos[n].events:
                    if e.kind == "call" and e.name in self.infos and e.name not in reach:
                        stack.append((e.name, trail + [e.name]))
            for n, trail in sorted(reach.items()):
                info = self.infos[n]
                for e in info.events:
                    if e.kind == "gate" and "gate_classes" in row:
                        cls = e.extra
                        if cls not in row["gate_classes"]:
                            self.add("R9", info, e.line,
                                     f"actor {actor} enters the gate (class {cls}) and may wait behind a barrier",
                                     f"{actor}:gate", trail)
                    if e.kind == "leaf" and e.extra and e.extra[0] == "await" and row.get("no_await"):
                        if e.name in row.get("await_ok", []) or n in row.get("await_ok_functions", []):
                            continue
                        self.add("R9", info, e.line, f"actor {actor} parks in {e.name}",
                                 f"{actor}:await:{e.name}", trail)
        # :reader quanta never reach the commit pipeline
        pipeline = set(self.c.raw.get("commit_pipeline", []))
        for name, info in self.infos.items():
            done = set()
            for e in info.events:
                if e.kind != "call" or not e.ctx.gated or e.name in done:
                    continue
                classes = self.class_values(name, e.ctx.gated)
                if ":reader" not in classes:
                    continue
                hit = self.reaches(("u", frozenset(), (e.name,), ()), pipeline)
                if hit:
                    done.add(e.name)
                    self.add("R9", info, e.line,
                             f"a :reader quantum (class {e.ctx.gated} -> {sorted(classes)}) reaches the commit "
                             f"pipeline ({hit[-1]})", "reader-commit:" + hit[-1], hit)

    def class_values(self, fname, cls, depth=4) -> set:
        if cls is None:
            return set()
        if not cls.startswith("$"):
            return {cls}
        param = cls[1:]
        info = self.infos.get(fname)
        if info is None or param not in info.params or depth == 0:
            return {"?"}
        pos = info.params.index(param)
        out = set()
        for caller, e in self.m.callers.get(fname, ()):
            d = self.an.tree.defs.get(caller)
            out |= self.arg_values(caller, d, fname, pos, depth)
        d = self.an.tree.defs.get(fname)
        # an &optional default
        if d is not None:
            for p in d.params:
                if isinstance(p, list) and p and sym(p[0]) == param and len(p) > 1 and isinstance(p[1], Sym):
                    out.add(str(p[1]))
        return out or {"?"}

    def arg_values(self, caller, d, callee, pos, depth) -> set:
        out = set()
        if d is None:
            return out
        stack = list(d.body)
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                if head(x) == callee and len(x) > pos + 1:
                    v = x[pos + 1]
                    if isinstance(v, Sym) and str(v).startswith(":"):
                        out.add(str(v))
                    elif isinstance(v, Sym):
                        out |= self.class_values(caller, "$" + str(v), depth - 1)
                stack.extend(x)
        return out

    def reaches(self, body, targets) -> list | None:
        calls = set()

        def collect(s):
            if s[0] == "u":
                calls.update(s[2])
                for p in s[3]:
                    collect(p)
            else:
                collect(s[1])
                for _, _, b in s[2]:
                    collect(b)
        collect(body)
        seen = {}
        stack = [(c, [c]) for c in calls]
        while stack:
            n, trail = stack.pop()
            if n in targets:
                return trail
            if n in seen or n not in self.infos:
                continue
            seen[n] = True
            for e in self.infos[n].events:
                if e.kind == "call" and e.name not in seen:
                    stack.append((e.name, trail + [e.name]))
        return None

    # R10 ---------------------------------------------------------------------
    def rule_R10(self):
        closers = set(self.c.raw.get("close_primitives", ["fnn-close"]))
        declared = self.c.raw.get("close_sites", {})
        openers = set(self.c.raw.get("open_primitives", []))
        for name, info in self.infos.items():
            if name in self.c.raw.get("close_primitive_definitions", []):
                continue
            d = self.an.tree.defs.get(name)
            for e in info.events:
                if e.kind != "call" or e.name not in closers:
                    continue
                if e.ctx.ignore:
                    self.add("R10", info, e.line, f"{e.name} inside ignore-errors: an ambiguous close is swallowed",
                             "ignored-close:" + e.name)
                    continue
                if name in declared:
                    continue
                if self.owns_fd(d, e.line, openers):
                    continue
                self.add("R10", info, e.line, f"{e.name} of a descriptor this function did not open "
                         "and no close row declares", "foreign-close:" + e.name, self.callers_trail(name, 2))

    def owns_fd(self, d, line, openers) -> bool:
        if d is None:
            return False
        stack = list(d.body)
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                h = head(x)
                if h in openers:
                    return True
                stack.extend(x)
        return False


# --------------------------------------------------------------------------
# realization table (host-model review M3)
# --------------------------------------------------------------------------


def realization_rows(contracts: Contracts) -> list:
    return contracts.raw.get("realization", [])


LABEL_LAYERS = {"C", "P"}


def check_realization(checker: Checker) -> None:
    """The host-model realization table (review M3): each label's host sites
    exist, call their primitive and ACL2 subject, hold the label's locks, and
    call each requires_before subject before the primitive; the row's own
    shape is the agreed one (layer C|P, a P label names its A-PRIM-* row,
    'enabled' names ACL2 functions that exist)."""
    known = getattr(checker.an.reach, "known", set())
    for row in realization_rows(checker.c):
        label = row.get("label", "?")
        anchor = FnInfo("realization " + label, "planning/host-realization.json", 0, True)
        if row.get("layer") not in LABEL_LAYERS:
            checker.add("R3", anchor, 0, f"realization {label}: layer must be C or P", "realization-shape:" + label)
        if row.get("layer") == "P" and not str(row.get("assumption", "")).startswith("A-PRIM-"):
            checker.add("R3", anchor, 0, f"realization {label}: a P label names its A-PRIM-* row",
                        "realization-shape:" + label)
        for name in row.get("enabled", []):
            if known and name not in known:
                checker.add("R3", anchor, 0, f"realization {label}: enabling predicate {name} is not an ACL2 function",
                            "realization-enabled:" + label)
        for site in row.get("sites", []):
            fn = site["function"]
            info = checker.infos.get(fn)
            if info is None:
                where = FnInfo(fn, site.get("file", "?"), 0, True)
                checker.add("R3", where, 0, f"realization {label}: {fn} does not exist", "realization:" + label)
                continue
            prim = site.get("primitive")
            prim_events = [e for e in info.events if (e.kind in ("leaf", "call") and e.name == prim)] if prim else []
            if prim and not prim_events:
                checker.add("R3", info, info.line, f"realization {label}: {fn} no longer calls {prim}",
                            "realization:" + label)
                continue
            core = site.get("core")
            if core and not any(e.kind == "core" and e.name == core for e in info.events):
                checker.add("R3", info, info.line, f"realization {label}: {fn} no longer calls {core}",
                            "realization:" + label)
            held_req = set(site.get("locks_held", []))
            if held_req:
                where = prim_events or [e for e in info.events if e.kind == "core" and e.name == core]
                for e in where:
                    have = e.ctx.locks | checker.m.mustheld.get(fn, frozenset())
                    if not held_req <= have:
                        checker.add("R3", info, e.line,
                                    f"realization {label}: {fn} runs {prim or core} holding "
                                    f"{sorted(have)}, the label needs {sorted(held_req)}",
                                    "realization-locks:" + label)
            for before in site.get("requires_before", []):
                firsts = [e.line for e in info.events if e.kind in ("core", "call") and e.name == before]
                for e in prim_events:
                    if not firsts or min(firsts) > e.line:
                        checker.add("R3", info, e.line,
                                    f"realization {label}: {prim} at :{e.line} without {before} before it",
                                    "realization-before:" + label)


# --------------------------------------------------------------------------
# baseline, report, main
# --------------------------------------------------------------------------


def load_baseline(path: Path) -> dict:
    if not path.exists():
        return {}
    data = json.loads(path.read_text())
    return {row["key"]: row for row in data.get("findings", [])}


def weights(findings: list[Finding]) -> collections.Counter:
    out: collections.Counter = collections.Counter()
    for f in findings:
        if f.category != "exception":
            out[f.baseline_key()] += f.weight
    return out


def judge(findings: list[Finding], baseline: dict, enclave: set) -> dict:
    """New: a key absent from the baseline, or over its count; every
    finding inside the enclave.  Stale: a baseline count above today's."""
    counted = weights(findings)
    base_counts = {k: row.get("count", 1) for k, row in baseline.items()}
    new = []
    for f in findings:
        if f.category == "exception":
            continue
        k = f.baseline_key()
        if f.function in enclave:
            new.append(("enclave", f))
            continue
        if k not in base_counts or counted[k] > base_counts[k]:
            new.append(("new", f))
    stale = [k for k, n in base_counts.items() if counted.get(k, 0) < n]
    enclave_rows = [k for k in base_counts if k.split("|")[1] in enclave]
    return {"new": new, "stale": stale, "enclave_baselined": enclave_rows}


def write_baseline(path: Path, findings: list[Finding], old: dict, initial: bool) -> list[str]:
    counted = weights(findings)
    if not initial:
        grown = [k for k, n in counted.items() if n > old.get(k, {}).get("count", 0)]
        if grown:
            return grown
    rows = []
    by_key = {}
    for f in findings:
        if f.category != "exception":
            by_key.setdefault(f.baseline_key(), f)
    for k in sorted(counted):
        f = by_key[k]
        rows.append({"key": k, "count": counted[k], "rule": f.rule, "category": f.category,
                     "where": f"{f.path}:{f.line}", "reason": old.get(k, {}).get("reason", f.message[:160])})
    path.write_text(json.dumps({"comment": "shrink-only; regenerate with "
                                "tools/lock_discipline_check.py --write-baseline", "findings": rows},
                               indent=1) + "\n")
    return []


def analyze_tree(root: Path, contracts: Contracts, files: list[str] | None = None,
                 reach: dict | None = None) -> tuple[Analyzer, Model, Checker]:
    tree = collect_tree(root, files)
    if reach is None:
        realizers = set(contracts.raw.get("realizers", [])) | (tree.raw_replaced & set(tree.defs))
        reach = acl2_realizer_reach(root, realizers)
    an = Analyzer(tree, contracts, reach)
    an.param_sites = {}
    an.analyze()
    model = Model(an)
    return an, model, Checker(model)


def build(root: Path, contracts_path: Path) -> tuple[Analyzer, Model, Checker]:
    return analyze_tree(root, load_contracts(contracts_path))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=str(TOOL_ROOT))
    ap.add_argument("--contracts", default=str(CONTRACTS))
    ap.add_argument("--baseline", default=str(BASELINE))
    ap.add_argument("--check", action="store_true", help="fail on new findings and any enclave finding")
    ap.add_argument("--rule", action="append")
    ap.add_argument("--function")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("-v", "--verbose", action="store_true")
    ap.add_argument("--all-files", action="store_true", help="also report parked (unloaded) files")
    ap.add_argument("--write-baseline", action="store_true")
    ap.add_argument("--initial", action="store_true")
    ap.add_argument("--emit-realization", action="store_true")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args(argv)
    started = time.time()
    root = Path(args.root).resolve()
    an, model, checker = build(root, Path(args.contracts))
    findings = checker.run(set(args.rule) if args.rule else None)
    if not args.rule or "R3" in args.rule:
        check_realization(checker)
        findings = checker.findings
    if not args.all_files:
        findings = [f for f in findings if f.loaded]
    if args.function:
        findings = [f for f in findings if f.function == args.function]
    if args.emit_realization:
        out = root / REALIZATION
        out.write_text(json.dumps({"comment": "generated by tools/lock_discipline_check.py "
                                   "--emit-realization; source: the model book's *fn-hmc-realization* "
                                   "(seeded from tools/lock_discipline_contracts.json until it lands)",
                                   "rows": realization_rows(checker.c)}, indent=1) + "\n")
        print(f"lock_discipline_check: wrote {REALIZATION}")
        return 0
    enclave = set(checker.c.raw.get("enclave", {}).get("functions", []))
    baseline = load_baseline(Path(args.baseline))
    if args.write_baseline:
        grown = write_baseline(Path(args.baseline), findings, baseline, args.initial)
        if grown:
            print("lock_discipline_check: refusing to raise the baseline (use --initial once):")
            for k in grown[:20]:
                print("  " + k)
            return 1
        print(f"lock_discipline_check: wrote {args.baseline}")
        return 0
    verdict = judge(findings, baseline, enclave)
    if args.rule or args.function:
        verdict["stale"] = []  # a filtered run cannot judge the whole baseline
    realization_drift = None
    out = root / REALIZATION
    if out.exists() and not args.rule:
        try:
            if json.loads(out.read_text()).get("rows") != realization_rows(checker.c):
                realization_drift = f"{REALIZATION} is stale: regenerate with --emit-realization"
        except ValueError:
            realization_drift = f"{REALIZATION} does not parse"
    elapsed = time.time() - started
    cats = collections.Counter((f.rule, f.category) for f in findings)
    total_sites = sum(len(i.events) for i in an.infos.values())
    if args.json:
        print(json.dumps({"seconds": round(elapsed, 2), "functions": len(an.infos),
                          "events": total_sites,
                          "findings": [f.__dict__ for f in findings],
                          "new": [f.baseline_key() for _, f in verdict["new"]],
                          "stale": verdict["stale"]}, indent=1, default=str))
    else:
        if not args.summary:
            for f in findings:
                tag = {"violation": "VIOLATION", "unresolved": "UNRESOLVED", "exception": "EXCEPTION"}[f.category]
                print(f"{f.path}:{f.line}: {f.rule} {tag} {f.function}: {f.message}")
                if args.verbose:
                    for t in f.trail:
                        print("    " + t)
        print(f"lock_discipline_check: {len(an.infos)} functions/roots, {total_sites} analyzed sites, "
              f"{len(an.tree.unreadable)} unreadable files, {elapsed:.1f} s")
        for rule in RULES:
            v, u, x = (cats[(rule, "violation")], cats[(rule, "unresolved")], cats[(rule, "exception")])
            if v or u or x:
                print(f"  {rule:4} violation {v:4}  unresolved {u:4}  exception {x:4}")
        nb = len([1 for k, f in verdict["new"]])
        if realization_drift:
            print("  " + realization_drift)
        print(f"  total {len(findings)}; baselined {len(baseline)} rows (weight "
              f"{sum(r.get('count', 1) for r in baseline.values())}); "
              f"new {nb}; stale baseline rows {len(verdict['stale'])}; enclave {len(enclave)} functions")
    if args.check:
        bad = verdict["new"] or verdict["stale"] or verdict["enclave_baselined"] or realization_drift
        if bad:
            for why, f in verdict["new"][:40]:
                print(f"lock_discipline_check: {why.upper()} {f.path}:{f.line} {f.rule} {f.function}: {f.message}")
            for k in verdict["stale"][:40]:
                print(f"lock_discipline_check: STALE baseline row (lower it with --write-baseline): {k}")
            for k in verdict["enclave_baselined"]:
                print(f"lock_discipline_check: an enclave finding cannot be baselined: {k}")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
