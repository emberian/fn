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
migrated, and "files": host files every function of which is migrated -- a
file whose owner sections are all declared def-sections, lane ACTORS) is
strict: any violation or unresolved site there fails.  Outside
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
    python3 tools/lock_discipline_check.py --audit-callbacks  # standalone: print only the
                           # callback-ordinal audit (a callback_contexts why text that names
                           # its own file must name the line its ordinal resolves to); the
                           # audit is part of --check's verdict either way
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
    global_inits: dict = field(default_factory=dict)  # defvar name -> its init form (None when absent)
    conditions: dict = field(default_factory=dict)    # name -> [parents]
    aliens: set = field(default_factory=set)          # define-alien-routine lisp names
    raw_replaced: set = field(default_factory=set)    # ACL2 names the host replaces
    files: dict = field(default_factory=dict)         # path -> loaded?
    unreadable: dict = field(default_factory=dict)
    sections: dict = field(default_factory=dict)      # def-section name -> (path, line, actors, classes, admits)
    actors: dict = field(default_factory=dict)        # def-actor name -> (path, line, kind, thread-name, roster, join, failure)


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


# def-actor (host/native/owner.lisp, lanes ACTORS / GENERATORS-2): a declared
# actor.  Its starter (NAME SERVICE CUSTODY THUNK [ESCAPE ...]) spawns a
# thread that runs THUNK (fnn-owner-actor-start -> fnn-owner-actor-run), so a
# call to it is walked as a make-thread of THUNK under the declared thread
# name, and rule R4 takes that thread's row from the declaration (its join
# site and failure policy) instead of a hand-written `threads' contract.
# The starter def-actor emits is (defun NAME (service custody thunk &optional
# escape physical-callback before-start) (fnn-owner-actor-start service custody
# thunk THREAD-NAME ROSTER escape physical-callback before-start)): argument
# index 5 is before-start (owner.lisp:1833-1834).
ACTOR_RUNNER = "fnn-owner-actor-start"
ACTOR_BEFORE_START_ARG = 5


def actor_declaration(form):
    """(kind, thread-name, roster, join, failure) of a (def-actor NAME :kind K
    :thread-name S :roster R :join J :failure F), or None without a thread
    name (ACL2 refuses an incomplete declaration at load)."""
    name = sym(form[1]) if len(form) > 1 else None
    keys = {}
    rest = list(form[2:])
    for k in range(0, len(rest) - 1, 2):
        if isinstance(rest[k], Sym):
            keys[str(rest[k])] = rest[k + 1]
    thread = keys.get(":thread-name")
    if not name or not isinstance(thread, str) or isinstance(thread, Sym):
        return None
    return (render(keys.get(":kind", Sym("nil")), 200), thread,
            render(keys.get(":roster", Sym("nil")), 200),
            render(keys.get(":join", Sym("nil")), 200),
            render(keys.get(":failure", Sym("nil")), 200))


def visit_top(tree: Tree, form, line: int, rel: str, lines: list[str]) -> None:
    h = head(form)
    if h is None:
        return
    if h == "def-actor":
        decl = actor_declaration(form)
        if decl is not None:
            tree.actors[str(form[1])] = (rel, line) + decl
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
        tree.global_inits[name] = form[2] if len(form) >= 3 else None
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
    # (param name, wants_truthy): this subtree was reached through the
    # corresponding arm of (if PARAM ...) / (if (not PARAM) ...) in the
    # current defun, so everything under it runs only when PARAM has that
    # truthiness at entry.  A route so tagged can be ruled out for a call
    # site that passes a literal for PARAM; it stays live otherwise.
    cond: tuple | None = None


@dataclass
class Event:
    kind: str
    name: str
    line: int
    ctx: Ctx
    extra: object = None
    # specials dynamically rebound (a `let' of a defvar) around this event,
    # in its own defun: the access names this thread's binding, not the global
    bound: frozenset = frozenset()
    # one operation on a :synchronized table (gethash, remhash, clrhash,
    # hash-table-count, setf of gethash): atomic in the table's own lock
    atomic: bool = False
    # (names the thread variable of an enclosing `unless (and T (thread-alive-p T))'
    # is bound from) per such guard, and a call's first argument when it is a symbol
    dead: tuple = ()
    arg0: str = ""


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
    actor_starts: list = field(default_factory=list)  # (actor, line, args) per declared starter call


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
# head -> (position of the table argument in the form, access kind)
SYNC_TABLE_OPS = {"gethash": (2, "r"), "remhash": (2, "w"), "clrhash": (1, "w"), "hash-table-count": (1, "r")}
BINDING_FORMS = {"let", "let*", "sb-int:dx-let"}
FUNCALLERS = {"funcall", "apply", "multiple-value-call"}
# env value marking "this name is the current defun's parameter" (walk_if)
PARAM_MARKER = ("param",)
# env value ("flet-lambda", form): this flet parameter is a lambda the flet
# funcalls synchronously. The form is not a free variable of that lambda.
# forms that can change a variable's value: if the tested parameter is
# written anywhere in its defun, its if-arms are not tagged (the value the
# test reads may not be the value the caller passed)
WRITE_HEADS = {"setq", "setf", "psetf", "psetq", "multiple-value-setq", "incf", "decf",
               "push", "pushnew", "pop", "rotatef", "shiftf"}


def _literal_params(cparams: list, args: list) -> dict:
    """Map callee parameter names to their literal truthiness where the
    argument is self-evaluating (t, nil, keywords, numbers, strings).
    Anything else is unknown and stays out: an unknown discriminator
    keeps every conditional run route live (conservative)."""
    lits: dict = {}
    for k, a in enumerate(args):
        if k >= len(cparams):
            break
        if isinstance(a, Sym):
            s = str(a)
            if s in ("t", "nil"):
                lits[cparams[k]] = (s == "t")
            elif s.startswith(":"):
                lits[cparams[k]] = True
        elif isinstance(a, bool):
            lits[cparams[k]] = a
        elif isinstance(a, (int, float)):
            lits[cparams[k]] = True
        elif isinstance(a, str) and not isinstance(a, Sym):
            lits[cparams[k]] = True
    return lits
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
        self.param_routes: dict = {}  # (fn, param) -> [(locks, gated, scope, cond)] per run site
        self.flet_scopes: list = []   # active flet/labels scopes (innermost last)
        self.run_targets: list = []   # (fn, param) of the argument position a walked closure was passed at
        self._writes_cache: dict = {}  # fn name -> frozenset of names its body writes
        self.cur_def = None
        self.rebound: list = []       # specials let-bound around the form being walked
        self.dead_guards: list = []   # thread-not-alive guards around the form being walked
        self.defer_vars: list = []    # variables whose captured conditions are rethrown on every exit path
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

    def wait_wrapper_problem(self, name: str, idx: int) -> str | None:
        """None when every sb-thread:condition-wait in the declared wrapper NAME waits
        on its own parameter number IDX (so the wrapper releases the mutex its
        caller passes, exactly as the primitive does); else why not."""
        d = self.tree.defs[name]
        params = [str(p) for p in lambda_params(d.params)]
        if idx >= len(params):
            return "mutex_arg out of range"
        waits = []

        def scan(x):
            if isinstance(x, list):
                if head(x) == "sb-thread:condition-wait":
                    waits.append(x)
                for y in x:
                    scan(y)
        scan(d.body)
        if not waits:
            return "no condition-wait in its body"
        for w in waits:
            if len(w) < 3 or not isinstance(w[2], Sym) or str(w[2]) != params[idx]:
                return "a condition-wait does not wait on parameter " + params[idx]
        return None

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
        other unquote a distinct opaque symbol.  Repeated references to the same
        macro-local symbol keep one identity; no expression is evaluated."""
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

        opaque_symbols = {}
        expansion_id = (getattr(form, "identity", self.cur.name) + "::" + d.name)

        def opaque(expr):
            # Local gensym variables are opaque, but distinct variables must
            # not alias: a later NIL bookkeeping binding is not the mutex.
            # Computed unquotes remain unknown; never interpret macro code.
            key = ("symbol", str(expr)) if isinstance(expr, Sym) else (
                "expression", getattr(expr, "identity", render(expr)))
            if key not in opaque_symbols:
                opaque_symbols[key] = Sym("#:opaque:" + expansion_id + ":" + str(len(opaque_symbols)))
            return opaque_symbols[key]

        def mapcar_template(expr):
            """`,@(mapcar (lambda (VAR) `TEMPLATE) PARAM)' with PARAM a macro
            &body/&rest parameter: one TEMPLATE per argument, VAR bound to that
            argument (fnn-unwind-cleanups' cleanup forms).  Anything else the
            splice computes stays unexpanded, exactly as before."""
            if not (isinstance(expr, list) and head(expr) == "mapcar" and len(expr) == 3):
                return None
            fn, seq = expr[1], expr[2]
            if not (isinstance(fn, list) and head(fn) == "lambda" and len(fn) == 3
                    and isinstance(fn[1], list) and len(fn[1]) == 1 and isinstance(fn[1][0], Sym)
                    and isinstance(fn[2], list) and head(fn[2]) == "quasiquote" and len(fn[2]) == 2):
                return None
            var, items = str(fn[1][0]), binding.get(sym(seq))
            if items is None or items[0] != "many":
                return None
            saved = binding.get(var)
            expanded = []
            for arg in items[1]:
                binding[var] = ("one", arg)
                expanded.append(sub(fn[2][1]))
            if saved is None:
                binding.pop(var, None)
            else:
                binding[var] = saved
            return expanded

        def conditional_template(expr):
            """`,(if TEST `THEN `ELSE)' where each arm is a backquote template (or
            a literal NIL/absent) and TEST is a macro parameter: a literal NIL
            argument selects ELSE, any other literal (T, a keyword, a number) selects
            THEN; an argument that is itself computed selects neither provably, so
            the expansion is both arms in a PROGN (each is walked; events common to
            both are deduplicated).  Any other computed unquote stays opaque."""
            if not (isinstance(expr, list) and head(expr) == "if" and len(expr) in (3, 4)):
                return None
            arms = []
            for arm in list(expr[2:]) + [Sym("nil")] * (4 - len(expr)):
                if isinstance(arm, list) and head(arm) == "quasiquote" and len(arm) == 2:
                    arms.append(arm[1])
                elif isinstance(arm, Sym) and str(arm) == "nil":
                    arms.append(Sym("nil"))
                else:
                    return None
            test = expr[1]
            if not (isinstance(test, Sym) and str(test) in binding and binding[str(test)][0] == "one"):
                return None
            val = binding[str(test)][1]
            if isinstance(val, Sym) and str(val) == "nil":
                return sub(arms[1])
            literal = (isinstance(val, Sym) and (str(val) == "t" or str(val).startswith(":"))) or \
                (not isinstance(val, (Sym, list)))
            if literal:
                return sub(arms[0])
            out = Node([Sym("progn"), sub(arms[0]), sub(arms[1])])
            out.line = getattr(form, "line", 0)
            return out

        def sub(t):
            if isinstance(t, list):
                h = head(t)
                if h == "unquote" and len(t) == 2:
                    chosen = conditional_template(t[1])
                    if chosen is not None:
                        return chosen
                    if isinstance(t[1], Sym) and str(t[1]) in binding and binding[str(t[1])][0] == "one":
                        return binding[str(t[1])][1]
                    return opaque(t[1])
                out = Node()
                out.line = getattr(form, "line", 0)
                out.identity = (getattr(form, "identity", self.cur.name) + "::" + d.name
                                + "::" + getattr(t, "identity", "template"))
                for item in t:
                    if isinstance(item, list) and head(item) == "unquote-splicing" and len(item) == 2:
                        spliced = mapcar_template(item[1])
                        if spliced is not None:
                            out.extend(spliced)
                            continue
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
        self.cur_def = d
        self.defer_vars = []
        self.rebound = []
        self.dead_guards = []
        self.recording = record
        if not record:
            self.pass1_name = name
        env = dict(env or {})
        for p in info.params:
            # the marker lets walk_if see that a tested symbol IS this
            # defun's parameter and not a shadowing local: every other
            # binding form stores None, an init form, or a flet entry
            env[p] = PARAM_MARKER
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
                k = (e.kind, e.name, e.line, e.ctx, e.bound, e.atomic, e.dead, e.arg0, render(e.extra, 200) if isinstance(e.extra, list) else repr(e.extra))
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

    def ev(self, kind, name, line, ctx, extra=None, atomic=False, arg0=""):
        if self.recording:
            self.cur.events.append(Event(kind, name, line, ctx, extra, frozenset(self.rebound), atomic,
                                         tuple(self.dead_guards), arg0))

    @staticmethod
    def _holding_release_cleanup(cleanup, lockform) -> bool:
        """CLEANUP is exactly (when (holding-mutex-p L) (release-mutex L)) for
        the very lock expression the grab named."""
        if not (isinstance(cleanup, list) and len(cleanup) == 3 and head(cleanup) == "when"):
            return False
        test, act = cleanup[1], cleanup[2]
        want = render(lockform)
        return (isinstance(test, list) and len(test) == 2 and head(test) == "sb-thread:holding-mutex-p"
                and render(test[1]) == want
                and isinstance(act, list) and len(act) == 2 and head(act) == "sb-thread:release-mutex"
                and render(act[1]) == want)

    def walk_body(self, forms, ctx, env, line):
        parts = []
        forms = list(forms)
        i = 0
        while i < len(forms):
            f = forms[i]
            # (grab-mutex L) directly followed by (unwind-protect BODY (when
            # (holding-mutex-p L) (release-mutex L))) is a critical section of L:
            # BODY runs holding L (a timed condition-wait may return without
            # it; the re-grab is the (unless (holding-mutex-p L) (grab-mutex L))
            # form, a no-op under the held model), and the cleanup releases
            # exactly L.  Any other manual grab stays unresolved.
            if (isinstance(f, list) and len(f) == 2 and head(f) == "sb-thread:grab-mutex"
                    and i + 1 < len(forms)):
                nxt = forms[i + 1]
                if (isinstance(nxt, list) and len(nxt) == 3 and head(nxt) == "unwind-protect"
                        and self._holding_release_cleanup(nxt[2], f[1])):
                    lock = self.lock_of(f[1], env)
                    ln = line_of(f, line)
                    self.ev("acq", lock, ln, ctx, "sb-thread:with-mutex")
                    if lock.startswith("?"):
                        self.ev("unresolved", "lock object " + lock[1:], ln, ctx)
                    inner = Ctx(ctx.locks | {lock}, ctx.noio, ctx.scope, ctx.gated, ctx.ignore, ctx.cond)
                    parts.append(self.walk(nxt[1], inner, env, line_of(nxt, ln)))
                    i += 2
                    continue
            parts.append(self.walk(f, ctx, env, line_of(f, line)))
            i += 1
        return sig_union(parts)

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
        if (h == "unless" and len(form) == 3 and isinstance(form[1], list) and len(form[1]) == 2
                and head(form[1]) == "sb-thread:holding-mutex-p"
                and isinstance(form[2], list) and len(form[2]) == 2
                and head(form[2]) == "sb-thread:grab-mutex"
                and render(form[1][1]) == render(form[2][1])
                and self.lock_of(form[2][1], env) in ctx.locks):
            # re-grab of a lock this region already holds, run only when it
            # is not held: restores the held state the model assumes
            return EMPTY_SIG
        if h == "unless" and len(form) > 2 and self.dead_test(form[1]) is not None:
            guard = self.dead_ties(self.dead_test(form[1]), env)
            parts = [self.walk(form[1], ctx, env, line)]
            self.dead_guards.append(guard)
            try:
                parts.append(self.walk_body(form[2:], ctx, env, line))
            finally:
                self.dead_guards.pop()
            return sig_union(parts)
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
        if h in SYNC_TABLE_OPS and len(form) > SYNC_TABLE_OPS[h][0]:
            pos, kind = SYNC_TABLE_OPS[h]
            table = form[pos]
            if isinstance(table, Sym) and str(table) in self.tree.synchronized and str(table) not in env:
                self.ev("acc", str(table), line, ctx, kind, True)
                return sig_union([self.walk(x, ctx, env, line) for k, x in enumerate(form[1:], 1) if k != pos])
        if h in ("flet", "labels", "macrolet"):
            env2 = dict(env)
            parts = []
            entries = {}
            for fdef in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
                if isinstance(fdef, list) and len(fdef) >= 2:
                    fname = sym(fdef[0])
                    if fname and fname not in entries:
                        entries[fname] = (fdef[1] if isinstance(fdef[1], list) else [], fdef[2:])
            body_forms = form[2:]
            # A per-reference flet (name -> (params, body)) is walked once at
            # EACH reference instead of once at its definition, so its run
            # sites record the context of the site that reaches them.  Names
            # that are referenced from a sibling definition (labels-style
            # recursion), passed as #'NAME to anything but a known defun, or
            # never referenced keep today's definition-site walk: scope[name]
            # is None for them.
            scope = dict.fromkeys(entries, None)
            if h != "macrolet":
                refs = self._flet_references(entries, body_forms)
                for fname in entries:
                    r = refs.get(fname)
                    if r and not r["sibling"] and r["dirty"] == 0 and (r["head"] or r["clean"]):
                        scope[fname] = entries[fname]
            self.flet_scopes.append(scope)
            try:
                for fname, entry in entries.items():
                    if scope[fname] is None:
                        e3 = dict(env2)
                        for p in lambda_params(entry[0]):
                            e3[p] = None
                        parts.append(self.walk_body(entry[1], ctx, e3, line))
                parts.append(self.walk_body(body_forms, ctx, env2, line))
            finally:
                self.flet_scopes.pop()
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
            self.add_handler(line, inner, [(("error",), False, EMPTY_SIG, frozenset(), "ignore-errors", [])], ctx)
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
        if h in self.tree.actors:
            return self.walk_actor_start(form, h, form[1:], ctx, env, line)
        if h == "funcall" and len(form) > 1 and self.funcalled_actors(form[1]):
            parts = [self.walk_actor_start(form, a, form[2:], ctx, env, line)
                     for a in self.funcalled_actors(form[1])]
            return sig_union(parts + [self.walk(form[1], ctx, env, line)])
        if h == "sb-thread:condition-wait":
            lock = self.lock_of(form[2], env) if len(form) > 2 else "?"
            self.ev("leaf", "sb-thread:condition-wait", line, ctx, ("await", lock))
            return self.walk_body(form[1:], ctx, env, line)
        wrapper = self.c.raw.get("condition_wait_wrappers", {}).get(h)
        if wrapper is not None and h in self.tree.defs:
            idx = wrapper["mutex_arg"]
            problem = self.wait_wrapper_problem(h, idx)
            if problem:
                self.ev("unresolved", "condition-wait wrapper " + h + ": " + problem, line, ctx)
                lock = "?"
            else:
                lock = self.lock_of(form[idx + 1], env) if len(form) > idx + 1 else "?"
            # the call edge stays (actors, lock context, the wrapper's other
            # effects); the blocking closure drops the wrapper's own wait leaf
            self.ev("leaf", "sb-thread:condition-wait", line, ctx, ("await", lock, "wrapper-site"))
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

    def _flet_references(self, entries: dict, body_forms) -> dict:
        """Count, per flet name, how the scope body and the sibling
        definitions reference it: head position (a direct call), #'NAME in
        an argument position of a known defun (clean), #'NAME anywhere else
        (dirty: stored, funcalled, passed to an unknown function), and any
        reference from a sibling definition's body."""
        names = set(entries)
        refs = {n: {"head": 0, "clean": 0, "dirty": 0, "sibling": False} for n in names}

        def scan(f, parent_head, in_fdef):
            if not isinstance(f, list) or not f:
                return
            h = head(f)
            if h in names:
                if in_fdef:
                    refs[h]["sibling"] = True
                else:
                    refs[h]["head"] += 1
            if h == "function" and len(f) > 1 and isinstance(f[1], Sym) and str(f[1]) in names:
                n = str(f[1])
                if in_fdef:
                    refs[n]["sibling"] = True
                elif parent_head in self.tree.defs and parent_head not in FUNCALLERS:
                    refs[n]["clean"] += 1
                else:
                    refs[n]["dirty"] += 1
            if h not in SPECIAL_SKIP:
                for el in f:
                    if isinstance(el, list):
                        scan(el, h, in_fdef)

        for stmt in body_forms:
            scan(stmt, None, False)
        for entry in entries.values():
            for stmt in entry[1]:
                scan(stmt, None, True)
        return refs

    def _lookup_flet(self, name: str):
        """The per-reference closure of NAME from the innermost flet scope
        that binds it, or None when absent or when that scope walks the
        definition in place (shadowing still stops the search)."""
        for sc in reversed(self.flet_scopes):
            if name in sc:
                return sc[name]
        return None

    def _flet_param_uses(self, params: list, body_forms) -> dict:
        """How an flet body uses each parameter: 'sync' when every mention is
        the operator of funcall/apply (the argument runs at that funcall, on
        this call), 'escapes' when the parameter is stored, returned, passed
        on or bound over, 'dead' when it is not mentioned. Only a 'sync'
        parameter's lambda is inlined; an escaping one stays a stored
        callback with a fresh lockset."""
        names = set(params)
        uses = {p: "dead" for p in params}

        def note(name: str, kind: str) -> None:
            if uses[name] == "escapes":
                return
            if kind == "escapes" or uses[name] == "dead":
                uses[name] = kind

        def scan(f) -> None:
            if isinstance(f, Sym):
                n = str(f)
                if n in names:
                    note(n, "escapes")
                return
            if not isinstance(f, list) or not f:
                return
            h = head(f)
            if h in SPECIAL_SKIP:
                return
            if h in FUNCALLERS and len(f) > 1 and isinstance(f[1], Sym) and str(f[1]) in names:
                note(str(f[1]), "sync")
                for el in f[2:]:
                    scan(el)
                return
            if h == "function" and len(f) > 1 and isinstance(f[1], Sym) and str(f[1]) in names:
                note(str(f[1]), "escapes")
                return
            for el in f:
                scan(el)

        for stmt in body_forms:
            scan(stmt)
        return uses

    @staticmethod
    def dead_test(test):
        """T for a test `(thread-alive-p T)' or `(and T (thread-alive-p T))' (an
        `unless' body then runs only when no thread T is running), else None."""
        if isinstance(test, list) and head(test) == "and" and len(test) == 3 and isinstance(test[1], Sym) \
                and test[1] == sym(test[2][1] if isinstance(test[2], list) and len(test[2]) > 1 else None):
            test = test[2]
        if isinstance(test, list) and head(test) == "sb-thread:thread-alive-p" and len(test) == 2 \
                and isinstance(test[1], Sym):
            return str(test[1])
        return None

    @staticmethod
    def dead_ties(thread_var, env):
        """THREAD-VAR and every name its binding forms mention, two bindings deep:
        what the guarded thread is looked up from."""
        def names(form, out):
            if isinstance(form, Sym):
                out.add(str(form))
            elif isinstance(form, list):
                for x in form:
                    names(x, out)
        out = {thread_var}
        for _ in range(2):
            for n in list(out):
                init = env.get(n)
                if isinstance(init, list):
                    names(init, out)
        return frozenset(out)

    def walk_flet_body(self, entry, ctx, env, line, bound=None):
        fparams, fbody = entry
        env2 = dict(env)
        for p in lambda_params(fparams):
            env2[p] = None
        for name, form in (bound or {}).items():
            env2[name] = ("flet-lambda", form)
        return self.walk_body(fbody, ctx, env2, line)

    def walk_binding(self, form, h, ctx, env, line):
        env2 = dict(env)
        parts = []
        noio = ctx.noio
        cond2 = ctx.cond
        rebinds = []
        if h in BINDING_FORMS:
            for b in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
                if isinstance(b, list) and b:
                    name = str(b[0])
                    init = b[1] if len(b) > 1 else None
                    parts.append(self.walk(init, ctx if h != "let*" else Ctx(ctx.locks, noio, ctx.scope, ctx.gated, ctx.ignore, ctx.cond), env2 if h == "let*" else env, line))
                    if name == "*fnn-extent-no-io*":
                        noio = not (init is None or (isinstance(init, Sym) and str(init) == "nil"))
                    elif name.startswith("*") and name in self.tree.globals:
                        rebinds.append(name)
                    else:
                        env2[name] = init
                        if cond2 and cond2[0] == name:
                            cond2 = None      # the binding shadows the tested parameter
                elif isinstance(b, Sym):
                    env2[str(b)] = None
            body = form[2:]
        else:
            vars_ = form[1] if len(form) > 1 else []
            for v in (lambda_params(vars_) if isinstance(vars_, list) else []):
                env2[v] = None
                if cond2 and cond2[0] == v:
                    cond2 = None
            if len(form) > 2:
                parts.append(self.walk(form[2], ctx, env, line))
            body = form[3:]
        ctx2 = Ctx(ctx.locks, noio, ctx.scope, ctx.gated, ctx.ignore, cond2)
        deferred = self._deferred_rethrow_vars(
            [str(b[0]) if isinstance(b, list) and b else str(b) for b in
             (form[1] if h in BINDING_FORMS and len(form) > 1 and isinstance(form[1], list) else [])], body)
        mark = len(self.defer_vars)
        rmark = len(self.rebound)
        self.defer_vars.extend(deferred)
        self.rebound.extend(rebinds)
        try:
            parts.append(self.walk_body(body, ctx2, env2, line))
        finally:
            del self.defer_vars[mark:]
            del self.rebound[rmark:]
        return sig_union(parts)

    EXIT_HEADS = {"return-from", "return", "go", "throw"}

    def _has_exit(self, forms) -> bool:
        stack = list(forms)
        while stack:
            x = stack.pop()
            if isinstance(x, list) and x:
                if head(x) in ("quote", "lambda", "function"):
                    continue
                if head(x) in self.EXIT_HEADS:
                    return True
                stack.extend(x)
        return False

    def _terminal_rethrow(self, form, var: str, fences: set) -> bool:
        """FORM always ends in a re-signal of VAR's captured condition (or
        a declared fence call): (error ...VAR...), a fence call, an if whose
        two arms are both terminal, or a progn whose last form is."""
        if not isinstance(form, list) or not form:
            return False
        h = head(form)
        if h in ("error", "signal"):
            return any(isinstance(x, Sym) and str(x) == var for x in self._flat(form[1:]))
        if h in fences:
            return True
        if h == "if" and len(form) == 4:
            return self._terminal_rethrow(form[2], var, fences) and self._terminal_rethrow(form[3], var, fences)
        if h == "progn" and len(form) > 1:
            return self._terminal_rethrow(form[-1], var, fences)
        return False

    @staticmethod
    def _flat(forms):
        stack = list(forms)
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                stack.extend(x)
            else:
                yield x

    def _deferred_rethrow_vars(self, names, body) -> set:
        """Variables V bound by this let whose captured conditions are
        re-signalled on EVERY exit path of the let body: the body's final
        form (or, for an unwind-protect, its last cleanup form, which every
        exit including a throw runs) is (when V ...) / (if V ...) whose
        taken arm is terminal (error naming V, or a fence call); no form
        that runs between the captures and that tail can leave the body
        (return-from, return, go, throw); V is never reset to nil; and the
        test is V itself, not a conjunction."""
        if not names or not body:
            return set()
        # a dominated-escape function (contract dominated_escape_functions)
        # returns only when the escape already in flight outranks every
        # recorded failure, and signals otherwise: terminal like a fence call
        fences = set(self.c.raw.get("fence_functions", [])) | set(self.c.raw.get("dominated_escape_functions", {}))
        last = body[-1]
        if isinstance(last, list) and head(last) == "unwind-protect" and len(last) > 2:
            tail, between = last[-1], list(body[:-1]) + list(last[2:-1])
        else:
            tail, between = last, list(body[:-1])
        if not (isinstance(tail, list) and head(tail) in ("when", "if") and len(tail) > 2
                and isinstance(tail[1], Sym)):
            return set()
        var = str(tail[1])
        if var not in names:
            return set()
        arms = tail[2:] if head(tail) == "when" else tail[2:3] + ([tail[3]] if len(tail) > 3 else [])
        if head(tail) == "if" and len(tail) != 4:
            return set()
        if head(tail) == "if":
            if not self._terminal_rethrow(tail[2], var, fences):
                return set()
        else:
            if not self._terminal_rethrow(tail[-1], var, fences):
                return set()
        if self._has_exit(between):
            return set()
        for f in self._flat_forms(between):
            if head(f) in ("setq", "setf") and len(f) == 3 and sym(f[1]) == var \
                    and isinstance(f[2], Sym) and str(f[2]) == "nil":
                return set()
        return {var}

    @staticmethod
    def _flat_forms(forms):
        stack = list(forms)
        while stack:
            x = stack.pop()
            if isinstance(x, list) and x:
                yield x
                stack.extend(x)

    def _captures_deferred(self, clause_body, cvar) -> bool:
        """The clause body stores its condition variable CVAR into a variable
        whose rethrow is deferred to the let tail."""
        for f in self._flat_forms(clause_body):
            h = head(f)
            if h in ("push", "pushnew") and len(f) == 3 and sym(f[1]) == cvar and sym(f[2]) in self.defer_vars:
                return True
            if h in ("setq", "setf") and len(f) == 3 and sym(f[2]) == cvar and sym(f[1]) in self.defer_vars:
                return True
        return False

    def _retag(self, ctx: Ctx, cond: tuple) -> Ctx:
        """The innermost test governs: entering an arm of (if PARAM ...)
        replaces any outer arm condition (sound: a route is excluded only
        by a literal contradicting its own arm's test, and an arm's test
        implies every enclosing test it sits under)."""
        return Ctx(ctx.locks, ctx.noio, ctx.scope, ctx.gated, ctx.ignore, cond)

    def _written_names(self) -> frozenset:
        d = self.cur_def
        if d is None:
            return frozenset()
        cached = self._writes_cache.get(d.name)
        if cached is None:
            names: set = set()

            def scan(f):
                if isinstance(f, list) and f:
                    if head(f) in WRITE_HEADS:
                        for el in f[1:]:
                            if isinstance(el, Sym):
                                names.add(str(el))
                            elif isinstance(el, list) and (head(f) == "multiple-value-setq"
                                                           or head(el) == "values"):
                                # (multiple-value-setq (a b) ...) / (setf (values a b) ...)
                                names.update(str(x) for x in el if isinstance(x, Sym))
                    if head(f) != "quote":
                        for el in f:
                            scan(el)

            for stmt in (d.body or []):
                scan(stmt)
            cached = frozenset(names)
            self._writes_cache[d.name] = cached
        return cached

    def walk_if(self, form, ctx, env, line):
        test = form[1] if len(form) > 1 else None
        if isinstance(test, Sym) and str(test) == "*fnn-extent-no-io*":
            parts = []
            if ctx.noio is not False and len(form) > 2:
                parts.append(self.walk(form[2], Ctx(ctx.locks, True, ctx.scope, ctx.gated, ctx.ignore, ctx.cond), env, line))
            if ctx.noio is not True and len(form) > 3:
                parts.append(self.walk_body(form[3:], Ctx(ctx.locks, False, ctx.scope, ctx.gated, ctx.ignore, ctx.cond), env, line))
            return sig_union(parts)
        # (if PARAM ...) / (if (not PARAM) ...): each arm runs only under
        # that truthiness of the defun's PARAMETER.  A call site that passes
        # a literal for PARAM can rule the contradicted arm's routes out
        # (this only ever REMOVES routes from consideration, never adds a
        # lock).  No tag when the parameter is written anywhere in the
        # defun, or when the tested symbol is a shadowing local.
        tag = None
        if isinstance(test, Sym) and env.get(str(test)) is PARAM_MARKER:
            tag = (str(test), True)
        elif (isinstance(test, list) and head(test) == "not" and len(test) > 1
              and isinstance(test[1], Sym) and env.get(str(test[1])) is PARAM_MARKER):
            tag = (str(test[1]), False)
        if tag and tag[0] not in self._written_names():
            parts = []
            if len(form) > 2:
                parts.append(self.walk(form[2], self._retag(ctx, tag), env, line))
            if len(form) > 3:
                parts.append(self.walk_body(form[3:], self._retag(ctx, (tag[0], not tag[1])), env, line))
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
                parts.append(self.note_place(pairs[k], ctx, env, line, value=pairs[k + 1], atomic_ok=True))
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

    def note_place(self, place, ctx, env, line, value=None, pushed=None, atomic_ok=False):
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
                for k, x in enumerate(place[1:], 1):
                    if isinstance(x, Sym) and str(x) in self.tree.globals and str(x) not in env:
                        self.ev("acc", str(x), line, ctx, "w",
                                atomic_ok and h == "gethash" and k == 2 and str(x) in self.tree.synchronized)
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
        inner = Ctx(ctx.locks | {lock}, ctx.noio, ctx.scope, ctx.gated, ctx.ignore, ctx.cond)
        return self.walk_body(form[2:], inner, env, line)

    def walk_gated_body(self, form, ctx, env, line):
        cls = self.gate_class
        inner = Ctx(ctx.locks, ctx.noio, None, cls, ctx.ignore, ctx.cond)
        sig = self.walk_body(form[1:], inner, env, line)
        # a gated macro declared "fenced" wraps its body in the shared-action
        # boundary by its own template (fnn-section-envelope): the body runs
        # inside the fence by construction, not by what it calls.
        if self.recording and not getattr(self, "gate_fenced", False):
            self.cur.gated.append((line, cls, sig, ctx))
        return sig

    def walk_make_thread(self, form, ctx, env, line):
        fn = form[1] if len(form) > 1 else None
        # a declared identity-on-its-thunk wrapper (fnn-native-observed-thread-
        # thunk: returns THUNK, or a lambda that rebinds two specials and funcalls
        # it) makes the thread run its first argument
        while (isinstance(fn, list) and len(fn) > 1 and head(fn)
               and head(fn) in self.c.raw.get("thread_thunk_wrappers", [])):
            fn = fn[1]
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
                saved = (self.cur, self.recording, self.rebound, self.defer_vars, self.dead_guards)
                info = self.walk_def(rid, lam, True, thread_of=(creator.name, line, tname))
                self.cur, self.recording, self.rebound, self.defer_vars, self.dead_guards = saved
            self.ev("thread", rid, line, ctx, tname)
        else:
            self.ev("unresolved", "make-thread of a computed function " + render(fn, 40), line, ctx)
        return EMPTY_SIG

    def funcalled_actors(self, fn) -> list:
        """The declared actors a funcall's function form names: #'A, or each
        arm of an (if C #'A #'B)."""
        if head(fn) == "function" and len(fn) > 1 and sym(fn[1]) in self.tree.actors:
            return [sym(fn[1])]
        if head(fn) == "if" and len(fn) == 4:
            arms = [self.funcalled_actors(x) for x in fn[2:]]
            if all(len(a) == 1 for a in arms):
                return [a[0] for a in arms]
        return []

    def walk_actor_start(self, form, actor, args, ctx, env, line):
        """A declared actor's starter: THUNK (the third argument) runs as the
        actor's thread; the other arguments are walked as values (the escape
        and the physical callbacks run later, on that thread or its joiner)."""
        tname = self.tree.actors[actor][3]
        parts = []
        for k, a in enumerate(args):
            if k == 2:
                continue
            if (k == ACTOR_BEFORE_START_ARG and isinstance(a, list) and head(a) == "lambda"):
                # the starter funcalls BEFORE-START on the caller's thread,
                # inside fnn-owner-actor-start's own critical section
                # (owner.lisp:1778-1785): the callee's context for that
                # parameter, not a stored callback
                pctx = self.param_ctx.get((ACTOR_RUNNER, "before-start"))
                extra = pctx if isinstance(pctx, Ctx) else Ctx()
                inner = Ctx(ctx.locks | extra.locks, ctx.noio, extra.scope or ctx.scope,
                            extra.gated or ctx.gated, ctx.ignore, ctx.cond)
                parts.append(self.walk_lambda_inline(a, inner, env, line))
                continue
            parts.append(self.walk(a, ctx, env, line))
        if len(args) > 2:
            spawn = Node([Sym("sb-thread:make-thread"), args[2], Sym(":name"), tname])
            spawn.line = line_of(form, line)
            spawn.identity = getattr(form, "identity", None) or getattr(args[2], "identity", None)
            parts.append(self.walk_make_thread(spawn, ctx, env, line))
        if self.recording:
            self.cur.actor_starts.append((actor, line_of(form, line), list(args)))
        return sig_union(parts)

    def spawn_lambda(self, lam, line, thread_of, env):
        identity = getattr(lam, "identity", None)
        if identity is None:
            raise ValueError(f"lambda lacks a lexical identity at {self.cur.path}:{line_of(lam, line)}")
        rid = "lambda@" + self.cur.path + ":" + identity

        if not self.recording:
            return rid
        d = Def(rid, self.cur.path, line_of(lam, line), lam[1] if len(lam) > 1 else [], list(lam[2:]),
                "lambda", "", self.cur.loaded)
        saved = (self.cur, self.cur_def, self.recording, getattr(self, "gate_class", None), self.defer_vars,
                 self.rebound, self.dead_guards)
        self.walk_def(rid, d, True, thread_of=thread_of, env={k: None for k in env})
        (self.cur, self.cur_def, self.recording, self.gate_class, self.defer_vars,
         self.rebound, self.dead_guards) = saved
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
                if not rethrows and self.defer_vars:
                    rethrows = self._captures_deferred(cl[2:], var)
            clauses.append((types, rethrows, body))
            recorded.append((types, rethrows, body, direct_symbols(cl[2:]), render(tspec, 60), cl[2:]))
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
        # a locally defined flet fn walked per reference (see the flet branch
        # of walk): its body runs here, under the call site's context.
        # A lambda passed to a parameter the flet only funcalls is not a
        # stored callback: walking it with walk() would spawn an async root
        # and attribute the body to a thread that does not exist.
        if h not in self.tree.defs:
            fl = self._lookup_flet(h)
            if fl is not None:
                fparams = lambda_params(fl[0])
                uses = self._flet_param_uses(fparams, fl[1])
                bound = {}
                for i, a in enumerate(args):
                    pname = fparams[i] if i < len(fparams) else None
                    if (pname and uses.get(pname) == "sync" and isinstance(a, list)
                            and head(a) == "lambda"):
                        bound[pname] = a
                        continue
                    parts.append(self.walk(a, ctx, env, line))
                parts.append(self.walk_flet_body(fl, ctx, env, line, bound))
                return sig_union(parts)
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
                bound_form = env[str(target)]
                if (isinstance(bound_form, tuple) and len(bound_form) == 2
                        and bound_form[0] == "flet-lambda"):
                    # the lambda runs at this funcall. Its free variables are
                    # the caller's, not the flet parameters bound to lambdas.
                    outer = {k: v for k, v in env.items()
                             if not (isinstance(v, tuple) and len(v) == 2 and v[0] == "flet-lambda")}
                    parts.append(self.walk_lambda_inline(bound_form[1], ctx, outer, line))
                    parts.extend(self.walk(a, ctx, env, line) for a in args[1:])
                    return sig_union(parts)
                pname = str(target)
                if not self.recording and pname in self.cur.params:
                    # a run site lexically inside a closure that was passed
                    # at argument position (FN, PARAM) also runs under that
                    # callee's own context for that parameter (solve joins
                    # it, exactly like a "pass" row)
                    row = ("run", ctx)
                    if self.run_targets and isinstance(self.run_targets[-1], tuple):
                        row = ("run", ctx, self.run_targets[-1])
                    self.param_sites.setdefault((self.pass1_name, pname), []).append(row)
                elif self.recording and pname not in self.cur.params:
                    self.ev("callback", pname, line, ctx)
                elif self.recording:
                    self.ev("callback-param", pname, line, ctx)
            elif quoted_symbol(target) and quoted_symbol(target) in self.tree.defs:
                self.ev("call", quoted_symbol(target), line, ctx, "funcall")
                parts.append(("u", frozenset(), (quoted_symbol(target),), ()))
        if h in self.tree.defs:
            self.ev("call", h, line, ctx, arg0=str(args[0]) if args and isinstance(args[0], Sym) else "")
            parts.append(("u", frozenset(), (h,), ()))
            callee = self.tree.defs[h]
            cparams = lambda_params(callee.params)
            # literal argument values, for resolving conditional run routes
            lits = _literal_params(cparams, args)
            for k, a in enumerate(args):
                pname = cparams[k] if k < len(cparams) else None
                if isinstance(a, list) and head(a) == "lambda":
                    pctx = self.resolve_param_ctx(h, pname, lits) if pname else None
                    if pctx == "async" or pctx is None and self.recording and not self.runs_param(h, pname):
                        rid = self.spawn_lambda(a, line, None, env)
                        self.ev("async", rid, line, ctx, h)
                    else:
                        extra = pctx if isinstance(pctx, Ctx) else Ctx()
                        inner = Ctx(ctx.locks | extra.locks, ctx.noio, extra.scope or ctx.scope,
                                    self.resolve_class(extra.gated, callee, args) or ctx.gated, ctx.ignore, ctx.cond)
                        if pname:
                            self.run_targets.append((h, pname))
                        try:
                            parts.append(self.walk_lambda_inline(a, inner, env, line))
                        finally:
                            if pname:
                                self.run_targets.pop()
                    continue
                if isinstance(a, list) and head(a) == "function" and isinstance(a[1], Sym) \
                        and sym(a[1]) in self.tree.defs:
                    pctx = self.resolve_param_ctx(h, pname, lits) if pname else None
                    extra = pctx if isinstance(pctx, Ctx) else Ctx()
                    inner = Ctx(ctx.locks | extra.locks, ctx.noio, extra.scope or ctx.scope,
                                extra.gated or ctx.gated, ctx.ignore, ctx.cond)
                    self.ev("call", sym(a[1]), line, inner, "ref")
                    parts.append(("u", frozenset(), (sym(a[1]),), ()))
                    continue
                if isinstance(a, list) and head(a) == "function" and isinstance(a[1], Sym):
                    # a per-reference flet closure passed at PARAM: its body
                    # runs under this site's context joined with the
                    # callee's context for PARAM
                    fl = self._lookup_flet(str(a[1]))
                    if fl is not None and pname:
                        pctx = self.resolve_param_ctx(h, pname, lits)
                        extra = pctx if isinstance(pctx, Ctx) else Ctx()
                        inner = Ctx(ctx.locks | extra.locks, ctx.noio, extra.scope or ctx.scope,
                                    extra.gated or ctx.gated, ctx.ignore, ctx.cond)
                        self.run_targets.append((h, pname))
                        try:
                            parts.append(self.walk_flet_body(fl, inner, env, line))
                        finally:
                            self.run_targets.pop()
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
                        ctx = row[1]
                        if len(row) == 3:
                            # the run site is inside a closure that was
                            # passed at (fn, param): it also runs under that
                            # callee's context for the parameter
                            sub = result.get(row[2])
                            if isinstance(sub, Ctx):
                                ctx = Ctx(ctx.locks | sub.locks, None, sub.scope or ctx.scope,
                                          sub.gated or ctx.gated, cond=ctx.cond)
                        ctxs.append(ctx)
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
        # per-route rows for call-site liveness resolution: exactly the
        # contexts whose intersection is param_ctx above, one per run/pass
        # site, with each site's arm condition (Ctx.cond) attached
        routes: dict = {}
        for key, rows in sites.items():
            entries = []
            for row in rows:
                if row[0] == "run":
                    ctx = row[1]
                    if len(row) == 3:
                        sub = result.get(row[2])
                        if isinstance(sub, Ctx):
                            ctx = Ctx(ctx.locks | sub.locks, None, sub.scope or ctx.scope,
                                      sub.gated or ctx.gated, cond=ctx.cond)
                    entries.append((ctx.locks, ctx.gated, ctx.scope, ctx.cond))
                else:
                    _, ctx, callee, cparam = row
                    sub = result.get((callee, cparam))
                    if isinstance(sub, Ctx):
                        entries.append((ctx.locks | sub.locks, sub.gated, sub.scope or ctx.scope, ctx.cond))
            if entries:
                routes[key] = entries
        self.param_routes = routes

    def resolve_param_ctx(self, fn: str, pname: str | None, literals: dict):
        """The context a closure passed at (FN, PNAME) runs in AT A CALL
        SITE whose literal argument values are LITERALS.  A run route
        whose arm condition is contradicted by a literal cannot reach this
        site and drops out of the intersection; every other route stays,
        so the answer is never wider than the conservative param_ctx."""
        if pname is None:
            return None
        key = (fn, pname)
        routes = self.param_routes.get(key)
        cur = self.param_ctx.get(key)
        if not routes:
            return cur
        live = []
        for locks, gated, scope, cond in routes:
            if cond is not None:
                lv = literals.get(cond[0])
                if lv is not None and lv is not cond[1]:
                    continue
            live.append((locks, gated, scope))
        if not live:
            return cur
        locks = frozenset.intersection(*[row[0] for row in live])
        gated = live[0][1] if all(r[1] == live[0][1] for r in live) else None
        scope = live[0][2] if all(r[2] == live[0][2] for r in live) else None
        return Ctx(locks, None, scope, gated)


# --------------------------------------------------------------------------
# private owner commands: the proof behind the contract row
# --------------------------------------------------------------------------

# forms whose arguments are ordinary statements: the owner passes through them
# unchanged (nothing here stores or starts anything)
_STATEMENT_FORMS = frozenset("""
progn if when unless cond case ecase typecase etypecase and or not the
block return-from return tagbody go catch throw unwind-protect
multiple-value-prog1 prog1 prog2 ignore-errors handler-bind restart-case
with-mutex sb-thread:with-mutex sb-thread:with-recursive-lock with-recursive-lock
sb-thread:with-recursive-lock with-open-file with-output-to-string
declare locally eval-when check-type assert incf decf
""".split())
_THREAD_STARTERS = frozenset(["sb-thread:make-thread", "make-thread"])
_OWNER_STARTER = re.compile(r"^fnn-owner-(?:.*-)?(?:start|spawn)")


def _strip_quasi(form):
    while isinstance(form, list) and head(form) in ("quasiquote", "unquote", "unquote-splicing") and len(form) == 2:
        form = form[1]
    return form


def _templates(form) -> list:
    """The outermost quasiquote templates under FORM."""
    if not isinstance(form, list):
        return []
    if head(form) == "quasiquote":
        return [form]
    out = []
    for x in form:
        out.extend(_templates(x))
    return out


def _mentions(form, names) -> bool:
    form = _strip_quasi(form)
    if isinstance(form, Sym):
        return str(form) in names
    if isinstance(form, list):
        if head(form) == "quote":
            return False
        return any(_mentions(x, names) for x in form)
    return False


def _bind_lambda_list(params, args, nested=False) -> dict:
    """{parameter name: [indices of the arguments it receives]} for an ordinary
    or destructuring lambda list: required, &optional, &key, &rest/&body.  A
    nested pattern against a list argument binds its names to that argument's
    elements, addressed as (index, sub-index...)."""
    out: dict = collections.defaultdict(list)
    mode = "req"
    pos = 0
    for p in params:
        if isinstance(p, Sym) and str(p).startswith("&"):
            mode = str(p)
            continue
        if mode in ("&rest", "&body"):
            name = str(p)
            for k in range(pos, len(args)):
                out[name].append((k,))
            continue
        if mode == "&key":
            name = str(p[0]) if isinstance(p, list) else str(p)
            for k in range(pos, len(args) - 1):
                if isinstance(args[k], Sym) and str(args[k]).lower() == ":" + name.lower():
                    out[name].append((k + 1,))
            continue
        if mode == "&aux":
            continue
        if isinstance(p, list) and p and mode in ("req", "&optional") and isinstance(p[0], Sym) and nested:
            if pos < len(args) and isinstance(args[pos], list):
                for name, idx in _bind_lambda_list(p, args[pos], True).items():
                    out[name].extend((pos,) + i for i in idx)
            pos += 1
            continue
        name = str(p[0]) if isinstance(p, list) else str(p)
        if pos < len(args):
            out[name].append((pos,))
        pos += 1
    return out


def _arg_at(args, idx):
    node = args
    for i in idx:
        if not isinstance(node, list) or i >= len(node):
            return None
        node = node[i]
    return node


class OwnerFlow:
    """A flow-insensitive scan of how one owner value is used.  `scan_def'
    follows it into every host function and macro it is handed to; a use that
    could publish it, store it, hand it to another thread or leave the host's
    sight is recorded as a problem.  Tainted names are never untainted
    (shadowing can only add findings, never hide one)."""

    def __init__(self, tree: Tree, row: dict) -> None:
        self.tree = tree
        self.row = row
        self.problems: list[str] = []
        self.memo: dict = {}
        self.stack: list = []
        self.pure = set(row.get("pure_callees", []))
        self.custody = set(row.get("failure_custody", []))
        self.makers = set(row.get("owner_makers", [])) | {row["constructor"]}
        self.gates = set(tree.sections) | set(row.get("gate_callees", []))
        self.starters = _THREAD_STARTERS | set(tree.actors) | {ACTOR_RUNNER}
        self.thunk_calls: dict = {}
        self.scanned: set = set()

    def problem(self, kind, st, line, text) -> None:
        where = " -> ".join(st["trail"])
        self.problems.append(f"{kind}: {text} (at {st['path']}:{line}; via {where})")

    def starter(self, h) -> bool:
        return h in self.starters or bool(_OWNER_STARTER.match(h))

    # entry points -------------------------------------------------------
    def scan_def(self, name, tparams, trail=()):
        """Scan host function or macro NAME with the parameters TPARAMS tainted;
        True when its value may be the owner."""
        d = self.tree.defs.get(name) or self.tree.macros.get(name)
        key = (name, frozenset(tparams))
        if key in self.memo:
            return self.memo[key]
        if key in self.stack:
            return False
        self.stack.append(key)
        self.scanned.add(name)
        st = {"tainted": set(tparams), "locals": set(), "dying": False, "ret": [], "runner": name,
              "trail": tuple(trail) + (name,), "path": d.path, "localfns": {}}
        params = d.params
        pat = _flatten_names(params)
        st["locals"].update(pat)
        body = list(d.body)
        if len(body) > 1 and isinstance(body[0], str) and not isinstance(body[0], Sym):
            body = body[1:]
        if d.kind == "macro":
            # the macro's own code runs at expansion time; what runs later is
            # what its quasiquote templates write
            result = False
            for template in _templates(body):
                result = self.scan(template, st) or result
        else:
            result = self.scan_body(body, st)
        result = result or any(st["ret"])
        self.stack.pop()
        self.memo[key] = result
        return result

    def scan_body(self, forms, st) -> bool:
        last = False
        for f in forms:
            last = self.scan(f, st)
        return last

    # the walk -----------------------------------------------------------
    def scan(self, form, st) -> bool:
        if isinstance(form, Sym):
            return str(form) in st["tainted"]
        if not isinstance(form, list) or not form:
            return False
        h = head(form)
        line = line_of(form, 0)
        if h == "declare":
            return False
        if h in ("unquote", "unquote-splicing") and len(form) == 2:
            if isinstance(form[1], Sym):
                return str(form[1]) in st["tainted"]
            for template in _templates(form[1]):    # an expansion-time computation: only
                self.scan(template, st)             # the code templates inside it run later
            return False
        if h == "quasiquote" and len(form) == 2:
            return self.scan(form[1], st)
        if h is None:
            if isinstance(form[0], list) and head(form[0]) == "lambda":
                return self.scan_lambda_call(form[0], form[1:], st)
            return any([self.scan(x, st) for x in form])
        if h == "quote":
            return False
        if h == "function":
            target = form[1] if len(form) > 1 else None
            if isinstance(target, list) and head(target) == "lambda":
                return self.scan_lambda_value(target, st)
            return isinstance(target, Sym) and str(target) in st["tainted"]
        if h == "lambda":
            return self.scan_lambda_value(form, st)
        if h in ("let", "let*"):
            return self.scan_let(form, st)
        if h in ("flet", "labels"):
            for entry in form[1] if len(form) > 1 and isinstance(form[1], list) else []:
                if isinstance(entry, list) and len(entry) >= 2:
                    lam = Node([Sym("lambda"), entry[1]] + list(entry[2:]))
                    lam.line = line_of(entry, line)
                    st["localfns"][str(entry[0])] = lam
                    if self.scan_lambda_value(lam, st):
                        st["tainted"].add(str(entry[0]))
            return self.scan_body(form[2:], st)
        if h in ("setq", "setf", "psetq", "psetf"):
            return self.scan_assign(form, st)
        if h in ("push", "pushnew"):
            value = self.scan(form[1], st) if len(form) > 1 else False
            place = form[2] if len(form) > 2 else None
            if len(form) > 2 and not isinstance(place, Sym):
                self.scan(place, st)
            if value:
                self.store(place, st, line, h)
            return False
        if h == "handler-case":
            result = self.scan(form[1], st) if len(form) > 1 else False
            for clause in form[2:]:
                if not isinstance(clause, list) or len(clause) < 2:
                    continue
                var = clause[1][0] if isinstance(clause[1], list) and clause[1] else None
                body = clause[2:]
                dying = bool(body) and isinstance(body[-1], list) and head(body[-1]) == "error" \
                    and len(body[-1]) == 2 and isinstance(var, Sym) and body[-1][1] == var
                if isinstance(var, Sym):
                    st["locals"].add(str(var))
                saved = st["dying"]
                st["dying"] = saved or dying
                self.scan_body(body, st)
                st["dying"] = saved
            return result
        if h == "multiple-value-bind":
            tainted = self.scan(form[2], st) if len(form) > 2 else False
            for v in form[1] if len(form) > 1 and isinstance(form[1], list) else []:
                st["locals"].add(str(v))
                if tainted:
                    st["tainted"].add(str(v))
            return self.scan_body(form[3:], st)
        if h in ("dolist", "dotimes"):
            spec = form[1] if len(form) > 1 and isinstance(form[1], list) else []
            tainted = self.scan(spec[1], st) if len(spec) > 1 else False
            if spec:
                st["locals"].add(str(spec[0]))
                if tainted:
                    st["tainted"].add(str(spec[0]))
            self.scan_body(form[2:], st)
            return False
        if h == "loop":
            return any([self.scan(x, st) for x in form[1:]])
        if h == "cond":
            out = False
            for clause in form[1:]:
                if isinstance(clause, list):
                    out = self.scan_body(clause, st) or out
            return out
        if h in ("case", "ecase", "typecase", "etypecase"):
            out = self.scan(form[1], st) if len(form) > 1 else False
            for clause in form[2:]:
                if isinstance(clause, list) and clause:
                    out = self.scan_body(clause[1:], st) or out
            return out
        if h in ("funcall", "apply"):
            return self.scan_funcall(form, st)
        if h in _STATEMENT_FORMS:
            return any([self.scan(x, st) for x in form[1:]])
        return self.scan_call(form, h, st, line)

    def scan_lambda_value(self, lam, st) -> bool:
        """A lambda in value position: its body runs where it is called; True
        when it captures the owner."""
        params = lambda_params(lam[1] if len(lam) > 1 else [])
        st["locals"].update(params)
        self.scan_body(lam[2:], st)
        return _mentions(lam, st["tainted"] - set(params)) or _mentions(lam, st["tainted"])

    def scan_lambda_call(self, lam, args, st) -> bool:
        flags = [self.scan(a, st) for a in args]
        params = lambda_params(lam[1] if len(lam) > 1 else [])
        st["locals"].update(params)
        for p, tainted in zip(params, flags):
            if tainted:
                st["tainted"].add(p)
        return self.scan_body(lam[2:], st)

    def scan_let(self, form, st) -> bool:
        for binding in form[1] if len(form) > 1 and isinstance(form[1], list) else []:
            if isinstance(binding, list) and binding:
                var = str(_strip_quasi(binding[0]))
                st["locals"].add(var)
                if len(binding) > 1 and self.scan(binding[1], st):
                    st["tainted"].add(var)
            elif isinstance(binding, Sym):
                st["locals"].add(str(binding))
        return self.scan_body(form[2:], st)

    def store(self, place, st, line, how) -> None:
        if isinstance(place, Sym):
            name = str(place)
            if name.startswith("*") or name in self.tree.globals or name not in st["locals"]:
                self.problem("published", st, line, f"the owner is stored into the global {name}")
            else:
                st["tainted"].add(name)
        else:
            self.problem("published", st, line,
                         f"the owner is stored into the place {render(place, 60)} ({how})")

    def scan_assign(self, form, st) -> bool:
        line = line_of(form, 0)
        out = False
        items = form[1:]
        for k in range(0, len(items) - 1, 2):
            place, value = items[k], items[k + 1]
            tainted = self.scan(value, st)
            if not isinstance(place, Sym):
                self.scan(place, st)
            if tainted:
                self.store(place, st, line, head(form))
            out = tainted
        return out

    def scan_funcall(self, form, st) -> bool:
        line = line_of(form, 0)
        fn = form[1] if len(form) > 1 else None
        args = form[2:]
        flags = [self.scan(a, st) for a in args]
        if isinstance(fn, list):
            target = fn[1] if head(fn) == "function" and len(fn) > 1 else None
            if isinstance(target, Sym) and (str(target) in self.tree.defs):
                return self.call_def(str(target), args, flags, st, line)
            if head(fn) == "lambda" or (head(fn) == "function" and isinstance(target, list)):
                lam = fn if head(fn) == "lambda" else target
                return self.scan_lambda_call(lam, args, st)
            self.scan(fn, st)
        if not any(flags):
            return False
        if isinstance(fn, Sym) and str(fn) in st["tainted"]:
            return False                        # calling a closure that holds the owner
        if isinstance(fn, Sym) and str(fn) == self.row.get("thunk") and st["runner"] == self.row["runner"]:
            self.thunk_calls.setdefault(st["runner"], set()).update(k for k, f in enumerate(flags) if f)
            return False
        self.problem("escaped", st, line,
                     f"the owner is passed to the computed call {render(form, 60)}")
        return False

    def scan_call(self, form, h, st, line) -> bool:
        args = form[1:]
        flags = [self.scan(a, st) for a in args]
        if h in self.makers:
            if any(flags):
                self.problem("escaped", st, line, f"{h} is handed the owner")
            if st["runner"] not in (self.row["constructor"], self.row["runner"]):
                self.problem("second-owner", st, line,
                             f"{h} makes another owner outside the constructor and the runner")
            return True
        if h in self.gates and not (flags and flags[0]):
            self.problem("second-owner", st, line,
                         f"{h} is entered on a value other than the private owner")
        if not any(flags):
            return False
        if self.starter(h):
            self.problem("thread-start", st, line,
                         f"the owner (or a closure over it) reaches {h}, a thread or actor start")
            return False
        if h in st["localfns"]:
            lam = st["localfns"][h]
            for p, tainted in zip(lambda_params(lam[1] if len(lam) > 1 else []), flags):
                if tainted:
                    st["tainted"].add(p)
            return self.scan_body(lam[2:], st)
        if h in self.custody:
            fresh = all(not f or (isinstance(a, list) and head(a) in self.makers)
                        for a, f in zip(args, flags))
            if not st["dying"] and not fresh:
                self.problem("published", st, line,
                             f"{h} keeps the owner and is called outside a failing handler clause "
                             "on anything but a freshly made throwaway")
            return False
        if h in self.tree.structs and flags[0]:
            return False
        if h in self.pure:
            return False
        if h in self.tree.defs or h in self.tree.macros:
            return self.call_def(h, args, flags, st, line)
        self.problem("escaped", st, line,
                     f"the owner is passed to {h}, which is neither a host function nor a cleared primitive")
        return False

    def call_def(self, name, args, flags, st, line) -> bool:
        macro = name in self.tree.macros and name not in self.tree.defs
        d = self.tree.macros[name] if macro else self.tree.defs[name]
        if macro:
            binding = _bind_lambda_list(d.params, args, nested=True)
            tparams = {p for p, idxs in binding.items()
                       if any(_mentions(_arg_at(args, i), st["tainted"]) for i in idxs
                              if _arg_at(args, i) is not None)}
        else:
            binding = _bind_lambda_list(d.params, args)
            tparams = {p for p, idxs in binding.items() if any(flags[i[0]] for i in idxs if i[0] < len(flags))}
            rest = [str(p) for k, p in enumerate(d.params) if k and isinstance(d.params[k - 1], Sym)
                    and str(d.params[k - 1]) in ("&rest", "&body")]
            if tparams & set(rest):
                self.problem("escaped", st, line, f"the owner is collected into {name}'s &rest list")
        if not tparams:
            return False
        result = self.scan_def(name, tparams, st["trail"])
        return result


def _flatten_names(params, mode="req") -> set:
    out = set()
    for p in params:
        if isinstance(p, Sym):
            if str(p).startswith("&"):
                mode = str(p)
            else:
                out.add(str(p))
        elif isinstance(p, list) and p:
            if mode in ("&optional", "&key", "&aux"):
                if isinstance(p[0], Sym):
                    out.add(str(p[0]))
            else:
                out |= _flatten_names(p)
    return out


def _call_forms(forms, name):
    """Every list form headed NAME anywhere under FORMS (lambdas included)."""
    out = []
    stack = list(forms)
    while stack:
        f = stack.pop()
        if isinstance(f, list):
            if head(f) == name:
                out.append(f)
            stack.extend(f)
    return out


def verify_binding_only_specials(model) -> dict:
    """contracts `binding_only_specials': {SPECIAL: why}.

    A special that is only ever dynamically rebound, never assigned, names no
    shared mutable cell: outside a rebinding it holds its global value, which
    nothing writes (the defvar's constant NIL), and inside one it holds the
    object the rebinding thread made for itself.  R1b therefore has no
    cross-actor state to report on it.  The row is accepted only when the
    source shows each part of that:
      (1) the defvar's initial value is NIL (or absent) -- the global value;
      (2) no form in any host function assigns the symbol itself (setq, setf,
          psetq, psetf, push, pushnew, pop, incf, decf, set, symbol-value,
          progv, makunbound), so the global value stays that NIL;
      (3) every let/let* that rebinds it gives it a value made by that form's
          thread: a lexical variable or a (list ...) / (cons ...) call, never
          another global (which could alias a shared object).
    The one premise it cannot check is that the rebound object is not handed
    to another thread; a handoff would be a thread spawn or a queue push that
    R4 and R8 see by their own rules.
    """
    tree, rows = model.tree, model.c.raw.get("binding_only_specials", {})
    ok = {}
    for name, why in rows.items():
        where = f"binding_only_specials {name}"
        if not why or not isinstance(why, str):
            raise ValueError(f"{where}: no why")
        if name not in tree.globals:
            continue    # a row for a special this tree does not define exempts nothing
        init = tree.global_inits.get(name)
        if init is not None and not (isinstance(init, Sym) and str(init).lower() == "nil"):
            raise ValueError(f"{where}: its defvar initial value is not NIL")
        for d in tree.defs.values():
            forms = d.body
            for h in ("setq", "setf", "psetq", "psetf"):
                for f in _call_forms(forms, h):
                    if any(isinstance(f[k], Sym) and str(f[k]) == name for k in range(1, len(f) - 1, 2)):
                        raise ValueError(f"{where}: {d.name} assigns it ({d.path}:{d.line})")
            for h, k in (("push", 2), ("pushnew", 2), ("pop", 1), ("incf", 1), ("decf", 1),
                         ("makunbound", 1)):
                for f in _call_forms(forms, h):
                    if len(f) > k and isinstance(f[k], Sym) and str(f[k]) == name:
                        raise ValueError(f"{where}: {d.name} assigns it with {h} ({d.path}:{d.line})")
            for h in ("set", "symbol-value", "progv"):
                for f in _call_forms(forms, h):
                    if any(name.lower() in str(x).lower() for x in f[1:2]):
                        raise ValueError(f"{where}: {d.name} reaches it through {h} ({d.path}:{d.line})")
            for h in ("let", "let*"):
                for f in _call_forms(forms, h):
                    for b in (f[1] if len(f) > 1 and isinstance(f[1], list) else []):
                        if not (isinstance(b, list) and len(b) >= 1 and isinstance(b[0], Sym) and str(b[0]) == name):
                            continue
                        val = b[1] if len(b) > 1 else None
                        fresh = (isinstance(val, Sym) and str(val) not in tree.globals
                                 and str(val).lower() != "nil") or (
                                 isinstance(val, list) and head(val) in ("list", "cons"))
                        if not fresh:
                            raise ValueError(f"{where}: {d.name} rebinds it to a value that is not a "
                                             f"lexical variable or a fresh list ({d.path}:{d.line})")
        ok[name] = why
    return ok


def _ancestors(model, name) -> set:
    seen, todo = {name}, [name]
    while todo:
        for caller, _ in model.callers.get(todo.pop(), []):
            if caller not in seen:
                seen.add(caller)
                todo.append(caller)
    return seen


def _top_forms(tree: Tree):
    for rel in sorted(tree.files):
        text = (tree.root / rel).read_text(encoding="utf-8", errors="replace")
        try:
            for form, _ in read_forms(text):
                yield rel, form
        except ledger.ReadError:
            continue


def verify_private_owner_commands(model) -> dict:
    """contracts `private_owner_commands': {RUNNER: row}.  RUNNER is a host
    function that makes an owner for one command, runs the command's THUNK
    inside the owner's section and closes it.  Everything the row claims is
    checked here, and a failing check is a ValueError (a row is never
    silently inert once its runner exists):

      1. the owner is a `let' variable of RUNNER, assigned only from the
         declared constructor, and RUNNER's callers are exactly `commands';
      2. an owner flow scan (OwnerFlow) of the constructor, of RUNNER and of
         each command's thunk, followed through every host function and macro
         the owner is handed to: the owner is never stored into a global, a
         struct slot or any place, never collected into a rest list, never
         passed to a thread or actor start (or a closure over it), never
         passed to a function the host does not define, never made a second
         owner beside (a section or install entered on another value);
      3. the commands are reached only from the declared one-shot dispatch
         functions, each registered only through the registrars, whose tables
         are read only by declared readers that no thread, serving or async
         root reaches.

    Returns {lock: {"functions": set, "rows": [...]}} for rule_R2, which
    exempts the lock's findings in those functions as private-owner I/O."""
    tree, infos, raw = model.tree, model.infos, model.c.raw
    rows = raw.get("private_owner_commands", {})
    exempt: dict = {}
    for runner in sorted(rows):
        row = dict(rows[runner], runner=runner)
        where = f"private_owner_commands {runner}"
        if runner not in infos:
            if not (tree.root / row.get("file", "")).is_file() or not row.get("file"):
                continue                    # a fixture host without the runner's file
            raise ValueError(f"{where}: not a function of the analyzed host")
        for key in ("file", "lock", "owner", "thunk", "constructor", "commands", "dispatch", "registrars",
                    "table_readers", "exempt_leaves", "exempt_leaf_functions", "why"):
            if not row.get(key):
                raise ValueError(f"{where}: no {key} (exempt_leaves is required: a row without it would "
                                 "exempt every leaf)")
        if "exempt_sites" not in row:
            raise ValueError(f"{where}: no exempt_sites (the ratcheted count of exempted R2 site/leaf pairs)")
        leaves = row["exempt_leaves"]
        known = {n for names in model.c.leaves.values() for n in names}
        if not isinstance(leaves, list) or not all(isinstance(n, str) and n in known for n in leaves):
            raise ValueError(f"{where}: exempt_leaves must be a list of leaf names the leaf table knows")
        if not isinstance(row["exempt_sites"], int) or isinstance(row["exempt_sites"], bool) \
                or row["exempt_sites"] < 0:
            raise ValueError(f"{where}: exempt_sites must be a non-negative integer")
        if row["lock"] not in model.c.locks:
            raise ValueError(f"{where}: lock {row['lock']} is not a declared lock")
        for name in [row["constructor"]] + list(row["commands"]) + list(row["dispatch"]):
            if name not in tree.defs:
                raise ValueError(f"{where}: {name} is not a host function")
        d = tree.defs[runner]
        owner, thunk = row["owner"], row["thunk"]
        # 1. the owner is a lexical variable of the runner, made only by the constructor
        if owner in lambda_params(d.params) or thunk not in lambda_params(d.params):
            raise ValueError(f"{where}: {owner} must be a local (not a parameter) and {thunk} a parameter")
        bound = [b for f in _call_forms(d.body, "let") + _call_forms(d.body, "let*")
                 for b in (f[1] if len(f) > 1 and isinstance(f[1], list) else [])
                 if (isinstance(b, list) and b and str(b[0]) == owner) or (isinstance(b, Sym) and str(b) == owner)]
        if len(bound) != 1:
            raise ValueError(f"{where}: {owner} is not bound by exactly one let in {runner}")
        assigns = [f for h in ("setq", "setf", "psetq", "psetf") for f in _call_forms(d.body, h)]
        sets = [(f[k], f[k + 1]) for f in assigns for k in range(1, len(f) - 1, 2)
                if isinstance(f[k], Sym) and str(f[k]) == owner]
        if not sets or any(head(v) != row["constructor"] for _, v in sets):
            raise ValueError(f"{where}: {owner} is assigned from something other than {row['constructor']}")
        callers = {c for c, _ in model.callers.get(runner, [])}
        if callers != set(row["commands"]):
            raise ValueError(f"{where}: RUNNER's callers {sorted(callers)} differ from the declared "
                             f"commands {sorted(row['commands'])}")
        # 2. the flow scans
        flow = OwnerFlow(tree, row)
        flow.scan_def(row["constructor"], ())
        flow.scan_def(runner, ())
        positions = flow.thunk_calls.get(runner)
        if not positions:
            flow.problems.append(f"{runner} never calls {thunk} with the owner")
        pidx = lambda_params(d.params).index(thunk) if thunk in lambda_params(d.params) else 0
        for cmd in row["commands"]:
            cd = tree.defs[cmd]
            sites = _call_forms(cd.body, runner)
            if not sites:
                flow.problems.append(f"{cmd} does not call {runner}")
            for site in sites:
                arg = site[1 + pidx] if len(site) > 1 + pidx else None
                if isinstance(arg, list) and head(arg) == "lambda":
                    lparams = lambda_params(arg[1] if len(arg) > 1 else [])
                    st = {"tainted": {lparams[p] for p in (positions or ()) if p < len(lparams)},
                          "locals": set(lparams) | _flatten_names(cd.params), "dying": False, "ret": [],
                          "runner": cmd, "trail": (cmd,), "path": cd.path, "localfns": {}}
                    flow.scan_body(arg[2:], st)
                elif isinstance(arg, list) and head(arg) == "function" and len(arg) > 1 and str(arg[1]) in tree.defs:
                    td = tree.defs[str(arg[1])]
                    tparams = lambda_params(td.params)
                    flow.scan_def(str(arg[1]), {tparams[p] for p in (positions or ()) if p < len(tparams)},
                                  (cmd,))
                else:
                    flow.problems.append(f"{cmd}: the thunk handed to {runner} is not a lambda or #'host-function "
                                         f"({render(arg, 50)})")
            outside = [f for h in flow.gates | {row["constructor"]} for f in _call_forms(cd.body, h)]
            inside = {id(f) for site in sites for g in (flow.gates | {row["constructor"]})
                      for f in _call_forms(site, g)}
            for f in outside:
                if id(f) not in inside:
                    flow.problems.append(f"{cmd}: {head(f)} is entered outside the thunk handed to {runner}")
        if flow.problems:
            raise ValueError(f"{where}: the owner is not private to the command:\n  "
                             + "\n  ".join(dict.fromkeys(flow.problems)))
        # 3. reachability: one-shot dispatch only
        dispatch = set(row["dispatch"])
        registrars = set(row["registrars"])
        closure = set()
        for cmd in row["commands"]:
            closure |= _ancestors(model, cmd)
        for n in sorted(closure):
            if n in model.roots and n not in dispatch:
                raise ValueError(f"{where}: reached from the root {n} ({model.roots[n]}), which is not a "
                                 "declared one-shot dispatch")
        for dsp in sorted(dispatch):
            if model.roots.get(dsp) != "entry":
                raise ValueError(f"{where}: dispatch {dsp} is called or referenced by the host "
                                 f"(root kind {model.roots.get(dsp)!r}), so it is not a registered one-shot entry")
        names = set(row["commands"]) | dispatch | {runner}
        allowed_defs = closure | set(row["commands"])
        for name, dd in list(tree.defs.items()) + list(tree.macros.items()):
            for target in names:
                if name != target and name not in allowed_defs and _mentions(dd.body, {target}):
                    raise ValueError(f"{where}: {name} mentions {target} but is not on its call path")
        registered = set()
        for rel, form in _top_forms(tree):
            h = head(form)
            if h in ("defun", "defmacro"):
                continue
            for target in dispatch:
                if _mentions(form, {target}):
                    if h in registrars:
                        registered.add(target)
                    else:
                        raise ValueError(f"{where}: {rel}: a top-level {h} form mentions the dispatch {target}")
        if registered != dispatch:
            raise ValueError(f"{where}: dispatch {sorted(dispatch - registered)} is not registered through "
                             f"{sorted(registrars)}")
        for table, readers in row["table_readers"].items():
            found = {name for name, dd in tree.defs.items() if _mentions(dd.body, {table})} - set(
                row.get("table_writers", []))
            if found != set(readers):
                raise ValueError(f"{where}: table {table} is read by {sorted(found)}, not the declared "
                                 f"{sorted(readers)}")
            for reader in readers:
                for n in _ancestors(model, reader):
                    if model.roots.get(n) in ("thread", "serving", "async"):
                        raise ValueError(f"{where}: table reader {reader} is reached from the "
                                         f"{model.roots[n]} root {n}")
        slot = exempt.setdefault(row["lock"], {"functions": set(), "rows": [], "scopes": []})
        slot["functions"] |= {runner} | set(row["commands"])
        slot["rows"].append(runner)
        slot["scopes"].append((frozenset({runner} | set(row["commands"])), frozenset(row["exempt_leaves"]),
                               runner, frozenset(row["exempt_leaf_functions"])))
    return exempt


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
        self.declare_callback_contexts()
        self.roots = self.find_roots()
        self.check_callback_entries()
        self.check_test_only_entries()
        self.private_owner = verify_private_owner_commands(self)
        self.binding_only = verify_binding_only_specials(self)
        self.entry_requirements = 0
        self.compute_blocking()
        self.compute_acquires()
        self.compute_signals()
        self.compute_requirements()
        self.compute_actors()
        self.compute_mustheld()
        self.compute_mustbound()

    def declare_callback_contexts(self) -> None:
        """contracts `callback_contexts': {LAMBDA-ID: {"runs_in": ENTRY, "why"}}.

        A stored callback (a lambda kept in a struct slot, a special binding or
        a callee's state, and called later) is an async root because the walk
        cannot name its caller.  The declaration names it: the callback runs
        only on ENTRY's thread, inside ENTRY's dynamic extent, holding no lock
        (a command's single serialized loop, specs/bp-node-machine.md 9.1).
        It becomes a lock-free call edge ENTRY -> LAMBDA, so its requirements
        are ENTRY's, as if ENTRY called it.  Checked here, refused otherwise:
        the lambda exists at that lexical identity (an edit that renumbers it
        re-declares it), ENTRY is reached only from startup or entry roots
        (check_callback_entries), and the lambda's
        lexical owner is reached from ENTRY by host calls (the callback is
        created inside ENTRY's call tree).  It closes the analysis gap only:
        that ENTRY never hands the callback to another thread is the declared
        contract, not something this check proves."""
        self.declared_callbacks: dict[str, str] = {}
        analyzed = {info.path for info in self.infos.values()}
        for lam, row in self.c.raw.get("callback_contexts", {}).items():
            entry = row.get("runs_in")
            if not row.get("why"):
                raise ValueError(f"callback_contexts {lam}: no why")
            if lam.removeprefix("lambda@").split(":", 1)[0] not in analyzed:
                continue  # a run over other files (a fixture) does not see it
            if lam not in self.infos:
                raise ValueError(f"callback_contexts names {lam}, which the host does not have "
                                 "(renumbered or removed: re-declare it from the current findings)")
            if entry not in self.infos or entry.startswith("lambda@"):
                raise ValueError(f"callback_contexts {lam}: runs_in {entry} is not a named host function")
            owner = lam.split(":", 1)[1].split("#", 1)[0]
            seen, todo = {entry}, [entry]
            while todo:
                for e in self.infos[todo.pop()].events:
                    if e.kind in ("call", "async") and e.name in self.infos and e.name not in seen:
                        seen.add(e.name)
                        todo.append(e.name)
            if owner not in seen:
                raise ValueError(f"callback_contexts {lam}: its owner {owner} is not reached from {entry}")
            edge = Event("call", lam, self.infos[lam].line, Ctx(), "declared-callback")
            self.infos[entry].events.append(edge)
            self.callers[lam].append((entry, edge))
            self.declared_callbacks[lam] = entry

    def check_test_only_entries(self) -> None:
        """A declared test-only entry is an uncalled host function that a test
        under tests/ calls: it is not an actor of the running host.  The row
        goes inert (the function is then an ordinary callee) the moment a host
        function calls or references it."""
        self.test_only = set()
        rows = self.c.raw.get("test_only_entries", {})
        texts = None
        for name in sorted(rows):
            if name not in self.infos:
                if not (self.tree.root / rows[name]["file"]).exists():
                    continue     # a fixture host without the file the row is about
                raise ValueError(f"test_only_entries {name}: not a function of the analyzed host")
            if self.roots.get(name) != "entry":
                raise ValueError(f"test_only_entries {name}: is called or referenced by the host "
                                 f"(root kind {self.roots.get(name)!r}); the row is stale")
            if texts is None:
                texts = [p.read_text(encoding="utf-8", errors="replace")
                         for p in sorted((self.tree.root / "tests").rglob("*.lisp"))]
            if not any(re.search(r"[(\s']" + re.escape(name) + r"[\s)]", t) for t in texts):
                raise ValueError(f"test_only_entries {name}: no file under tests/ mentions it")
            self.test_only.add(name)

    def check_callback_entries(self) -> None:
        """A declared callback's ENTRY is reached only from startup or entry
        roots (a command's own thread), never from a thread, serving or async
        root, where "inside ENTRY's extent" would not be one thread."""
        for lam, entry in self.declared_callbacks.items():
            seen, todo = {entry}, [entry]
            while todo:
                name = todo.pop()
                kind = self.roots.get(name)
                if kind in ("thread", "serving", "async"):
                    raise ValueError(f"callback_contexts {lam}: runs_in {entry} is reached from "
                                     f"the {kind} root {name}")
                for caller, _ in self.callers.get(name, []):
                    if caller not in seen:
                        seen.add(caller)
                        todo.append(caller)

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
            elif name.startswith("lambda@") and name not in self.declared_callbacks:
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
        waiters = self.c.raw.get("condition_wait_wrappers", {})
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
                    if key[0] in waiters and leaf.startswith(key[0] + ":") \
                            and leaf.endswith(":sb-thread:condition-wait"):
                        continue   # a wrapper's own wait: its call site carries the wait leaf, mutex released
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
        post: dict[str, set] = collections.defaultdict(set)
        guards = self.dead_guard_rows()
        for r, kind in self.roots.items():
            if kind not in ("thread", "serving", "async", "entry", "startup"):
                continue
            if kind == "entry" and r in self.test_only:
                continue
            stack = [(r, None)]
            seen = {(r, None)}
            while stack:
                n, tag = stack.pop()
                (actors[n].add(r) if tag is None else post[n].add((r, tag)))
                for e in self.infos[n].events:
                    if e.kind == "call" and e.name in self.infos:
                        nxt = (e.name, tag or guards.get((n, e.name, id(e))))
                        if nxt not in seen:
                            seen.add(nxt)
                            stack.append(nxt)
        self.actors = actors
        self.post_actors = post

    def dead_guard_rows(self) -> dict:
        """{(function, callee, id(call event)): the root of the thread that is
        not running} for the guarded calls a contract row declares: the call
        sits in an `unless (and T (thread-alive-p T))' body, T is looked up
        from the very object the call's first argument names, and the
        function starts exactly one thread of the declared name."""
        out = {}
        for row in self.c.raw.get("dead_thread_guards", []):
            info = self.infos.get(row["function"])
            if info is None:
                continue
            roots = [e.name for e in info.events if e.kind == "thread" and e.extra == row["thread_name"]]
            if len(roots) != 1:
                continue
            for e in info.events:
                if (e.kind == "call" and e.name == row["call"] and e.arg0
                        and any(e.arg0 in ties for ties in e.dead)):
                    out[(row["function"], e.name, id(e))] = roots[0]
        return out

    def collapse_dead(self, labels):
        """Drop the actor labels `X|after|R' when R is the only other actor:
        the stop that runs after the thread R is no longer running is ordered
        after everything R did."""
        out = set(labels)
        for lab in list(out):
            if "|after|" in lab:
                tag = lab.split("|after|", 1)[1]
                if tag in out and all(l == tag or l.endswith("|after|" + tag) for l in out):
                    out = {tag}
        return out

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

    def compute_mustbound(self) -> None:
        """mustbound[f]: the specials every call of F reaches it under a `let'
        rebinding of (its callers' own, or their callers').  A root starts with
        none: a thread sees the global value, not its spawner's binding."""
        top = None
        bound: dict[str, frozenset | None] = {n: top for n in self.infos}
        for n in self.roots:
            bound[n] = frozenset()
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
                    b = bound.get(caller)
                    if b is None:
                        continue
                    here = b | e.bound
                    acc = here if acc is None else acc & here
                if acc is not None and acc != bound[name]:
                    bound[name] = acc
                    changed = True
        self.mustbound = {n: (b if b is not None else frozenset()) for n, b in bound.items()}


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
        self.private_io_rows: dict = {}  # runner -> exempted pairs, held to the row's exempt_sites
        self.private_io: dict = {}      # lock -> R2 (site, leaf) pairs exempted as private-owner I/O
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
                if e.name in e.bound or e.name in self.m.mustbound.get(name, frozenset()):
                    continue        # the access names a thread-local dynamic binding
                if e.name in self.m.binding_only:
                    continue        # verified: only rebound, never assigned (verify_binding_only_specials)
                held = e.ctx.locks | self.m.mustheld.get(name, frozenset())
                if e.atomic:
                    held = held | {"SYNC:" + e.name}    # the table's own lock covers this one operation
                actors = {self.m.actor_of(r) for r in self.m.actors.get(name, ())}
                actors |= {self.m.actor_of(r) + "|after|" + tag for r, tag in self.m.post_actors.get(name, ())}
                if not actors or actors == {"startup"} or "STARTUP" in held:
                    continue
                sites[e.name].append((info, e, held, actors - {"startup"}))
        for var, rows in sorted(sites.items()):
            writes = [r for r in rows if r[1].extra == "w"]
            if not writes:
                continue
            actors = self.m.collapse_dead(set().union(*(r[3] for r in rows)))
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
        waiters = self.c.raw.get("condition_wait_wrappers", {})
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
                        if e.name in waiters and leaf.startswith(e.name + ":") \
                                and leaf.endswith(":sb-thread:condition-wait"):
                            continue   # the wrapper's own wait: the call-site wait leaf stands for it
                        cands.append((leaf, kind, held, (e.name, noio)))
                elif e.kind == "core":
                    for r in sorted(self.an.reach.get(e.name, {})):
                        if r in self.infos and r not in overrides:
                            for leaf, (kind, _, _) in self.m.blk.get((r, noio), {}).items():
                                cands.append((leaf, kind, held, ("core", e.name, r, noio)))
                for leaf, kind, locks, how in cands:
                    for lock in sorted(locks):
                        if leaf.split(":", 2)[2] in self.c.locks.get(lock, {}).get("io_leaves_ok", []):
                            continue   # this lock's declared non-blocking leaves
                        hit = next((r for fns, leaves, r, lfns in self.m.private_owner.get(lock, {}).get("scopes", ())
                                    if name in fns and leaf.split(":", 2)[2] in leaves
                                    and leaf.split(":", 2)[0] in lfns), None)
                        if hit is not None:
                            # a command whose owner the checker proved private (verify_private_owner_commands)
                            self.private_io[lock] = self.private_io.get(lock, 0) + 1
                            self.private_io_rows[hit] = self.private_io_rows.get(hit, 0) + 1
                            continue
                        k = (lock, leaf)
                        row = found.get(k)
                        if row is None:
                            found[k] = [kind, info, e, how, 1]
                        else:
                            row[4] += 1
        for runner, row in sorted(self.c.raw.get("private_owner_commands", {}).items()):
            if runner not in self.infos or runner not in {r for v in self.m.private_owner.values()
                                                          for r in v["rows"]}:
                continue
            have, want = self.private_io_rows.get(runner, 0), row["exempt_sites"]
            if have != want:
                advice = ("lower exempt_sites: a site or leaf no longer needs the exemption" if have < want
                          else "a new site or leaf is exempted: review it, then raise exempt_sites")
                self.add("R2", self.infos[runner], self.infos[runner].line,
                         f"private-owner exemption pinned at {want} site/leaf pair(s), found {have}; {advice}",
                         f"private-owner-sites:{runner}")
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
        if kind == "owned-fd":
            return self.owned_fd_problem(info, sink, row)
        return f"unknown borrow kind {kind}"

    def owned_fd_problem(self, info, sink, row) -> str | None:
        """owned-fd: the descriptor the sink reads is not an extent-registry descriptor.
        It is a slot only a private worker thread touches, assigned once from an
        fnn-open in OPEN_IN and retired by an fnn-close in CLOSE_IN.  Checked over
        the source: (1) every SINK call in this function passes (SLOT x);
        (2) SLOT is referenced in no function but this one, OPEN_IN and CLOSE_IN;
        (3) every setf of SLOT stores nil or a variable bound to an OPEN_CALL;
        (4) CONSTRUCTOR never passes the slot's keyword; (5) CLOSE_IN closes a
        variable bound from SLOT; (6) the sink's function is called only from
        CLOSE_IN and CLOSE_IN only from the declared THREAD_ROOTS."""
        slot, oi, ci = row["slot"], row["open_in"], row["close_in"]
        defs = self.an.tree.defs
        if oi not in defs or ci not in defs:
            return f"{oi} or {ci} is missing"

        def walk(x):
            st = [x]
            while st:
                y = st.pop()
                if isinstance(y, list):
                    yield y
                    st.extend(y)

        def binds(fname, var, test):
            for f in walk(defs[fname].body):
                if head(f) in ("let", "let*") and len(f) > 1 and isinstance(f[1], list):
                    for b in f[1]:
                        if isinstance(b, list) and len(b) >= 2 and str(b[0]) == var and test(b[1]):
                            return True
            return False

        calls = [f for f in walk(defs[info.name].body) if head(f) == sink.name]
        if not calls:
            return f"{info.name} no longer calls {sink.name}"
        for f in calls:
            if len(f) < 2 or head(f[1]) != slot:
                return f"{sink.name} at line {line_of(f, 0)} is not passed the {slot} slot"
        for fname, d in defs.items():
            uses = [f for f in walk(d.body) if head(f) == slot]
            if uses and fname not in (info.name, oi, ci):
                return f"{slot} is referenced in {fname}"
        stores = []
        for fname in (info.name, oi, ci):
            for f in walk(defs[fname].body):
                if head(f) in ("setf", "setq"):
                    for place, value in zip(f[1::2], f[2::2]):
                        if head(place) == slot:
                            stores.append((fname, value))
        opened = False
        for fname, value in stores:
            if isinstance(value, Sym) and str(value).lower() == "nil":
                continue
            if fname != oi or not isinstance(value, Sym) or not binds(
                    fname, str(value), lambda init: head(init) == row["open_call"]):
                return f"{slot} is stored from something other than a {row['open_call']} in {oi} ({fname})"
            opened = True
        if not opened:
            return f"{oi} no longer stores a {row['open_call']} result in {slot}"
        for d in defs.values():
            for f in walk(d.body):
                if head(f) == row["constructor"] and any(
                        isinstance(a, Sym) and str(a).lower() == row["slot_keyword"] for a in f):
                    return f"{row['constructor']} initialises {slot}"
        closed = False
        for f in walk(defs[ci].body):
            if head(f) == row["close_call"] and len(f) > 1 and isinstance(f[1], Sym) and binds(
                    ci, str(f[1]), lambda init: head(init) == slot):
                closed = True
        if not closed:
            return f"{ci} does not {row['close_call']} a variable bound from {slot}"
        callers_of = lambda n: {c for c, _ in self.m.callers.get(n, ())}
        if callers_of(info.name) != {ci}:
            return f"{info.name} is called from {sorted(callers_of(info.name))}, not only {ci}"
        if not callers_of(ci) or not callers_of(ci) <= set(row["thread_roots"]):
            return f"{ci} is called from {sorted(callers_of(ci))}; the declared thread roots are {row['thread_roots']}"
        return None

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
        actor_threads = {decl[3]: actor for actor, decl in self.an.tree.actors.items()}
        self.check_actor_declarations()
        for name, info in self.infos.items():
            for e in info.events:
                if e.kind != "thread":
                    continue
                if e.extra in actor_threads:
                    continue  # a declared actor: its row is the declaration (check_actor_*)
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

    # The failure policies a def-actor declares (books/failure-scope.lisp
    # *fn-fs-actor-failures*) and what each asks of a starter call: the
    # actor's escape is decided by the service's boundary (:service,
    # fnn-owner-thread-escape), by a private job's (:job, the same with its
    # JOBP argument t), or the body hands its outcome to its joiner (:result:
    # no escape, the thunk handles serious-condition itself).
    ACTOR_ESCAPE = "fnn-owner-thread-escape"
    ACTOR_JOIN = "fnn-owner-actor-join"

    def escape_calls(self, form, depth=1) -> list:
        """The (fnn-owner-thread-escape ...) forms in FORM, following named
        calls DEPTH levels into their definitions."""
        found, stack, seen = [], [form], set()
        while stack:
            x = stack.pop()
            if not isinstance(x, list):
                continue
            h = head(x)
            if h == self.ACTOR_ESCAPE:
                found.append(x)
            elif depth and h in self.an.tree.defs and h not in seen:
                seen.add(h)
                found.extend(self.escape_calls(self.an.tree.defs[h].body, depth - 1))
            stack.extend(x)
        return found

    @staticmethod
    def jobp(call) -> bool:
        return len(call) > 4 and not (isinstance(call[4], Sym) and str(call[4]) == "nil")

    @staticmethod
    def handles_serious(form) -> bool:
        stack = [form]
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                if head(x) == "handler-case" and any(
                        isinstance(c, list) and c and sym(c[0]) in ("serious-condition", "condition", "t")
                        for c in x[2:]):
                    return True
                stack.extend(x)
        return False

    def check_actor_declarations(self):
        for actor, (path, line, kind, tname, roster, join, failure) in sorted(self.an.tree.actors.items()):
            jinfo = self.infos.get(join)
            if jinfo is None or not any(x.kind == "call" and x.name == self.ACTOR_JOIN for x in jinfo.events):
                self.add("R4", self.infos.get(actor) or FnInfo(actor, path, line, True), line,
                         f"def-actor {actor}: declared join site {join} does not call {self.ACTOR_JOIN}",
                         "actor-no-join:" + actor)
        for name, info in self.infos.items():
            for actor, line, args in info.actor_starts:
                failure = self.an.tree.actors[actor][6]
                thunk = args[2] if len(args) > 2 else None
                escape = args[3] if len(args) > 3 else None
                no_escape = escape is None or (isinstance(escape, Sym) and str(escape) == "nil")
                if failure == ":result":
                    ok = no_escape and thunk is not None and self.handles_serious(thunk)
                    why = "a :result actor has no escape and its thunk handles serious-condition"
                elif failure in (":service", ":job"):
                    calls = self.escape_calls(escape if not no_escape else thunk)
                    ok = bool(calls) and all(self.jobp(c) == (failure == ":job") for c in calls)
                    why = (f"a {failure} actor's escape (or, with none, its thunk) reaches "
                           f"{self.ACTOR_ESCAPE}" + (" with JOBP t" if failure == ":job" else " without JOBP"))
                else:
                    ok, why = False, f"failure policy {failure} is not :service, :job or :result"
                if not ok:
                    self.add("R4", info, line, f"starts def-actor {actor} against its declared failure "
                             f"policy {failure}: {why}", "actor-failure:" + actor)

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
    def _always_signals(self) -> dict:
        """defun name -> the condition classes it signals on EVERY path: its
        final body form is (error 'CLASS ...) or a call to such a defun
        (fnn-fault, fnn-indeterminate, ...), through progn/let/let*/an if
        whose two arms both do."""
        if hasattr(self, "_always"):
            return self._always
        defs = self.an.tree.defs
        result: dict = {}

        def classes(form):
            if not isinstance(form, list) or not form:
                return None
            h = head(form)
            if h in ("error", "signal") and len(form) > 1:
                q = quoted_symbol(form[1])
                return frozenset([q]) if q and h == "error" else None
            if h in ("progn",) and len(form) > 1:
                return classes(form[-1])
            if h in ("let", "let*") and len(form) > 2:
                return classes(form[-1])
            if h == "if" and len(form) == 4:
                a, b = classes(form[2]), classes(form[3])
                return a | b if a is not None and b is not None else None
            if h in result:
                return result[h]
            return None

        changed = True
        while changed:
            changed = False
            for name, d in defs.items():
                if name in result or not d.body:
                    continue
                c = classes(d.body[-1])
                if c is not None:
                    result[name] = c
                    changed = True
        self._always = result
        self._always_classes = classes
        return result

    def _converts(self, forms) -> bool:
        """The clause body ends in a call that signals a fault or an
        indeterminate condition on every path: the condition is converted
        to one the fence takes, not consumed."""
        self._always_signals()
        stack = list(forms)
        while stack:        # an early exit before the signal consumes the condition on that path
            f = stack.pop()
            if isinstance(f, list) and f:
                if head(f) in ("quote", "lambda", "function"):
                    continue
                if head(f) in Analyzer.EXIT_HEADS:
                    return False
                stack.extend(f)
        c = self._always_classes(Node([Sym("progn")] + list(forms))) if forms else None
        if not c:
            return False
        core = (CLASS_TYPE["fault"], CLASS_TYPE["indet"])
        return all(any(self.m.subtype(x, t) for t in core) for x in c)

    def verified_status_rethrows(self) -> dict:
        """{function: handler clause type} for the declared value-routed
        deferred rethrows (contract status_rethrows) that hold up against the
        source.  FUNCTION's HANDLER clause hands the condition on as a returned
        status: its last form is (values STATUS ...) and it never exits early.
        Every reference to FUNCTION in the host is a call that is the value
        form of a (multiple-value-bind (S ...) (FUNCTION ...) BODY...), and BODY
        reaches, past forms that cannot leave BODY early (no return-from,
        return, go or throw, even nested), a form (when (eq S STATUS) CALL)
        whose CALL signals a fault or indeterminate condition on every path.
        A row that does not verify is a loud error."""
        out = {}
        tree = self.an.tree
        for name, row in sorted(self.c.raw.get("status_rethrows", {}).items()):
            if name not in self.infos:
                if not (tree.root / row["file"]).exists():
                    continue
                raise ValueError(f"status_rethrows {name}: not a function of the analyzed host")
            status, clause_type = row["status"], row["clause"]

            def fail(why, name=name):
                raise ValueError(f"status_rethrows {name}: {why}")

            exits = Analyzer.EXIT_HEADS

            def has_exit(f):
                stack = [f]
                while stack:
                    x = stack.pop()
                    if isinstance(x, list) and x:
                        if head(x) in ("quote", "lambda", "function"):
                            continue
                        if head(x) in exits:
                            return True
                        stack.extend(x)
                return False

            # the clause hands the condition on as the returned status
            clauses = []
            stack = list(tree.defs[name].body)
            while stack:
                x = stack.pop()
                if isinstance(x, list) and x:
                    if head(x) == "handler-case":
                        clauses += [cl for cl in x[2:] if isinstance(cl, list) and cl and sym(cl[0]) == clause_type]
                    stack.extend(x)
            if not clauses:
                fail(f"no handler-case clause {clause_type}")
            for cl in clauses:
                body = cl[2:]
                last = body[-1] if body else None
                if not (isinstance(last, list) and head(last) == "values" and len(last) > 1
                        and sym(last[1]) == status):
                    fail(f"the clause {clause_type} does not end in (values {status} ...)")
                if any(has_exit(f) for f in body):
                    fail(f"the clause {clause_type} can exit early")

            def converts(forms, var):
                for f in forms:
                    if (isinstance(f, list) and head(f) == "when" and len(f) == 3
                            and isinstance(f[1], list) and head(f[1]) == "eq" and len(f[1]) == 3
                            and sym(f[1][1]) == var and sym(f[1][2]) == status
                            and isinstance(f[2], list) and self._converts([f[2]])):
                        return True
                    if has_exit(f):
                        return False
                    if isinstance(f, list) and head(f) in ("let", "let*") and len(f) > 2:
                        if any(has_exit(b) for b in (f[1] if isinstance(f[1], list) else [])):
                            return False
                        if converts(f[2:], var):
                            return True
                        return False
                return False

            seen = 0
            for dname, d in tree.defs.items():
                stack = [(f, None) for f in d.body]
                while stack:
                    x, parent = stack.pop()
                    if isinstance(x, Sym) and str(x) == name and not (
                            parent is not None and parent and parent[0] is x):
                        if not (isinstance(parent, list) and parent and head(parent) == "multiple-value-bind"):
                            if dname != name:
                                fail(f"{dname} references {name} outside a multiple-value-bind value form")
                    if not (isinstance(x, list) and x):
                        continue
                    if head(x) == name:
                        fail(f"{dname} calls {name} outside a multiple-value-bind value form")
                    if head(x) == "multiple-value-bind" and len(x) > 3:
                        call = x[2]
                        if isinstance(call, list) and head(call) == name:
                            seen += 1
                            vars_ = x[1] if isinstance(x[1], list) else []
                            if not vars_ or not isinstance(vars_[0], Sym) or not converts(x[3:], str(vars_[0])):
                                fail(f"{dname}: the status of the call is not converted past early exits")
                            stack.extend((c, x) for c in call[1:])
                            stack.extend((c, x) for c in x[3:])
                            continue
                    stack.extend((c, x) for c in x)
            if seen == 0:
                fail("no caller binds its status")
            out[name] = clause_type
        return out

    @staticmethod
    def _subforms(f):
        stack = [f]
        while stack:
            x = stack.pop()
            yield x
            if isinstance(x, list):
                stack.extend(x)

    def verified_diagnostic_sinks(self) -> set:
        """The declared diagnostic sinks (contract diagnostic_sinks) that hold
        up against the source: a function of the analyzed host whose call
        closure reaches no fence function and no descriptor open or close
        primitive, so a failure inside it cannot alter custody or the node's
        lifecycle.  A row whose function is absent is inert in a fixture host
        without its file, and a loud error otherwise."""
        forbidden = (set(self.c.raw.get("fence_functions", [])) | set(self.c.raw.get("close_primitives", []))
                     | set(self.c.raw.get("open_primitives", [])))
        out = set()
        for name, row in sorted(self.c.raw.get("diagnostic_sinks", {}).items()):
            if name not in self.infos:
                if not (self.an.tree.root / row["file"]).exists():
                    continue
                raise ValueError(f"diagnostic_sinks {name}: not a function of the analyzed host")
            hit = self.reaches(("u", frozenset(), (name,), ()), forbidden - {name})
            if hit:
                raise ValueError(f"diagnostic_sinks {name}: reaches {hit[-1]} ({' -> '.join(hit)}); "
                                 f"a diagnostic sink cannot touch custody or the fence")
            out.add(name)
        return out

    @staticmethod
    def _sig_calls(sig) -> tuple:
        """(every callee name in the SigX, whether any raw leaf signal is in it)."""
        calls, leaves = set(), False
        stack = [sig]
        while stack:
            s = stack.pop()
            if s[0] == "u":
                calls.update(s[2])
                leaves = leaves or bool(s[1])
                stack.extend(s[3])
            else:
                stack.append(s[1])
                stack.extend(b for _, _, b in s[2])
        return calls, leaves

    def diagnostic_only(self, inner, clauses, sinks) -> bool:
        """The protected form calls nothing but verified diagnostic sinks and
        signals nothing of its own, and every clause body is empty (no call, no
        rethrow): the swallowed condition is the sink's own failure."""
        calls, leaves = self._sig_calls(inner)
        return (bool(calls) and not leaves and calls <= sinks
                and all(body == EMPTY_SIG for _, _, body, _, _, _ in clauses))

    def rule_R7(self):
        fences = set(self.c.raw.get("fence_functions", []))
        sinks = self.verified_diagnostic_sinks()
        status_routed = self.verified_status_rethrows()
        debt_routed = self.verified_debt_rethrows()
        # classify-and-route functions (contract classifying_escape_functions):
        # a fault or indeterminate condition handed to one reaches the fence
        # or fault stop; any other kind is answered to the caller. They count
        # as routing for fault/indet only, never as a fence for connection-local kinds.
        classifiers = set(self.c.raw.get("classifying_escape_functions", {}))
        scopes = self.c.raw.get("failure_scopes", {})
        for name, info in self.infos.items():
            actors = {self.m.actor_of(r) for r in self.m.actors.get(name, ())}
            if not (actors - {"startup", "main"}) and self.m.roots.get(name) not in ("thread", "serving", "async"):
                continue  # offline/command code: inventoried, not a served failure scope
            for (line, inner, clauses, ctx) in info.handlers:
                can = set(self.m.eval_sig(inner, self.m.signals))
                if sinks and self.diagnostic_only(inner, clauses, sinks):
                    continue
                row = scopes.get(f"{name}:{line}") or scopes.get(name)
                scope = row["scope"] if isinstance(row, dict) else row
                remaining = set(can)
                for types, rethrows, body, names, spec, forms in clauses:
                    caught = {c for c in remaining if any(self.m.subtype(CLASS_TYPE[c], t) for t in types)}
                    remaining -= caught
                    if not caught:
                        continue
                    routes = rethrows or bool(names & fences)
                    if status_routed.get(name) and spec == status_routed[name] and (caught & {"fault", "indet"}) == {"indet"}:
                        continue    # handed on as a returned status the callers convert (verified)
                    drow = debt_routed.get(name)
                    if (drow and spec == drow["clause"] and any(
                            isinstance(y, list) and head(y) == "setq" and len(y) == 3
                            and sym(y[1]) == drow["var"] and isinstance(y[2], Sym)
                            for f in forms for y in self._subforms(f))):
                        continue    # captured into the verified debt slot (contract debt_rethrows)
                    core = caught & {"fault", "indet"}
                    local = caught & {"socket", "refusal", "connection"}
                    if core and not (routes or names & classifiers or self._converts(forms)) \
                            and scope not in ("private", "result", "converts", "fence"):
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
    def verified_debt_rethrows(self) -> dict:
        """{function: row} for the declared cross-function debt rethrows
        (contract debt_rethrows) that hold up against the source.  A handler
        of FUNCTION captures a cleanup condition into the local VAR instead of
        signalling it (a primary escape may be unwinding); the swallow is
        deferred, not lost, when ALL of these hold:
          1. a clause of CLAUSE type in FUNCTION assigns the condition to VAR
             (setq VAR condition), VAR bound by a let to nil;
          2. on that let's body, past forms that cannot leave early, comes
             (when VAR (setf (SLOT R) VAR));
          3. that store is the only write of SLOT in the host (no other
             setf/setq/incf/push/pop of a (SLOT x) place, no :SLOT-keyword);
          4. CLOSER, on its own spine and past no early exit, reaches
             (when (SLOT R) (error (SLOT R))) for the R it got from the registry;
             every other removal from REGISTRY is under an (unless ... (SLOT R)
             ...) guard;
          5. CLOSER is a close hook of the stop path: a binding of SPECIAL
             names #'CLOSER, a constructor stores SPECIAL as its :close-hooks,
             and a stop function funcalls each hook of the service's close-hooks
             inside a handler whose clause clears a flag the same function then
             tests; the constructor and the stop function are both reached from
             inside that binding's body.
        A row that does not verify is a loud error."""
        out = {}
        tree = self.an.tree
        exits = Analyzer.EXIT_HEADS
        mutators = {"setq", "setf", "psetq", "psetf", "incf", "decf", "push", "pushnew", "pop",
                    "rotatef", "shiftf", "remf"}

        def walk(forms):
            stack = [(f, ()) for f in forms]
            while stack:
                x, anc = stack.pop()
                yield x, anc
                if isinstance(x, list):
                    stack.extend((c, anc + ((x, k),)) for k, c in enumerate(x))

        def has_exit(f):
            stack = [f]
            while stack:
                x = stack.pop()
                if isinstance(x, list) and x:
                    if head(x) in ("quote", "lambda", "function"):
                        continue
                    if head(x) in exits:
                        return True
                    stack.extend(x)
            return False

        def spine(forms, goal):
            """GOAL is reached on the spine of FORMS (descending let, let*, when,
            unless bodies, progn) before any form that may leave early."""
            for f in forms:
                if goal(f):
                    return True
                if isinstance(f, list) and head(f) in ("let", "let*") and len(f) > 2:
                    if any(has_exit(b) for b in (f[1] if isinstance(f[1], list) else [])):
                        return False
                    if spine(f[2:], goal):
                        return True
                if isinstance(f, list) and head(f) in ("when", "unless", "progn") and len(f) > 1:
                    if head(f) != "progn" and has_exit(f[1]):
                        return False
                    if spine(f[(1 if head(f) == "progn" else 2):], goal):
                        return True
                if has_exit(f):
                    return False
            return False

        for name, row in sorted(self.c.raw.get("debt_rethrows", {}).items()):
            if name not in self.infos:
                if not (tree.root / row["file"]).exists():
                    continue
                raise ValueError(f"debt_rethrows {name}: not a function of the analyzed host")
            var, slot, closer = row["var"], row["slot"], row["closer"]
            registry, special = row["registry"], row["special"]

            def fail(why, name=name):
                raise ValueError(f"debt_rethrows {name}: {why}")

            # 1 + 2: the capture and the store
            captured = False
            store = None
            for x, anc in walk(tree.defs[name].body):
                if isinstance(x, list) and head(x) == "handler-case":
                    for cl in x[2:]:
                        if isinstance(cl, list) and cl and sym(cl[0]) == row["clause"]:
                            for y, _ in walk(cl[2:]):
                                if (isinstance(y, list) and head(y) == "setq" and len(y) == 3
                                        and sym(y[1]) == var and isinstance(y[2], Sym)):
                                    captured = True
                if isinstance(x, list) and head(x) in ("let", "let*") and len(x) > 2 and isinstance(x[1], list):
                    binds = [b for b in x[1] if isinstance(b, list) and b and sym(b[0]) == var]
                    if binds and (len(binds[0]) == 1 or binds[0][1] is None or sym(binds[0][1]) == "nil"):
                        def is_store(f):
                            return (isinstance(f, list) and head(f) == "when" and len(f) == 3 and sym(f[1]) == var
                                    and isinstance(f[2], list) and head(f[2]) == "setf" and len(f[2]) == 3
                                    and isinstance(f[2][1], list) and head(f[2][1]) == slot
                                    and len(f[2][1]) == 2 and sym(f[2][2]) == var)
                        if spine(x[2:], is_store):
                            store = next(f for f, _ in walk(x[2:]) if is_store(f))
            if not captured:
                fail(f"no {row['clause']} clause assigns the condition to {var}")
            if store is None:
                fail(f"{var} is not stored into {slot} past forms that cannot leave early")
            # 3: the only write of the slot
            for dname, d in tree.defs.items():
                for x, anc in walk(d.body):
                    if isinstance(x, Sym) and str(x).lower() == row["slot_keyword"]:
                        fail(f"{dname} initialises the slot by keyword")
                    if (isinstance(x, list) and len(x) > 1 and head(x) in mutators and x is not store[2]
                            and isinstance(x[1], list) and x[1] and sym(x[1][0]) == slot):
                        fail(f"{dname} writes {slot} other than the one store")
            # 4: the closer
            if closer not in self.infos:
                fail(f"closer {closer} is not a function of the host")
            cd = tree.defs[closer]
            rvars = set()
            for x, _ in walk(cd.body):
                if (isinstance(x, list) and head(x) in ("let", "let*") and len(x) > 2 and isinstance(x[1], list)):
                    for b in x[1]:
                        if isinstance(b, list) and len(b) == 2 and isinstance(b[1], list) \
                                and head(b[1]) == row["registry_reader"]:
                            rvars.add(sym(b[0]))
            if not rvars:
                fail(f"{closer} does not take its runtime from {row['registry_reader']}")

            def is_signal(f):
                if not (isinstance(f, list) and head(f) == "when" and len(f) == 3):
                    return False
                t, a = f[1], f[2]
                if not (isinstance(t, list) and len(t) == 2 and sym(t[0]) == slot and sym(t[1]) in rvars):
                    return False
                return (isinstance(a, list) and head(a) == "error" and len(a) == 2
                        and isinstance(a[1], list) and len(a[1]) == 2 and sym(a[1][0]) == slot
                        and sym(a[1][1]) == sym(t[1]))
            if not spine(cd.body, is_signal):
                fail(f"{closer} does not signal {slot} on its spine before any early exit")
            for dname, d in tree.defs.items():
                if dname == closer:
                    continue
                for x, anc in walk(d.body):
                    if isinstance(x, list) and head(x) == "remhash" and len(x) > 2 and sym(x[2]) == registry:
                        guarded = any(isinstance(f, list) and head(f) == "unless" and len(f) > 2
                                      and any(isinstance(t, list) and len(t) == 2 and sym(t[0]) == slot
                                              for t, _ in walk([f[1]]))
                                      for f, _ in anc)
                        if not guarded:
                            fail(f"{dname} removes a runtime from {registry} without checking {slot}")
            # 5: the closer is a close hook of the stop path
            binders = []
            for dname, d in tree.defs.items():
                for x, anc in walk(d.body):
                    if isinstance(x, list) and head(x) in ("let", "let*") and len(x) > 2 and isinstance(x[1], list):
                        for bi, b in enumerate(x[1]):
                            if (isinstance(b, list) and len(b) == 2 and sym(b[0]) == special
                                    and any(isinstance(y, list) and head(y) == "function" and len(y) == 2
                                            and sym(y[1]) == closer for y, _ in walk([b[1]]))):
                                # the binding is in effect in the body and, for let*, in later inits
                                later = [lb[1] for lb in x[1][bi + 1:]
                                         if head(x) == "let*" and isinstance(lb, list) and len(lb) == 2]
                                binders.append((dname, list(x[2:]) + later))
            if not binders:
                fail(f"no binding of {special} names #'{closer}")
            ctors = {dname for dname, d in tree.defs.items()
                     if any(isinstance(x, list) and ":close-hooks" in [str(t) for t in x if isinstance(t, Sym)]
                            and any(str(x[k]) == ":close-hooks" and k + 1 < len(x) and sym(x[k + 1]) == special
                                    for k in range(len(x) - 1) if isinstance(x[k], Sym))
                            for x, _ in walk(d.body))}
            stops = set()
            for dname, d in tree.defs.items():
                for x, anc in walk(d.body):
                    if not (isinstance(x, list) and head(x) == "dolist" and len(x) > 2 and isinstance(x[1], list)
                            and len(x[1]) >= 2 and isinstance(x[1][1], list) and len(x[1][1]) == 2
                            and sym(x[1][1][0]) == row["hooks_reader"]):
                        continue
                    hv = sym(x[1][0])
                    flag = None
                    for y, _ in walk(x[2:]):
                        if (isinstance(y, list) and head(y) == "handler-case" and len(y) > 2
                                and isinstance(y[1], list) and head(y[1]) == "funcall" and len(y[1]) > 1
                                and sym(y[1][1]) == hv):
                            for cl in y[2:]:
                                if (isinstance(cl, list) and len(cl) == 3 and isinstance(cl[2], list)
                                        and head(cl[2]) == "setq" and len(cl[2]) == 3 and sym(cl[2][2]) == "nil"):
                                    flag = sym(cl[2][1])
                    if flag and any(isinstance(z, list) and (
                            (head(z) == "unless" and len(z) > 2 and sym(z[1]) == flag) or
                            (head(z) == "when" and len(z) > 2 and isinstance(z[1], list) and head(z[1]) == "and"
                             and flag in [sym(t) for t in z[1][1:]]))
                            for z, _ in walk(d.body)):
                        stops.add(dname)
            if not ctors:
                fail(f"no constructor stores {special} as :close-hooks")
            if not stops:
                fail(f"no stop function funcalls each hook of ({row['hooks_reader']} ...) and tests the failure flag")
            ok = False
            for dname, forms in binders:
                heads = set()
                for f, _ in walk(forms):
                    if isinstance(f, list) and f and isinstance(f[0], Sym):
                        heads.add(str(f[0]))
                heads &= set(self.infos)
                if (self.reaches(("u", frozenset(), tuple(sorted(heads)), ()), ctors)
                        and self.reaches(("u", frozenset(), tuple(sorted(heads)), ()), stops)):
                    ok = True
            if not ok:
                fail(f"the binding of {special} does not reach both a constructor and a stop function")
            out[name] = row
        return out

    def verified_dead_call_arms(self) -> dict:
        """{(caller, callee): the callee calls that sit only in the arm CALLER
        has excluded} for the declared edges (contract dead_call_arms) that hold
        up against the source.  CALLER's call to CALLEE passes, as CALLEE's
        RESULTS parameter, a local R that CALLER never assigns, and every such
        call sits in the else branch of (if (eq (first R) TAG) ...).  In CALLEE,
        every call to an ARM_CALLS function sits in the TAG clause of a
        (case (first RESULTS) ...), and no ARM_CALLS function is referenced any
        other way.  Then, reached through that edge, the arm's calls cannot run.
        A row that does not verify is a loud error."""
        out = {}
        tree = self.an.tree
        mutators = {"setq", "setf", "psetq", "psetf", "incf", "decf", "push", "pushnew", "pop", "rotatef", "shiftf"}
        for row in self.c.raw.get("dead_call_arms", []):
            caller, callee, tag = row["function"], row["call"], row["tag"]
            arm_calls = set(row["arm_calls"])

            def fail(why, caller=caller, callee=callee):
                raise ValueError(f"dead_call_arms {caller} -> {callee}: {why}")

            if caller not in self.infos or callee not in self.infos:
                if not (tree.root / row["file"]).exists():
                    continue
                fail("not functions of the analyzed host")
            params = lambda_params(tree.defs[callee].params)
            if row["results_param"] not in params:
                fail(f"{callee} has no parameter {row['results_param']}")
            idx = params.index(row["results_param"])

            def walk(forms, parents):
                """(form, ancestors-with-branch-index) for every list form."""
                stack = [(f, ()) for f in forms]
                while stack:
                    x, anc = stack.pop()
                    yield x, anc
                    if isinstance(x, list):
                        stack.extend((c, anc + ((x, k),)) for k, c in enumerate(x))

            def tag_clause(key):
                return sym(key) == tag or (isinstance(key, list) and any(sym(k) == tag for k in key))

            # CALLEE: the arm's calls live only in the TAG clause of (case (first RESULTS) ...)
            for x, anc in walk(tree.defs[callee].body, ()):
                if isinstance(x, Sym) and str(x) in arm_calls:
                    parent = anc[-1][0] if anc else None
                    if not (isinstance(parent, list) and parent and parent[0] is x):
                        fail(f"{x} is referenced other than by a call in {callee}")
                if isinstance(x, list) and x and head(x) in arm_calls:
                    ok = False
                    for k in range(len(anc) - 1):
                        form, _ = anc[k]
                        clause, _ = anc[k + 1]
                        if (isinstance(form, list) and head(form) in ("case", "ecase") and len(form) > 2
                                and isinstance(form[1], list) and head(form[1]) == "first"
                                and len(form[1]) == 2 and sym(form[1][1]) == row["results_param"]
                                and isinstance(clause, list) and clause and clause is not form[1]
                                and any(clause is c for c in form[2:]) and tag_clause(clause[0])):
                            ok = True
                    if not ok:
                        fail(f"a call to {head(x)} in {callee} is outside the {tag} clause of (case (first {row['results_param']}) ...)")
            # CALLER: every call passes an unassigned local, in the else branch of the tag test
            seen = 0
            for x, anc in walk(tree.defs[caller].body, ()):
                if isinstance(x, Sym) and str(x) == callee:
                    parent = anc[-1][0] if anc else None
                    if not (isinstance(parent, list) and parent and parent[0] is x):
                        fail(f"{callee} is referenced other than by a call in {caller}")
                if not (isinstance(x, list) and x and head(x) == callee):
                    continue
                seen += 1
                arg = x[idx + 1] if len(x) > idx + 1 else None
                if not isinstance(arg, Sym):
                    fail(f"the RESULTS argument of a call in {caller} is not a variable")
                var = str(arg)
                ok = False
                for k, (form, _) in enumerate(anc):
                    if (isinstance(form, list) and head(form) == "if" and len(form) == 4
                            and isinstance(form[1], list) and head(form[1]) in ("eq", "eql") and len(form[1]) == 3):
                        a, b = form[1][1], form[1][2]
                        if sym(b) == tag and isinstance(a, list) and head(a) == "first" and len(a) == 2 \
                                and sym(a[1]) == var:
                            child = anc[k + 1][0] if k + 1 < len(anc) else x
                            if child is form[3]:
                                ok = True
                if not ok:
                    fail(f"a call in {caller} is not in the else branch of (if (eq (first {var}) {tag}) ...)")
                for y, _ in walk(tree.defs[caller].body, ()):
                    if isinstance(y, list) and len(y) > 1 and head(y) in mutators and any(
                            sym(t) == var or (isinstance(t, list) and t and sym(t[0]) == var)
                            for t in y[1:2]):
                        fail(f"{var} is assigned in {caller}")
            if seen == 0:
                fail(f"{caller} has no call to {callee}")
            out[(caller, callee)] = frozenset(arm_calls)
        return out

    def rule_R9(self):
        actors = self.c.raw.get("actors", {})
        dead_arms = self.verified_dead_call_arms()
        for actor, row in actors.items():
            roots = [r for r in row["roots"] if r in self.infos]
            reach: dict[tuple, list] = {}
            stack = [((r, frozenset()), [r]) for r in roots]
            while stack:
                (n, excl), trail = stack.pop()
                if (n, excl) in reach:
                    continue
                reach[(n, excl)] = trail
                for e in self.infos[n].events:
                    if e.kind == "call" and e.name in self.infos:
                        if e.name in excl:
                            continue
                        # EXCL names calls of N itself, never of what N calls
                        nxt = dead_arms.get((n, e.name), frozenset())
                        if (e.name, nxt) not in reach:
                            stack.append(((e.name, nxt), trail + [e.name]))
            for (n, _excl), trail in sorted(reach.items(), key=lambda kv: (kv[0][0], sorted(kv[0][1]))):
                info = self.infos[n]
                for e in info.events:
                    if e.kind == "gate" and "gate_classes" in row:
                        cls = e.extra
                        if cls not in row["gate_classes"]:
                            self.add("R9", info, e.line,
                                     f"actor {actor} enters the gate (class {cls}) and may wait behind a barrier",
                                     f"{actor}:gate", trail)
                    if e.kind == "leaf" and e.extra and e.extra[0] == "await" and row.get("no_await"):
                        if len(e.extra) > 2:
                            continue   # a wrapper call site: the wrapper's own wait leaf is reported
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


def realization_table(root: Path) -> dict:
    """Read the model's table with the non-evaluating reader, never a JSON seed.

    The machine split is followed only when the model actually includes it.
    A parked machine file cannot replace the model's current table.
    """
    paths = [root / "books/host-model.lisp"]
    found = []
    for path in paths:
        text = path.read_text()
        forms = ledger.Reader(text).top_level()
        for form, line in forms:
            if (head(form) == "include-book" and len(form) >= 2
                    and form[1] == "host-model-machine"
                    and not isinstance(form[1], Sym)):
                machine = root / "books/host-model-machine.lisp"
                if machine not in paths:
                    paths.append(machine)
            if (head(form) == "defconst" and len(form) >= 2
                    and str(form[1]) == "*fn-hmc-realization*"):
                if len(form) != 3 or head(form[2]) != "quote" or len(form[2]) != 2:
                    raise ValueError("*fn-hmc-realization* must be one quoted literal")
                found.append((path, text, line, form[2][1]))
    if len(found) != 1:
        raise ValueError(f"model must define exactly one *fn-hmc-realization*, found {len(found)}")

    def literal(value):
        if isinstance(value, Sym):
            if str(value) == "nil":
                return None
            if str(value).startswith(":"):
                return str(value)
            raise ValueError("nonliteral realization symbol: " + str(value))
        if isinstance(value, list):
            if value and isinstance(value[0], Sym) and str(value[0]).startswith(":"):
                if len(value) % 2:
                    raise ValueError("realization property list has an unmatched key")
                data = {}
                for key, item in zip(value[::2], value[1::2]):
                    if not isinstance(key, Sym) or not str(key).startswith(":"):
                        raise ValueError("realization property key must be a keyword")
                    key = str(key)[1:]
                    if key in data:
                        raise ValueError("duplicate realization property: " + key)
                    data[key] = literal(item)
                return data
            return [literal(item) for item in value]
        if isinstance(value, str):
            return value
        raise ValueError("unsupported realization literal")

    path, text, line, form = found[0]
    rows = literal(form)
    if not isinstance(rows, list) or not rows:
        raise ValueError("realization must be a nonempty row list")
    labels = set()
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("label"), str):
            raise ValueError("realization row needs a label")
        if row["label"] in labels:
            raise ValueError("duplicate realization label: " + row["label"])
        labels.add(row["label"])
        if not isinstance(row.get("layer"), str):
            raise ValueError("realization layer must be a string")
        enabled = row.get("enabled")
        row["enabled"] = [enabled] if isinstance(enabled, str) else enabled or []
        row["sites"] = row.get("sites") or []
        if not isinstance(row["enabled"], list) or not all(isinstance(x, str) for x in row["enabled"]):
            raise ValueError("realization enabled must name functions")
        if not isinstance(row["sites"], list):
            raise ValueError("realization sites must be a list")
        for site in row["sites"]:
            if not isinstance(site, dict) or not isinstance(site.get("function"), str):
                raise ValueError("realization site needs a function")
            for key in ("file", "primitive", "core"):
                if site.get(key) is not None and not isinstance(site[key], str):
                    raise ValueError("realization " + key + " must be a string or nil")
            if site.get("capability") is not None and not isinstance(site["capability"], dict):
                raise ValueError("realization capability must be a property list or nil")
            for key in ("locks_held", "requires_before"):
                site[key] = site.get(key) or []
                if not isinstance(site[key], list) or not all(isinstance(x, str) for x in site[key]):
                    raise ValueError("realization " + key + " must be a string list")
    return {"source": {"file": path.relative_to(root).as_posix(),
                       "constant": "*fn-hmc-realization*", "line": line,
                       "sha256": hashlib.sha256(text.encode()).hexdigest()},
            "rows": rows}


def realization_rows(root: Path) -> list:
    return realization_table(root)["rows"]


LABEL_LAYERS = {"C", "P"}


def realized_core_sites(checker: Checker, fn: str, core: str, via: dict, seen=frozenset()) -> list:
    """Where FN makes its ACL2 call CORE: (line, locks held there) for each direct
    call, and for each call of a function the contracts' realization_via names
    for FN (a declared delegation: that helper is the one choke point of the
    call), the locks held at that call plus whatever the helper holds around its
    own realization.  A delegation is followed only where declared."""
    info = checker.infos.get(fn)
    if info is None or fn in seen:
        return []
    out = [(e.line, e.ctx.locks) for e in info.events if e.kind == "core" and e.name == core]
    for helper in via.get(fn, []):
        inner = realized_core_sites(checker, helper, core, via, seen | {fn})
        for e in info.events:
            if e.kind in ("call", "core") and e.name == helper:
                out.extend((e.line, e.ctx.locks | locks) for _, locks in inner)
    return out


def check_realization(checker: Checker) -> None:
    """The host-model realization table (review M3): each label's host sites
    exist, call their primitive and ACL2 subject, hold the label's locks, and
    call each requires_before subject before the primitive; the row's own
    shape is the agreed one (layer C|P, a P label names its A-PRIM-* row
    or :crash's A-CRASH-IMAGE,
    'enabled' names ACL2 functions that exist)."""
    known = getattr(checker.an.reach, "known", set())
    via = checker.c.raw.get("realization_via", {})
    try:
        checker.realization = realization_table(checker.an.tree.root)
    except (OSError, ValueError, ledger.ReadError) as error:
        checker.realization = None
        anchor = FnInfo("realization source", "books/host-model.lisp", 0, True)
        checker.add("R3", anchor, 0, "realization source refused: " + str(error),
                    "realization-source")
        return
    for row in checker.realization["rows"]:
        label = row.get("label", "?")
        anchor = FnInfo("realization " + label, checker.realization["source"]["file"],
                        checker.realization["source"]["line"], True)
        if row.get("layer") not in LABEL_LAYERS:
            checker.add("R3", anchor, 0, f"realization {label}: layer must be C or P", "realization-shape:" + label)
        assumption = row.get("assumption", "")
        if (row.get("layer") == "P" and not str(assumption).startswith("A-PRIM-")
                and not (label == ":crash" and assumption == "A-CRASH-IMAGE")):
            checker.add("R3", anchor, 0, f"realization {label}: a P label names its primitive assumption",
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
            if site.get("file") != info.path:
                checker.add("R3", info, info.line,
                            f"realization {label}: {fn} is in {info.path}, table names {site.get('file')}",
                            "realization-file:" + label)
            prim = site.get("primitive")
            prim_events = [e for e in info.events if (e.kind in ("leaf", "call") and e.name == prim)] if prim else []
            if prim and not prim_events:
                checker.add("R3", info, info.line, f"realization {label}: {fn} no longer calls {prim}",
                            "realization:" + label)
                continue
            core = site.get("core")
            core_sites = realized_core_sites(checker, fn, core, via) if core else []
            if core and not core_sites:
                checker.add("R3", info, info.line, f"realization {label}: {fn} no longer calls {core}",
                            "realization:" + label)
            held_req = set(site.get("locks_held", []))
            if held_req:
                where = [(e.line, e.ctx.locks) for e in prim_events] or core_sites
                for line, locks in where:
                    have = locks | checker.m.mustheld.get(fn, frozenset())
                    if not held_req <= have:
                        checker.add("R3", info, line,
                                    f"realization {label}: {fn} runs {prim or core} holding "
                                    f"{sorted(have)}, the label needs {sorted(held_req)}",
                                    "realization-locks:" + label)
            borrow = checker.c.raw.get("borrows", {}).get(fn)
            for before in site.get("requires_before", []):
                firsts = [e.line for e in info.events if e.kind in ("core", "call") and e.name == before]
                for e in prim_events:
                    # a site that holds a typed borrow (the row's capability) is
                    # dominated by its issue: the function the borrow names issues
                    # the row through BEFORE, and R3 verifies that protocol itself
                    if (site.get("capability") and borrow and borrow.get("issue_core") == before
                            and checker.verify_borrow(info, e, borrow) is None):
                        continue
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


def in_enclave(function: str, path: str, enclave: set, enclave_files: set,
               excepted: dict | None = None) -> bool:
    """A finding is strict when its function is declared migrated or when its
    whole file is (a lambda or thread root of that file included), unless the
    file's declaration excepts that function by name with its why
    (contracts enclave "files_except": {FILE: {FUNCTION: why}})."""
    if function in enclave:
        return True
    if path in enclave_files:
        return function not in (excepted or {}).get(path, {})
    return False


def judge(findings: list[Finding], baseline: dict, enclave: set,
          enclave_files: set = frozenset(), excepted: dict | None = None) -> dict:
    """New: a key absent from the baseline, or over its count; every
    finding inside the enclave (a function, or any function of an enclave
    file).  Stale: a baseline count above today's.  A baseline row inside
    the enclave is refused: strictness admits no baselined finding."""
    counted = weights(findings)
    base_counts = {k: row.get("count", 1) for k, row in baseline.items()}
    new = []
    for f in findings:
        if f.category == "exception":
            continue
        k = f.baseline_key()
        if in_enclave(f.function, f.path, enclave, enclave_files, excepted):
            new.append(("enclave", f))
            continue
        if k not in base_counts or counted[k] > base_counts[k]:
            new.append(("new", f))
    stale = [k for k, n in base_counts.items() if counted.get(k, 0) < n]
    enclave_rows = [k for k, row in baseline.items()
                    if in_enclave(k.split("|")[1], str(row.get("where", "")).rsplit(":", 1)[0],
                                  enclave, enclave_files, excepted)]
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


def lower_stale(path: Path, findings: list[Finding]) -> tuple[list[str], list[str]]:
    """--lower-stale: shrink-only.  Lower each baseline row whose current count
    (the same weights() the verdict uses) is below its count, drop it at 0;
    never add a key, never raise a count, leave every other row untouched.
    Returns (changes, raised); writes only when there is a change."""
    data = json.loads(path.read_text())
    counted = weights(findings)
    changes, raised, rows = [], [], []
    for row in data["findings"]:
        k, n = row["key"], row.get("count", 1)
        now = counted.get(k, 0)
        if now > n:
            raised.append(f"{k}: {n} -> {now} (not applied; a raise)")
        if now >= n:
            rows.append(row)
        elif now == 0:
            changes.append(f"removed {k} (was {n})")
        else:
            rows.append({**row, "count": now})
            changes.append(f"lowered {k}: {n} -> {now}")
    if changes:
        path.write_text(json.dumps({**data, "findings": rows}, indent=1) + "\n")
    return changes, raised


def audit_callbacks(model: Model, raw: dict) -> list[str]:
    """--audit-callbacks: hold a why text's own-file line marker to its ordinal.

    declare_callback_contexts refuses a MISSING ordinal, never a MOVED one:
    a lambda inserted before a declared callback silently re-targets the row,
    and the declaration then masks a different function than its text
    describes (found live in fnn-bpnode-passive-begin, 2026-10-05: three rows
    had drifted onto other lambdas).  A why text that names the callback's own
    file with `file.lisp:NNN' claims that line for the ordinal; this audit
    fails every such marker that disagrees with the line the ordinal resolves
    to.  A row without an own-file marker is not audited and never an error:
    only rows that claim a line are held to it (a marker naming ANOTHER file
    -- a funcall site elsewhere -- is context, not an ordinal claim).
    """
    failures = []
    for lam, row in raw.get("callback_contexts", {}).items():
        info = model.an.infos.get(lam)
        if info is None:
            continue  # a run over other files (a fixture) does not see it
        base = re.escape(Path(info.path).name)
        for mark in re.finditer(rf"\b({base}):(\d+)", row.get("why", "")):
            if int(mark.group(2)) != info.line:
                failures.append(
                    f"callback_contexts {lam}: its why text names {mark.group(0)} but the "
                    f"ordinal resolves to {info.path}:{info.line} -- a lambda insert moved "
                    f"it: re-declare the row (declare_callback_contexts cannot see a move)")
    return failures


def audit_summary(model: Model, raw: dict, failures: list[str]) -> str:
    marked = 0
    for lam in model.declared_callbacks:
        info = model.an.infos.get(lam)
        why = raw.get("callback_contexts", {}).get(lam, {}).get("why", "")
        if info is not None and re.search(rf"\b{re.escape(Path(info.path).name)}:\d+", why):
            marked += 1
    return (f"lock_discipline_check: callback-ordinal audit: {len(model.declared_callbacks)} "
            f"declared row(s), {marked} with an own-file line marker, "
            f"{len(failures)} disagreeing marker(s)")


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
    ap.add_argument("--cap", type=int, default=0,
                    help="with --check: print at most N verdict lines (default 0: every line)")
    ap.add_argument("--lower-stale", action="store_true",
                    help="shrink-only: lower baseline rows whose findings dropped, remove rows at 0; "
                         "never adds a key or raises a count")
    ap.add_argument("--emit-realization", action="store_true")
    ap.add_argument("--audit-callbacks", action="store_true",
                    help="standalone: print only the callback-ordinal audit (which --check's "
                         "verdict already includes) and exit on its failures: a "
                         "callback_contexts why text that names its own file (file.lisp:NNN) "
                         "must name the line the ordinal resolves to; a row without such a "
                         "marker is not audited")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args(argv)
    started = time.time()
    root = Path(args.root).resolve()
    an, model, checker = build(root, Path(args.contracts))
    audit_failures = audit_callbacks(model, checker.c.raw)
    if args.audit_callbacks:
        for why in audit_failures:
            print("lock_discipline_check: " + why)
        print(audit_summary(model, checker.c.raw, audit_failures))
        return 1 if audit_failures else 0
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
        table = getattr(checker, "realization", None)
        if table is None:
            print("lock_discipline_check: refused realization source; no snapshot written")
            return 1
        out.write_text(json.dumps({"comment": "generated literal model table; host sites are checked "
                                   "syntactically, not a refinement proof", **table}, indent=1) + "\n")
        print(f"lock_discipline_check: wrote {REALIZATION}")
        return 0
    enclave = set(checker.c.raw.get("enclave", {}).get("functions", []))
    enclave_files = set(checker.c.raw.get("enclave", {}).get("files", []))
    excepted = checker.c.raw.get("enclave", {}).get("files_except", {})
    missing_files = sorted(f for f in enclave_files if f not in an.tree.files)
    stray = sorted(f"{path}:{fn}" for path, fns in excepted.items()
                   for fn in fns if path not in enclave_files or fn not in an.infos
                   or an.infos[fn].path != path)
    if stray:
        print("lock_discipline_check: enclave files_except names a function its file does not define, "
              "or a file that is no enclave: " + ", ".join(stray))
        return 1
    if missing_files:
        print("lock_discipline_check: enclave names a host file the tree does not read: "
              + ", ".join(missing_files))
        return 1
    if args.lower_stale:
        if args.rule or args.function:
            print("lock_discipline_check: --lower-stale needs the whole finding set (no --rule/--function)")
            return 1
        try:
            changes, raised = lower_stale(Path(args.baseline), findings)
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as e:
            print(f"lock_discipline_check: refusing: baseline unreadable: {e!r}")
            return 1
        for c in changes:
            print("  " + c)
        for r in raised:
            print("  RAISE " + r)
        print(f"lock_discipline_check: --lower-stale: {len(changes)} change(s)" if changes
              else "lock_discipline_check: --lower-stale: nothing to lower")
        return 0
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
    verdict = judge(findings, baseline, enclave, enclave_files, excepted)
    if args.rule or args.function:
        verdict["stale"] = []  # a filtered run cannot judge the whole baseline
    realization_drift = None
    out = root / REALIZATION
    if out.exists() and not args.rule:
        try:
            snapshot = json.loads(out.read_text())
            table = getattr(checker, "realization", None)
            if table is None or any(snapshot.get(key) != table[key] for key in ("source", "rows")):
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
                          "private_owner_io": {"exempt_site_leaf_pairs": checker.private_io,
                                               "runners": {l: sorted(v["functions"])
                                                           for l, v in model.private_owner.items()}},
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
        for lock, n in sorted(checker.private_io.items()):
            print(f"  private-owner I/O under {lock}: {n} R2 (site, leaf) pair(s) exempt in "
                  f"{len(model.private_owner[lock]['functions'])} proved one-shot function(s)")
        print(f"  total {len(findings)}; baselined {len(baseline)} rows (weight "
              f"{sum(r.get('count', 1) for r in baseline.values())}); "
              f"new {nb}; stale baseline rows {len(verdict['stale'])}; enclave {len(enclave)} functions"
              f" + {len(enclave_files)} files ({sum(len(v) for v in excepted.values())} excepted)")
        if args.summary:
            print(audit_summary(model, checker.c.raw, audit_failures))
    if args.check:
        bad = (verdict["new"] or verdict["stale"] or verdict["enclave_baselined"]
               or realization_drift or audit_failures)
        if bad:
            counted = weights(findings)
            cap = args.cap or None
            seen: dict = {}
            for why, f in verdict["new"]:
                seen.setdefault(f.baseline_key(), (why, f))
            lines = []
            for k in sorted(seen):
                why, f = seen[k]
                base = baseline.get(k, {}).get("count", 0)
                lines.append(f"lock_discipline_check: {why.upper()} {k} (count {counted[k]}, baseline {base}) "
                             f"{f.path}:{f.line} {f.rule} {f.function}: {f.message}")
            stale = sorted(set(verdict["stale"]))
            for k in stale:
                lines.append(f"lock_discipline_check: STALE baseline row (lower it with --lower-stale): {k} "
                             f"(count {counted.get(k, 0)}, baseline {baseline[k].get('count', 1)})")
            for k in sorted(verdict["enclave_baselined"]):
                lines.append(f"lock_discipline_check: an enclave finding cannot be baselined: {k}")
            for why in audit_failures:
                lines.append("lock_discipline_check: CALLBACK-AUDIT " + why)
            for line in lines[:cap]:
                print(line)
            if cap and len(lines) > cap:
                print(f"lock_discipline_check: {len(lines) - cap} more line(s) hidden by --cap {cap}")
            print(f"lock_discipline_check: {len(seen)} new key(s), {len(stale)} stale")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
