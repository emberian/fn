#!/usr/bin/env python3
"""tools/depth_check.py -- no new unbounded non-tail recursion on the host-called closure.

Every node thread runs on the control stack the installed launcher passes
(books/heap-reservation.lisp fn-heap-stack-kib, 1,024 KiB: about 5,000 to
30,000 frames of fn's code).  A function that calls itself (or a member of
its mutual-recursion component) OUTSIDE tail position costs one frame per
step, so a walk over a group's article list, a store's records, a history,
a queue or an article's octets dies once that list is long enough: LIST
ACTIVE killed the owner past ~30,000 articles in fn-nntp-group-low
(PKT-877), the open in fn-retain-obligation-ids (PKT-876).  The fix is a
loop twin, (mbe :logic <the recursion> :exec <a tail-recursive loop>) with
a lemma equating them (PRF-345, PRF-352), and this lint keeps new ones out.

WHAT IT READS.  The HOST-CALLED CLOSURE: every ACL2 function a raw host
file (the trust-tagged adapter, host/native/*.lisp: ledger.raw_host_paths)
names -- fnn-call's, fnn-core's, the owner dispatchers' quoted entries and
any other mention -- and everything those reach through tools/callgraph.py's
mention edges (macros followed).  For each `defun' there, the EXECUTABLE
body: an (mbe :logic L :exec E) runs E when the function is guard-verified
or :program (raw Lisp runs the :exec branch), and L when it is a logic-mode
function whose guards are not verified (the host calls through the
executable counterpart, host/native/io.lisp fnn-call, and `*1*' of such a
function evaluates its logic: a loop twin in its :exec never runs; lane
depth-debt, `unverified'); `mbt' runs as t.  A call is in
tail position when it is the body; a branch of an `if'/`cond'/`case' in tail
position; the last form of a `let', `let*', `mv-let', `when', `unless',
`progn$', `prog2$', `return-last' or lambda body in tail position; the last
argument of an `and'/`or' in tail position; the argument of `the' or
`ec-call' in tail position.  Everything else -- an argument, a test, a
binding, anything under a macro this reader does not know -- is not.  The
recursive components are Tarjan's SCCs over function-position calls.

This agrees with the extractor (tools/extract/frontend.lisp over ACL2's
translated terms, tools/nontail_recursions.py) on the closure; the record
planning/evidence/serve-depth-2026-09-28.md gives the comparison.  The
reader is source-level so `make check' needs no ACL2.

THE BASELINE, tools/depth_baseline.json, classifies every non-tail recursion
the closure has today:
  "bounded": {fn: its bound, NAMED: a `*constant*' the tree defines (the
             check reads the defconst), a literal number (depth <= 31, a
             32-octet digest), or a structural bound (a number's decimal
             digits / log n, a fixed record's fields or width, a tree's
             car-nesting or height)};
  "debt":    {fn: what it walks} -- depth an article count, a list of
             articles, records, history entries, queue entries, octets, or
             OPERATOR DATA: a configuration table's rows, a profile field
             (max-config-generations, max-connections, max-consumers) or any
             other count the operator sets.  Not yet a loop.  Only shrinks.
A non-tail recursion on the closure that is in neither fails, and so does a
listed function that no longer is one (remove its entry: the list only
shrinks), and so does a "bounded" entry that names no bound or cites a
constant the tree does not define.

WHY OPERATOR DATA IS NOT A BOUND (lane peer-list-depth, batch AZ).  D27: no
fixed cap on stored data, so a configuration table grows as far as the
operator (or a stream of admin requests) takes it.  Until 2026-09-28 the
baseline accepted "bounded by the operator's profile" / "the peer config
table" as bounds, 128 entries of them, and `peer list' over a peer carrying
~1,100 principals (PRF-171 lifted the 1,024-row cap) died at 1,024 KiB in
fn-napb-before-last, an entry classified "bounded peer-config-row
rendering".  The rule is now mechanical: no named bound, not "bounded".

    python3 tools/depth_check.py                 # the lint (make check)
    python3 tools/depth_check.py --list          # every finding, classified
    python3 tools/depth_check.py --json
    python3 tools/depth_check.py --compare X.json  # against the extractor's rows
                                                   # (nontail_recursions.py --json)
    python3 tools/depth_check.py --driver OUT.lisp  # the extractor's session script

THE GROUND TRUTH.  `--driver' writes an ACL2 session script: the image's
own world (host/native/build.lisp up to its trust tag, so the same books,
host files and attachments in the same order), lane extract-2's
tools/extract/frontend.lisp, and `xt-extract' of this closure's roots into
build/depth-extract.json; then `(logic)', since the front end leaves the
session in :program mode.  Run it in a tree whose books are certified (an
hbox_native scratch tree) under the image's ACL2 launcher, then
`tools/nontail_recursions.py build/depth-extract.json --json > rows.json'
and `--compare rows.json'.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import callgraph  # noqa: E402
import ledger  # noqa: E402
from ledger import Sym  # noqa: E402

ROOT = ledger.ROOT
BASELINE = ROOT / "tools" / "depth_baseline.json"

# Forms that evaluate none of their arguments as code.
OPAQUE = {"quote", "declare", "function", "quasiquote"}


def _name(x) -> str | None:
    return str(x).lower() if isinstance(x, Sym) else None


def _body_forms(forms: list) -> list:
    """FORMS without leading declarations and documentation strings."""
    out = list(forms)
    while len(out) > 1 and (isinstance(out[0], str) and not isinstance(out[0], Sym)
                            or (isinstance(out[0], list) and _name(out[0][0] if out[0] else None) == "declare")):
        out.pop(0)
    return out


def calls(term, tail: bool, out: list) -> None:
    """Append (callee, tailp) for every function-position symbol in TERM."""
    if not isinstance(term, list) or not term:
        return
    op = term[0]
    if isinstance(op, list):  # ((lambda (formals) body) actuals...)
        if op and _name(op[0]) == "lambda":
            for a in term[1:]:
                calls(a, False, out)
            seq(_body_forms(op[2:]), tail, out)
        else:
            for a in term:
                calls(a, False, out)
        return
    name = _name(op)
    if name is None or name in OPAQUE:
        return
    args = term[1:]
    if name == "if":
        if args:
            calls(args[0], False, out)
        for a in args[1:3]:
            calls(a, tail, out)
    elif name == "cond":
        for clause in args:
            if isinstance(clause, list) and clause:
                calls(clause[0], tail and len(clause) == 1, out)
                seq(clause[1:], tail, out)
    elif name in ("case", "ecase"):
        if args:
            calls(args[0], False, out)
        for clause in args[1:]:
            if isinstance(clause, list) and clause:
                seq(clause[1:], tail, out)
    elif name in ("let", "let*"):
        if args and isinstance(args[0], list):
            for binding in args[0]:
                if isinstance(binding, list) and len(binding) > 1:
                    calls(binding[1], False, out)
        seq(_body_forms(args[1:]), tail, out)
    elif name == "mv-let":
        if len(args) > 1:
            calls(args[1], False, out)
        seq(_body_forms(args[2:]), tail, out)
    elif name in ("and", "or"):
        for a in args[:-1]:
            calls(a, False, out)
        if args:
            calls(args[-1], tail, out)
    elif name in ("when", "unless"):
        if args:
            calls(args[0], False, out)
        seq(args[1:], tail, out)
    elif name in ("progn$", "prog2$", "return-last", "progn"):
        seq(args, tail, out)
    elif name == "the":
        if len(args) > 1:
            calls(args[1], tail, out)
    elif name == "ec-call":
        if args:
            calls(args[0], tail, out)
    elif name == "mbe":
        pairs = dict((_name(args[i]), args[i + 1]) for i in range(0, len(args) - 1, 2))
        if _BRANCH[0] in pairs:
            calls(pairs[_BRANCH[0]], tail, out)
    elif name == "mbt":
        return
    else:
        out.append((name, tail))
        for a in args:
            calls(a, False, out)


# Which branch of an `mbe' runs: :exec for a guard-verified (or :program)
# function, whose raw definition the host reaches; :logic for a logic-mode
# function whose guards are not verified, since the host calls ACL2 through
# the executable counterpart (host/native/io.lisp fnn-call, `*1*'), which
# runs such a function's logic -- its :exec twin never runs (lane depth-debt).
_BRANCH = [":exec"]
_LOGIC_RUN: set[str] = set()  # closure()'s unverified logic-mode functions


def body_calls(form, logic: bool) -> list:
    """(callee, tailp) for FORM's body, reading the mbe branch that runs."""
    out: list = []
    _BRANCH[0] = ":logic" if logic else ":exec"
    try:
        seq(_body_forms(form[3:]), True, out)
    finally:
        _BRANCH[0] = ":exec"
    return out


# DATA-SIZED APPENDS (lane depth-debt-2).  `append' recurses on its first
# argument, and a function whose guards are not verified runs its logic
# through `*1*', where binary-append's own recursion runs too: one control-
# stack frame per element of the first argument (the kind-5 persist's
# 40,721 BINARY-APPEND frames, lane depth-debt).  Guard-verified code runs
# the raw `append', a loop.  So on the closure, every `append' in a body that
# runs its logic, whose first argument (every argument but the last) is not a
# literal, a quoted constant, a `*constant*' or a `(list ...)' of fixed
# arity, is a finding: verify the function's guards (so its raw code runs),
# or list it under "append" -> "bounded" with the bound named.
_SMALL_APPEND_HEADS = {"list", "quote"}


def _small_first(arg) -> bool:
    if isinstance(arg, (int, float)) or (isinstance(arg, str) and not isinstance(arg, Sym)):
        return True
    if isinstance(arg, Sym):
        n = _name(arg)
        return n in ("nil", "t") or bool(CONSTANT.fullmatch(n or ""))
    if isinstance(arg, list) and arg:
        if _name(arg[0]) == "coerce" and len(arg) > 1 and isinstance(arg[1], str) \
                and not isinstance(arg[1], Sym):
            return True  # (coerce "literal" 'list)
        return _name(arg[0]) in _SMALL_APPEND_HEADS
    return arg is None


def appends(term, out: list) -> None:
    """Append every data-sized first argument of an `append' in TERM (the
    mbe branch that runs, as `calls' reads it)."""
    if not isinstance(term, list) or not term:
        return
    op = term[0]
    name = _name(op) if not isinstance(op, list) else None
    if name in OPAQUE or name == "mbt":
        return
    if name == "mbe":
        args = term[1:]
        pairs = dict((_name(args[i]), args[i + 1]) for i in range(0, len(args) - 1, 2))
        if _BRANCH[0] in pairs:
            appends(pairs[_BRANCH[0]], out)
        return
    if name in ("append", "binary-append") and len(term) > 2:
        for a in term[1:-1]:
            if not _small_first(a):
                out.append(a)
    if name in ("let", "let*") and len(term) > 1 and isinstance(term[1], list):
        for binding in term[1]:
            if isinstance(binding, list) and len(binding) > 1:
                appends(binding[1], out)
        for a in term[2:]:
            appends(a, out)
        return
    for a in (term if isinstance(op, list) else term[1:]):
        appends(a, out)


def _show(x) -> str:
    if isinstance(x, list):
        return "(" + " ".join(_show(a) for a in x) + ")"
    return _name(x) if isinstance(x, Sym) else repr(x)


def body_appends(form, logic: bool) -> list:
    out: list = []
    _BRANCH[0] = ":logic" if logic else ":exec"
    try:
        for f in _body_forms(form[3:]):
            appends(f, out)
    finally:
        _BRANCH[0] = ":exec"
    return out


def append_findings(defs: dict) -> list[dict]:
    rows = []
    for name, d in sorted(defs.items()):
        form = d.form
        if name not in _LOGIC_RUN:
            continue
        if callgraph.head(form) not in callgraph.FUNCTION_HEADS or len(form) < 4:
            continue
        found = body_appends(form, True)
        if found:
            rows.append({"function": name, "where": "{}:{}".format(d.path, d.line),
                         "first": [_show(a) for a in found]})
    return rows


def _xargs(form) -> dict:
    """The keyword arguments of FORM's (declare (xargs ...)) forms."""
    found: dict = {}
    for item in form[3:]:
        if not (isinstance(item, list) and item and _name(item[0]) == "declare"):
            continue
        for decl in item[1:]:
            if isinstance(decl, list) and decl and _name(decl[0]) == "xargs":
                rest = decl[1:]
                for i in range(0, len(rest) - 1, 2):
                    found[_name(rest[i])] = rest[i + 1]
            elif isinstance(decl, list) and decl and _name(decl[0]) == "type":
                found.setdefault(":guard", True)
    return found


_VERIFY = re.compile(r"\(verify-guards\s+([^\s()]+)", re.IGNORECASE)
_EAGER0 = re.compile(r"\(set-verify-guards-eagerness\s+0\s*\)", re.IGNORECASE)
_EAGER2 = re.compile(r"\(set-verify-guards-eagerness\s+2\s*\)", re.IGNORECASE)


def unverified(defs: dict) -> set[str]:
    """The logic-mode functions of DEFS whose guards are not verified: an
    explicit `:verify-guards nil', no guard declared (eagerness 1 verifies only
    a declared guard), or a book at eagerness 0 -- each unless a
    `(verify-guards NAME' event names it somewhere in books/ or host/."""
    events: set[str] = set()
    eager: dict[str, int] = {}
    for top in ("books", "host"):
        for path in sorted((ROOT / top).rglob("*.lisp")):
            text = path.read_text(encoding="utf-8", errors="replace")
            events.update(m.lower() for m in _VERIFY.findall(text))
            rel = path.relative_to(ROOT).as_posix()
            eager[rel] = 0 if _EAGER0.search(text) else 2 if _EAGER2.search(text) else 1
    out = set()
    for name, d in defs.items():
        form = d.form
        if callgraph.head(form) not in callgraph.FUNCTION_HEADS or len(form) < 4:
            continue
        x = _xargs(form)
        mode = x.get(":mode")
        if isinstance(mode, Sym) and _name(mode) == ":program":
            continue
        vg = x.get(":verify-guards")
        if isinstance(vg, Sym) and _name(vg) == "nil":
            ok = False
        elif vg is not None:
            ok = True
        else:
            level = eager.get(d.path, 1)
            ok = level == 2 or (level == 1 and (":guard" in x or ":stobjs" in x))
        if not ok and name not in events:
            out.add(name)
    return out


def seq(forms: list, tail: bool, out: list) -> None:
    for a in forms[:-1]:
        calls(a, False, out)
    if forms:
        calls(forms[-1], tail, out)


def _sccs(graph: dict[str, list[str]]) -> list[list[str]]:
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on: set[str] = set()
    out: list[list[str]] = []
    counter = [0]
    for start in sorted(graph):
        if start in index:
            continue
        work = [(start, iter(graph.get(start, ())))]
        index[start] = low[start] = counter[0]
        counter[0] += 1
        stack.append(start)
        on.add(start)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(graph.get(w, ()))))
                    advanced = True
                    break
                if w in on:
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                out.append(sorted(comp))
    return out


def _stobj_and_attachment_edges() -> dict[str, set[str]]:
    """name -> what runs for it: an abstract stobj's export (and recognizer,
    creator) -> its :exec function; a constrained function -> its attachment."""
    edges: dict[str, set[str]] = {}

    def attach(form) -> None:
        args = form[1:]
        if args and isinstance(args[0], Sym):  # (defattach f g ...)
            if len(args) > 1 and isinstance(args[1], Sym):
                edges.setdefault(_name(args[0]), set()).add(_name(args[1]))
            return
        for pair in args:  # (defattach (f g) (f2 g2) ...)
            if isinstance(pair, list) and len(pair) >= 2 and all(isinstance(x, Sym) for x in pair[:2]):
                edges.setdefault(_name(pair[0]), set()).add(_name(pair[1]))

    stobjs: dict[str, dict[str, tuple[str, str]]] = {}  # stobj -> export -> (logic, exec)
    attached: dict[str, str] = {}  # attach-stobj: the generic -> its implementation

    def absstobj(form) -> None:
        st = _name(form[1])
        rest = form[2:]
        keys = dict((_name(rest[i]), rest[i + 1]) for i in range(0, len(rest) - 1, 2))
        items = []
        for key, default in ((":recognizer", st + "p"), (":creator", "create-" + st)):
            items.append(keys.get(key, Sym(default)))
        exports = keys.get(":exports")
        items.extend(exports if isinstance(exports, list) else [])
        table = stobjs.setdefault(st, {})
        for item in items:
            if isinstance(item, Sym):
                name = _name(item)
                logic, execname = name + "$a", name + "$c"
            elif isinstance(item, list) and item and isinstance(item[0], Sym):
                name = _name(item[0])
                opts = dict((_name(item[i]), item[i + 1]) for i in range(1, len(item) - 1, 2))
                logic = _name(opts.get(":logic", Sym(name + "$a")))
                execname = _name(opts.get(":exec", Sym(name + "$c")))
            else:
                continue
            table[name] = (logic, execname)

    def visit(form) -> None:
        if not isinstance(form, list) or not form:
            return
        h = _name(form[0])
        if h == "defattach":
            attach(form)
        elif h == "defabsstobj" and len(form) > 1:
            absstobj(form)
        elif h == "attach-stobj" and len(form) > 2:
            attached[_name(form[1])] = _name(form[2])
        elif h in ("encapsulate", "progn", "local", "with-output", "defsection"):
            for item in form[1:]:
                visit(item)

    for path, _relative in ledger.book_paths():
        if _relative.startswith("tests/"):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        if "defattach" not in text and "defabsstobj" not in text and "attach-stobj" not in text:
            continue
        for form, _line in ledger.Reader(text).top_level():
            visit(form)
    # An export runs its stobj's :exec; an attachable stobj's export runs the
    # attached implementation's export of the same :logic function instead.
    for st, table in stobjs.items():
        impl = stobjs.get(attached.get(st, ""), {})
        by_logic = {logic: execname for logic, execname in impl.values()}
        for name, (logic, execname) in table.items():
            edges.setdefault(name, set()).add(by_logic.get(logic, execname))
    return edges


class _Unexpandable(Exception):
    pass


def _fill(template, env: dict):
    """A backquote TEMPLATE with each ,PARAM (and ,@PARAM) replaced from ENV."""
    if isinstance(template, list) and template:
        h = _name(template[0])
        if h == "unquote":
            key = _name(template[1]) if len(template) > 1 else None
            if key not in env:
                raise _Unexpandable(key)
            return env[key]
        out = []
        for item in template:
            if isinstance(item, list) and item and _name(item[0]) == "unquote-splicing":
                key = _name(item[1]) if len(item) > 1 else None
                if key not in env or not isinstance(env[key], list):
                    raise _Unexpandable(key)
                out.extend(env[key])
            else:
                out.append(_fill(item, env))
        return out
    return template


def _macro_written_defuns(graph) -> dict[str, callgraph.Definition]:
    """Defuns a macro writes: a `defmacro' whose body is one backquoted
    `defun' over plain parameters (books/article-header-census.lisp's
    fn-ahl-census-step), expanded at each top-level use in a book.  A macro
    that computes its defun any other way is not seen (the extractor is)."""
    writers = {}
    for name, definitions in graph.definitions.items():
        for d in definitions:
            form = d.form
            if (d.kind != "macro" or d.path.startswith("tests/") or len(form) != 4
                    or not isinstance(form[2], list)
                    or not all(isinstance(p, Sym) and not str(p).startswith("&") for p in form[2])):
                continue
            body = form[3]
            if (isinstance(body, list) and len(body) == 2 and _name(body[0]) == "quasiquote"
                    and isinstance(body[1], list) and body[1]
                    and _name(body[1][0]) in ("defun", "defund")):
                writers[name] = ([_name(p) for p in form[2]], body[1])
    found: dict[str, callgraph.Definition] = {}
    if not writers:
        return found
    for path, relative in ledger.book_paths():
        if relative.startswith("tests/"):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        if not any("(" + w + " " in text for w in writers):
            continue
        for form, line in ledger.Reader(text).top_level():
            h = _name(form[0]) if isinstance(form, list) and form else None
            if h not in writers:
                continue
            params, template = writers[h]
            if len(form) - 1 != len(params):
                continue
            try:
                expanded = _fill(template, dict(zip(params, form[1:])))
            except _Unexpandable:
                continue
            defined = _name(expanded[1]) if len(expanded) > 1 else None
            if defined:
                found[defined] = callgraph.Definition(defined, "function", relative, line, expanded)
    return found


def closure() -> tuple[dict[str, callgraph.Definition], set[str]]:
    """(the ACL2 function definitions of the host-called closure, the roots).

    The walk follows what RUNS: a function's executable body's calls (its
    mbe :exec branch; the :logic branch of a logic-mode function whose guards
    are not verified, which the host's *1* call runs), a macro's every mention (its template
    builds the calls), an abstract stobj export's :exec function and a
    constrained function's attachment."""
    tree = ledger.load_tree()
    raw = ledger.raw_host_paths(tree)
    graph = callgraph.build(callgraph.tree_files())
    functions: dict[str, callgraph.Definition] = {}
    macros: set[str] = set()
    for name, definitions in graph.definitions.items():
        for d in definitions:
            if d.path in raw or d.path.startswith("tests/"):
                continue
            if d.kind in ("function", "record"):
                functions.setdefault(name, d)
            elif d.kind == "macro":
                macros.add(name)
    for name, d in _macro_written_defuns(graph).items():
        functions.setdefault(name, d)
    extra = _stobj_and_attachment_edges()
    named: set[str] = set()
    for relative in sorted(raw):
        for form, _line in tree.hosts[relative].forms:
            callgraph.symbols(form, named)
    roots = {n for n in named if n in functions or n in extra}
    logic_run = unverified(functions)
    _LOGIC_RUN.clear()
    _LOGIC_RUN.update(logic_run)

    def successors(name: str) -> set[str]:
        found: set[str] = set(extra.get(name, ()))
        if name in tree.constrained:  # a local witness never runs; its attachment does
            pass
        elif name in functions:
            d = functions[name]
            if callgraph.head(d.form) in callgraph.FUNCTION_HEADS and len(d.form) >= 4:
                out = body_calls(d.form, name in logic_run)
                found |= {c for c, _ in out}
            else:  # a record's generated definitions: every mention
                found |= graph.edges.get(name, set())
        if name in macros:
            found |= graph.edges.get(name, set())
        return {n for n in found if n in functions or n in macros or n in extra}

    reached = set(roots)
    frontier = sorted(roots)
    while frontier:
        following = []
        for name in frontier:
            for one in successors(name):
                if one not in reached:
                    reached.add(one)
                    following.append(one)
        frontier = following
    return {n: functions[n] for n in reached
            if n in functions and n not in tree.constrained}, roots


def findings() -> tuple[list[dict], int, int]:
    """(every non-tail recursion on the closure, closure size, root count)."""
    defs, roots = closure()
    _LAST_DEFS.clear()
    _LAST_DEFS.update(defs)
    sites: dict[str, list] = {}
    for name, d in defs.items():
        form = d.form
        if callgraph.head(form) not in callgraph.FUNCTION_HEADS or len(form) < 4:
            continue
        sites[name] = body_calls(form, name in _LOGIC_RUN)
    graph = {n: sorted({c for c, _ in s if c in sites}) for n, s in sites.items()}
    rows = []
    for comp in _sccs(graph):
        members = set(comp)
        if len(comp) == 1 and comp[0] not in graph[comp[0]]:
            continue
        for fn in comp:
            bad = sorted({c for c, tail in sites[fn] if c in members and not tail})
            if bad:
                d = defs[fn]
                rows.append({"function": fn, "component": comp, "nontail_calls": bad,
                             "where": "{}:{}".format(d.path, d.line)})
    rows.sort(key=lambda r: r["function"])
    return rows, len(sites), len(roots)


_LAST_DEFS: dict = {}


def load_baseline(path: Path = BASELINE) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    app = data.get("append", {})
    return {"bounded": dict(data.get("bounded", {})), "debt": dict(data.get("debt", {})),
            "append": {"bounded": dict(app.get("bounded", {})), "debt": dict(app.get("debt", {}))}}


def check_appends(rows: list[dict], baseline: dict) -> list[str]:
    """The data-sized append rule (see `appends'): the same only-shrinks
    discipline as the recursions, under the baseline's "append" key."""
    listed = baseline.get("append", {"bounded": {}, "debt": {}})
    problems = []
    found = {r["function"]: r for r in rows}
    for fn, r in sorted(found.items()):
        if fn in listed["bounded"] or fn in listed["debt"]:
            continue
        problems.append(
            "{} ({}): appends onto {} in a body the host runs through *1* (its guards are "
            "not verified), where binary-append recurses once per element of its first "
            "argument.  Verify the function's guards (the raw append is a loop), or list it "
            "under \"append\" -> \"bounded\" in tools/depth_baseline.json with the bound "
            "named".format(fn, r["where"], ", ".join(r["first"])))
    for kind in ("bounded", "debt"):
        for fn in sorted(set(listed[kind]) - set(found)):
            problems.append("{}: listed under \"append\" -> \"{}\" but no longer appends data "
                            "through *1* on the closure: remove its entry".format(fn, kind))
    for fn, why in sorted(listed["bounded"].items()):
        text = why if isinstance(why, str) else ""
        if not (CONSTANT.search(text) or LITERAL.search(text) or STRUCTURAL.search(text)):
            problems.append("{}: its \"append\" -> \"bounded\" entry names no bound ({!r})".format(
                fn, text))
    return problems


def check(rows: list[dict], baseline: dict, constants: set[str] | None = None) -> list[str]:
    problems = []
    found = {r["function"]: r for r in rows}
    both = set(baseline["bounded"]) & set(baseline["debt"])
    for fn in sorted(both):
        problems.append("{}: listed as both bounded and debt".format(fn))
    for fn, r in sorted(found.items()):
        if fn in baseline["bounded"] or fn in baseline["debt"]:
            continue
        problems.append(
            "{} ({}): a non-tail recursion on the host-called closure (calls {} outside "
            "tail position): one control-stack frame per step, and every node thread has "
            "1,024 KiB.  Make it a loop twin, (mbe :logic <this> :exec <a tail-recursive "
            "loop>) with its equality lemma (docs/proof-style.md, PRF-352), or, if its depth "
            "is bounded by something that is not an article count, a group's article list, "
            "a history, a queue, an octet count or operator data (a configuration "
            "table, a profile field: D27), list it under \"bounded\" in "
            "tools/depth_baseline.json with the bound named".format(
                fn, r["where"], " ".join(r["nontail_calls"])))
    for kind in ("bounded", "debt"):
        for fn in sorted(set(baseline[kind]) - set(found)):
            problems.append("{}: listed under \"{}\" in tools/depth_baseline.json but no longer "
                            "a non-tail recursion on the host-called closure: remove its entry "
                            "(the list only shrinks)".format(fn, kind))
    known = defined_constants() if constants is None else constants
    for fn, why in sorted(baseline["bounded"].items()):
        text = why if isinstance(why, str) else ""
        cited = CONSTANT.findall(text)
        unknown = sorted(c for c in set(cited) if c.lower() not in known)
        if unknown:
            problems.append("{}: its \"bounded\" entry cites {}, which the tree does not "
                            "define (books/, host/): name the bound that exists".format(
                                fn, " ".join(unknown)))
        elif not (cited or LITERAL.search(text) or STRUCTURAL.search(text)):
            problems.append(
                "{}: a \"bounded\" entry names no bound ({!r}): cite the `*constant*' "
                "or the number that caps its depth, or a structural bound (decimal digits, "
                "a fixed width or shape, car-nesting).  A configuration table, a profile "
                "field or any count the operator sets is data (D27: no fixed cap), not a "
                "bound: make it a loop twin or list it under \"debt\"".format(fn, text))
    return problems


# A named bound (check): a constant, a literal number, or a structural bound.
CONSTANT = re.compile(r"\*[A-Za-z0-9-]+\*")
LITERAL = re.compile(r"\d")
STRUCTURAL = re.compile(r"decimal digits|\blog n\b|\bfixed\b|car-nesting|\bheight\b",
                        re.IGNORECASE)


def defined_constants() -> set[str]:
    """Every `*name*' a book or host file defines by defconst (lower case)."""
    found: set[str] = set()
    pattern = re.compile(r"\(defconst\s+(\*[A-Za-z0-9-]+\*)", re.IGNORECASE)
    for top in ("books", "host"):
        for path in sorted((ROOT / top).rglob("*.lisp")):
            text = path.read_text(encoding="utf-8", errors="replace")
            found.update(m.lower() for m in pattern.findall(text))
    return found


def compare(rows: list[dict], path: str) -> int:
    """Differences with the extractor's rows (tools/nontail_recursions.py --json)."""
    extracted = json.loads(Path(path).read_text(encoding="utf-8"))
    theirs = {r["function"].split("::")[-1].lower() for r in extracted if not r.get("predefined")}
    ours = {r["function"] for r in rows}
    only_ours = sorted(ours - theirs)
    only_theirs = sorted(theirs - ours)
    print("source reader: {}; extractor: {}; both: {}".format(len(ours), len(theirs),
                                                              len(ours & theirs)))
    for fn in only_ours:
        print("only-source", fn)
    for fn in only_theirs:
        print("only-extractor", fn)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--list", action="store_true", help="every finding with its class")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--compare", metavar="ROWS", help="the extractor's rows to compare with")
    parser.add_argument("--driver", metavar="OUT", help="write the extractor's session script")
    arguments = parser.parse_args(argv)
    if arguments.driver:
        _defs, roots = closure()
        text = (ROOT / "host" / "native" / "build.lisp").read_text(encoding="utf-8")
        text = text[:text.index("(defttag :fn-native-host)")]
        text += ('\n(ld "tools/extract/frontend.lisp")\n'
                 "(defconst *depth-roots* '({}))\n"
                 "(defun depth-fns (xs w) (if (endp xs) nil (if (and (function-symbolp (car xs) w) "
                 "(not (eq (getpropc (car xs) 'formals :none w) :none))) (cons (car xs) "
                 "(depth-fns (cdr xs) w)) (depth-fns (cdr xs) w))))\n"
                 '(xt-extract (depth-fns *depth-roots* (w state)) "build/depth-extract.json" state)\n'
                 "(logic)\n"
                 '(value-triple (cw "DEPTH_EXTRACT_DONE~%"))\n').format(" ".join(sorted(roots)))
        Path(arguments.driver).write_text(text, encoding="utf-8")
        print("depth_check: wrote {} ({} roots)".format(arguments.driver, len(roots)), file=sys.stderr)
        return 0
    rows, size, roots = findings()
    if arguments.compare:
        return compare(rows, arguments.compare)
    baseline = load_baseline()
    for r in rows:
        fn = r["function"]
        r["class"] = ("bounded" if fn in baseline["bounded"]
                      else "debt" if fn in baseline["debt"] else "UNLISTED")
        r["why"] = baseline["bounded"].get(fn) or baseline["debt"].get(fn) or ""
    if arguments.json:
        print(json.dumps({"roots": roots, "closure": size, "rows": rows}, indent=1))
    elif arguments.list:
        for r in rows:
            print("{:8s} {:45s} {}  {}".format(r["class"], r["function"], r["where"], r["why"]))
    problems = check(rows, baseline)
    app_rows = append_findings(_LAST_DEFS)
    if arguments.list:
        listed = baseline["append"]
        for r in app_rows:
            cls = ("bounded" if r["function"] in listed["bounded"]
                   else "debt" if r["function"] in listed["debt"] else "UNLISTED")
            print("append-{:8s} {:45s} {}  {}".format(cls, r["function"], r["where"],
                                                     " | ".join(r["first"])))
    problems += check_appends(app_rows, baseline)
    for p in problems:
        print("depth_check: " + p, file=sys.stderr)
    print("depth_check: {} host-called root(s), {} function(s) in the closure, {} non-tail "
          "recursion(s): {} bounded, {} debt; {} data-sized append(s) through *1*: {} bounded, {} debt; "
          "{} problem(s)".format(
              roots, size, len(rows), sum(r["class"] == "bounded" for r in rows),
              sum(r["class"] == "debt" for r in rows), len(app_rows),
              sum(r["function"] in baseline["append"]["bounded"] for r in app_rows),
              sum(r["function"] in baseline["append"]["debt"] for r in app_rows),
              len(problems)), file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
