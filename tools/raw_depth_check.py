#!/usr/bin/env python3
"""tools/raw_depth_check.py -- no new unbounded non-tail recursion in the raw host code.

tools/depth_check.py lints the ACL2 functions the host calls; the raw
Common Lisp the image loads under the trust tag (host/native/*.lisp: the
sockets, threads, files, the command line and the adapter that calls ACL2)
runs on the same 1,024 KiB control stack (books/heap-reservation.lisp
fn-heap-stack-kib) and nothing read it (lane peer-list-depth's obstruction,
2026-09-28).  This is that lint: every `defun' (and every `labels' function
inside one) in host/native/*.lisp that calls itself, or a member of its
recursive component, outside tail position.

TAIL POSITION in raw Lisp is narrower than in ACL2's translated terms,
because SBCL merges a tail call only when no dynamic state is left to undo:
the body of `if'/`cond'/`case'/`typecase' branches, the last form of `progn',
`let', `let*', `when', `unless', `block', `locally', `multiple-value-bind',
`destructuring-bind', `flet'/`labels' bodies and `lambda' bodies, the last
argument of `and'/`or', the argument of `the'.  NOT tail: anything under
`handler-case', `handler-bind', `unwind-protect', `catch', `with-*' macros,
`loop', `dolist', `dotimes', `prog1', a special binding (a `let' that binds
a *special*: SBCL must unbind it), an argument or a test.  Unknown forms are
not tail (conservative, as depth_check is).  `funcall', `apply' and #'f
passed as a value are not direct calls; recursion through them is not seen.
A `lambda' passed as an argument is read as called here (a handler or a
serialized quantum runs it on this stack), except under `make-thread', whose
function runs on the new thread's own stack.

THE BASELINE, tools/raw_depth_baseline.json, has depth_check's two classes
and rules (tools/depth_check.py check): "bounded" names its bound (a
*constant* the tree defines, a number, or a structural bound), "debt" only
shrinks, an unlisted finding fails, a listed function that no longer is one
fails.  An empty baseline is the goal and the state at its introduction.

    python3 tools/raw_depth_check.py           # the lint (make check)
    python3 tools/raw_depth_check.py --list    # every finding with its class
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import depth_check  # noqa: E402
import ledger  # noqa: E402
from ledger import Sym  # noqa: E402

ROOT = ledger.ROOT
BASELINE = ROOT / "tools" / "raw_depth_baseline.json"
RAW_DIR = "host/native"

OPAQUE = {"quote", "function", "quasiquote", "declare"}
# The body's last form is in tail position.
LAST_TAIL = {"progn", "locally", "when", "unless"}
BLOCKLIKE = {"block"}  # (block NAME . body)
BINDERS = {"let", "let*"}
LAST_AFTER_2 = {"multiple-value-bind", "destructuring-bind"}  # (m VARS FORM . body)
# The arguments run on another thread's stack, not this one's.
NEW_THREAD = {"sb-thread:make-thread", "make-thread", "sb-thread::make-thread"}
# The body is not in tail position: a handler, cleanup or iteration frame.
NEVER_TAIL = {"handler-case", "handler-bind", "unwind-protect", "catch", "loop",
              "dolist", "dotimes", "do", "do*", "prog1", "prog2", "ignore-errors",
              "restart-case", "with-open-file", "with-open-stream",
              "without-interrupts", "with-timeout", "with-lock-held",
              "with-recursive-lock", "with-mutex", "with-recursive-lock-held"}


def _name(x) -> str | None:
    return str(x).lower() if isinstance(x, Sym) else None


def _body(forms: list) -> list:
    out = list(forms)
    while len(out) > 1 and ((isinstance(out[0], str) and not isinstance(out[0], Sym))
                            or (isinstance(out[0], list) and out[0]
                                and _name(out[0][0]) == "declare")):
        out.pop(0)
    return out


def _special(sym) -> bool:
    n = _name(sym)
    return bool(n) and len(n) > 2 and n.startswith("*") and n.endswith("*")


class Walker:
    """Collects (callee, tailp) for one function body; `labels'/`flet'
    functions found inside are recorded as their own definitions."""

    def __init__(self, owner: str, local_defs: dict) -> None:
        self.owner = owner
        self.local_defs = local_defs  # qualified name -> (lambda-list, body forms)
        self.scopes: list[dict[str, str]] = []

    def resolve(self, name: str) -> str:
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        return name

    def seq(self, forms: list, tail: bool, out: list) -> None:
        for f in forms[:-1]:
            self.term(f, False, out)
        if forms:
            self.term(forms[-1], tail, out)

    def term(self, t, tail: bool, out: list) -> None:
        if not isinstance(t, list) or not t:
            return
        op = t[0]
        if isinstance(op, list):
            if op and _name(op[0]) == "lambda":
                for a in t[1:]:
                    self.term(a, False, out)
                self.seq(_body(op[2:]), tail, out)
            else:
                for a in t:
                    self.term(a, False, out)
            return
        name = _name(op)
        if name is None:
            return
        if name.startswith("#"):  # a reader conditional's feature expression
            return
        args = t[1:]
        if name in OPAQUE:
            return
        if name == "if":
            if args:
                self.term(args[0], False, out)
            for a in args[1:3]:
                self.term(a, tail, out)
        elif name == "cond":
            for clause in args:
                if isinstance(clause, list) and clause:
                    self.term(clause[0], tail and len(clause) == 1, out)
                    self.seq(clause[1:], tail, out)
        elif name in ("case", "ecase", "typecase", "etypecase", "ccase"):
            if args:
                self.term(args[0], False, out)
            for clause in args[1:]:
                if isinstance(clause, list) and clause:
                    self.seq(clause[1:], tail, out)
        elif name in BINDERS:
            bindings = args[0] if args and isinstance(args[0], list) else []
            special = False
            for b in bindings:
                if isinstance(b, list) and b:
                    special = special or _special(b[0])
                    if len(b) > 1:
                        self.term(b[1], False, out)
                else:
                    special = special or _special(b)
            self.seq(_body(args[1:]), tail and not special, out)
        elif name in LAST_TAIL:
            if name in ("when", "unless"):
                if args:
                    self.term(args[0], False, out)
                self.seq(args[1:], tail, out)
            else:
                self.seq(args, tail, out)
        elif name in BLOCKLIKE:
            self.seq(args[1:], tail, out)
        elif name in LAST_AFTER_2:
            if len(args) > 1:
                self.term(args[1], False, out)
            self.seq(_body(args[2:]), tail, out)
        elif name in ("and", "or"):
            for a in args[:-1]:
                self.term(a, False, out)
            if args:
                self.term(args[-1], tail, out)
        elif name == "the":
            if len(args) > 1:
                self.term(args[1], tail, out)
        elif name in ("flet", "labels"):
            defs = args[0] if args and isinstance(args[0], list) else []
            scope = {}
            for d in defs:
                if isinstance(d, list) and d and isinstance(d[0], Sym):
                    scope[_name(d[0])] = "{}/{}".format(self.owner, _name(d[0]))
            if name == "labels":
                self.scopes.append(scope)
            for d in defs:
                if isinstance(d, list) and len(d) >= 2 and isinstance(d[0], Sym):
                    self.local_defs[scope[_name(d[0])]] = (d[1], _body(d[2:]), list(self.scopes))
            if name == "flet":
                self.scopes.append(scope)
            self.seq(_body(args[1:]), tail, out)
            self.scopes.pop()
        elif name in NEW_THREAD:
            return  # the function runs on the new thread's own stack
        elif name in NEVER_TAIL or name.startswith("with-"):
            for a in args:
                self.term(a, False, out)
        else:
            out.append((self.resolve(name), tail))
            for a in args:
                self.term(a, False, out)


def _defuns(form, found: list, line: int) -> None:
    """Every top-level defun of FORM, looking through progn/eval-when/locally."""
    if not isinstance(form, list) or not form:
        return
    h = _name(form[0])
    if h == "defun" and len(form) >= 4 and isinstance(form[1], Sym):
        found.append((_name(form[1]), form[2], _body(form[3:]), line))
    elif h in ("progn", "eval-when", "locally"):
        for item in form[1:]:
            _defuns(item, found, line)


def definitions(root: Path = ROOT) -> dict[str, tuple[str, int, list]]:
    """name -> (file, line, [(callee, tailp)]) over every raw host function,
    `labels'/`flet' functions as OWNER/NAME."""
    out: dict[str, tuple[str, int, list]] = {}
    for path in sorted((root / RAW_DIR).glob("*.lisp")):
        relative = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8", errors="replace")
        found: list = []
        for form, line in ledger.Reader(text).top_level():
            _defuns(form, found, line)
        for name, _ll, body, line in found:
            local: dict = {}
            w = Walker(name, local)
            sites: list = []
            w.seq(body, True, sites)
            out.setdefault(name, (relative, line, sites))
            pending = dict(local)
            while pending:
                qualified, (_ll2, lbody, scopes) = pending.popitem()
                local2: dict = {}
                w2 = Walker(qualified.split("/")[0], local2)
                w2.scopes = scopes + [{qualified.split("/")[-1]: qualified}]
                s2: list = []
                w2.seq(lbody, True, s2)
                out.setdefault(qualified, (relative, line, s2))
                pending.update({k: v for k, v in local2.items() if k not in out})
    return out


def findings(root: Path = ROOT) -> tuple[list[dict], int]:
    defs = definitions(root)
    graph = {n: sorted({c for c, _ in s if c in defs}) for n, (_f, _l, s) in defs.items()}
    rows = []
    for comp in depth_check._sccs(graph):
        members = set(comp)
        if len(comp) == 1 and comp[0] not in graph[comp[0]]:
            continue
        for fn in comp:
            f, line, sites = defs[fn]
            bad = sorted({c for c, tail in sites if c in members and not tail})
            if bad:
                rows.append({"function": fn, "component": comp, "nontail_calls": bad,
                             "where": "{}:{}".format(f, line)})
    rows.sort(key=lambda r: r["function"])
    return rows, len(defs)


def load_baseline(path: Path = BASELINE) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    return {"bounded": dict(data.get("bounded", {})), "debt": dict(data.get("debt", {}))}


def check(rows: list[dict], baseline: dict, constants: set[str] | None = None) -> list[str]:
    """depth_check's rules, with the raw lint's advice for an unlisted finding."""
    problems = []
    listed = set(baseline["bounded"]) | set(baseline["debt"])
    for r in rows:
        if r["function"] not in listed:
            problems.append(
                "{} ({}): a non-tail recursion in the raw host code (calls {} outside tail "
                "position): one control-stack frame per step on a 1,024 KiB stack.  Make it "
                "a loop (an accumulator and a tail call, or `loop'/`do'), or list it in "
                "tools/raw_depth_baseline.json: \"bounded\" with its bound named (a "
                "*constant*, a number, a structural bound), never operator data "
                "(D27)".format(r["function"], r["where"], " ".join(r["nontail_calls"])))
    unlisted = [r for r in rows if r["function"] in listed]
    for p in depth_check.check(unlisted, baseline, constants):
        problems.append(p.replace("tools/depth_baseline.json", "tools/raw_depth_baseline.json")
                        .replace("on the host-called closure", "in the raw host code"))
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--list", action="store_true", help="every finding with its class")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args(argv)
    rows, size = findings()
    baseline = load_baseline()
    for r in rows:
        fn = r["function"]
        r["class"] = ("bounded" if fn in baseline["bounded"]
                      else "debt" if fn in baseline["debt"] else "UNLISTED")
        r["why"] = baseline["bounded"].get(fn) or baseline["debt"].get(fn) or ""
    if arguments.json:
        print(json.dumps({"functions": size, "rows": rows}, indent=1))
    elif arguments.list:
        for r in rows:
            print("{:8s} {:45s} {}  {}".format(r["class"], r["function"], r["where"], r["why"]))
    problems = check(rows, baseline)
    for p in problems:
        print("raw_depth_check: " + p, file=sys.stderr)
    print("raw_depth_check: {} raw host function(s) in {}/*.lisp, {} non-tail recursion(s): "
          "{} bounded, {} debt, {} problem(s)".format(
              size, RAW_DIR, len(rows), sum(r["class"] == "bounded" for r in rows),
              sum(r["class"] == "debt" for r in rows), len(problems)), file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
