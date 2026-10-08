#!/usr/bin/env python3
"""A def-carried row on a stobj state names every declared entry that returns it.

THE RULE (books/def-carried.lisp fn-cd-problem, the refusal the image build
raises in fnn-install-raw-dispatch / definterface's :raw-with (:carried NAME)):

    host-called entry X (fn-interfaces) returns the carried state STATE and is
    neither a transition nor an establishing point of NAME, nor owed under
    A-ID: its preservation theorem is owed.

* An entry is every `definterface' of the tree (the `fn-interfaces' table,
  not only the raw-dispatched ones).  It "returns the carried state" when
  the carried stobj (the one formal of the row's :invariant) is among the
  entry's `stobjs-out' -- a RETURNED stobj, not a declared :stobjs formal: an
  entry that only reads `state' is outside the rule.
* Every such entry must be a :transitions or :established name of the row or
  occur in its :incomplete (A-ID (NAME ...)) list.
* STALE: an :incomplete name that is no function or returns no state, and an
  :incomplete name that is also a transition or establishing point (its
  theorem is proved: it leaves the owed list).  Both are refused by the image.

DECIDABILITY.  The image reads `stobjs-out' from the certified world; this
reads it from the source, by the way ACL2 derives it: an entry returns
`state' at an output position when its body's result there is the variable
`state' or a call that does (mv, if/cond/case/let/mv-let/pprogn/er-let*
tails, calls of tree functions to a fixpoint, the ACL2 state primitives
below).  A function without a `state' formal cannot return it (exact).  What
the source cannot decide -- a macro of the tree in tail position, a call of a
function the tree does not define that is handed `state', an entry no book or
host file defines, a congruent stobj -- is listed UNDECIDED and is never a
failure and never silently counted clean: the image build judges those.

    python3 tools/carried_entries.py          # report, with the undecided list
    python3 tools/carried_entries.py --check  # exit 1 on a finding
(`tools/interface_emit.py --check' runs it: the runner's fast checks.)
"""
from __future__ import annotations

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402
from tools import interface_kinds  # noqa: E402

Sym = ledger.Sym

# Output signatures: a tuple of booleans, True where the position is the
# carried stobj; BOTTOM for a term that never returns (hard error, recursion
# in progress); None for a term the source cannot decide.
BOTTOM = "bottom"

# ACL2 primitives and macros whose stobjs-out are known: head -> signature.
PRIMS = {
    "f-put-global": (True,), "put-global": (True,), "princ$": (True,),
    "newline": (True,), "set-print-case": (True,), "close-input-channel": (True,),
    "close-output-channel": (True,), "write-byte$": (True,), "write-char$": (True,),
    "update-acl2-oracle": (True,), "increment-timer": (True,), "set-timer": (True,),
    "set-gag-mode": (True,),
    "fmt": (False, True), "fmt1": (False, True), "fms": (True,), "fms!": (True,),
    "fmt!": (False, True), "fmt1!": (False, True), "print-object$": (True,),
    "open-input-channel": (False, True), "open-output-channel": (False, True),
    "read-byte$": (False, True), "read-char$": (False, True),
    "read-object": (False, False, True), "read-acl2-oracle": (False, False, True),
    "value": (False, False, True), "value-triple": (False, False, True),
    "assign": (False, False, True), "er": (False, False, True),
    "read-file-into-string": None, "getenv$": (False, True), "get-universal-time": (False, True),
    "putenv$": (False, True), "system-call+": (False, False, False, True),
    "read-run-time": (False, True), "read-idate": (False, True),
}
# Heads that read the carried state or are plain values in every use here.
PURE_HEADS = {
    "f-get-global", "get-global", "boundp-global", "state-p", "mv-nth", "list", "cons",
    "car", "cdr", "equal", "and", "or", "not", "quote", "nth", "len", "append", "member",
    "assoc", "true-listp", "natp", "integerp", "stringp", "symbolp", "consp", "atom",
    "+", "-", "*", "<", ">", "<=", ">=", "1+", "1-", "eq", "eql", "null", "append",
    "length", "nfix", "ifix", "zp", "endp", "list*", "acons", "update-nth", "ec-call",
    "declare", "the", "int=", "lnot", "logand", "logior", "ash", "mod", "floor", "truncate",
}
HARD_ERRORS = {"hard-error", "illegal", "abort!", "assert$", "cw", "prog2$", "progn$"}
SEQUENCES = {"pprogn", "progn$", "prog2$", "progn", "time$", "with-guard-checking",
             "with-output", "ec-call", "must-be-equal", "serialize-write"}
LET_LIKE = {"let", "let*", "flet", "labels", "with-local-stobj", "stobj-let", "b*"}


def _s(x) -> str:
    return str(x).lower()


def _bodies(definition) -> list:
    """The forms after the formals, past declarations and the docstring."""
    rest = definition.form[3:]
    out = []
    for form in rest:
        if isinstance(form, list) and form and _s(form[0]) == "declare":
            continue
        if isinstance(form, str) and not isinstance(form, Sym):
            continue
        out.append(form)
    return out


def _merge(a, b):
    if a == BOTTOM:
        return b
    if b == BOTTOM:
        return a
    if a is None or b is None:
        return None
    if len(a) != len(b):
        return None
    return tuple(x or y for x, y in zip(a, b))


class Inference:
    """stobjs-out of tree functions at the position of the carried stobj ST."""

    def __init__(self, source, st: str = "state", stobj_functions=frozenset()):
        self.source = source
        self.st = st
        # defabsstobj exports and defstobj creators: functions over their own
        # stobj, which return `state' only if they take it (none does)
        self.stobj_functions = stobj_functions
        self.memo: dict[str, object] = {}
        self.open: set[str] = set()

    def function(self, name: str):
        """Signature of NAME: tuple, BOTTOM, or None (undecided)."""
        if name in self.memo:
            return self.memo[name]
        definition = self.source.definitions.get(name)
        if definition is None:
            if self.st == "state" and (name in self.stobj_functions
                                       or name.startswith("create-")):
                self.memo[name] = (False,)
                return self.memo[name]
            return None
        formals = definition.form[2]
        if not isinstance(formals, list) or self.st not in {_s(f) for f in formals}:
            self.memo[name] = (False,)      # no state variable: nothing to return
            return self.memo[name]
        if name in self.open:
            return BOTTOM
        self.open.add(name)
        try:
            bodies = _bodies(definition)
            sig = self.term(bodies[-1], name) if bodies else None
        finally:
            self.open.discard(name)
        if sig == BOTTOM:
            sig = None
        self.memo[name] = sig
        return sig

    def returns(self, name: str):
        """True, False, or None (undecided)."""
        sig = self.function(name)
        if sig is None or sig == BOTTOM:
            return None
        return any(sig)

    def term(self, t, owner: str):
        if isinstance(t, Sym):
            return (True,) if _s(t) == self.st else (False,)
        if not isinstance(t, list):
            return (False,)
        if not t:
            return (False,)
        head = _s(t[0]) if isinstance(t[0], str) else None
        if head is None:
            return None                     # ((lambda ...) ...)
        args = t[1:]
        if head == "quote":
            return (False,)
        if head == "if":
            return self._all([self.term(a, owner) for a in args[1:]])
        if head == "cond":
            return self._all([self.term(c[-1], owner) if isinstance(c, list) and len(c) > 1
                              else (False,) for c in args])
        if head in ("case", "case-match", "typecase"):
            return self._all([self.term(c[-1], owner) for c in args[1:]
                              if isinstance(c, list) and len(c) > 1])
        if head in ("when", "unless"):
            return self._all([self.term(args[-1], owner), (False,)]) if len(args) > 1 else None
        if head == "mv":
            return tuple(self._is_st(a) for a in args)
        if head in ("mv-let", "mv?-let"):
            return self.term(args[-1], owner) if len(args) >= 3 else None
        if head in LET_LIKE:
            return self.term(args[-1], owner) if len(args) >= 2 else None
        if head in SEQUENCES:
            return self.term(args[-1], owner) if args else None
        if head == "mbe":
            plist = ledger.keyword_plist(args)
            return self.term(plist[":exec"], owner) if ":exec" in plist else None
        if head == "er-let*":
            body = self.term(args[-1], owner)
            return _merge((False, False, True), body)
        if head == "er":
            return BOTTOM if args and _s(args[0]) == "hard" else (False, False, True)
        if head in ("hard-error", "illegal", "abort!"):
            return BOTTOM
        if head in PRIMS:
            return PRIMS[head]
        if head in self.source.definitions or head in self.stobj_functions:
            return self.function(head)
        if head in self.source.macros:
            return None
        if head in PURE_HEADS:
            return (False,)
        # a function the tree does not define: a builtin.  Handed the state it
        # may well return it, and the source cannot say.
        if any(self._is_st(a) for a in args if not isinstance(a, list)):
            return None
        return (False,)

    def _is_st(self, a) -> bool:
        return isinstance(a, Sym) and _s(a) == self.st

    @staticmethod
    def _all(sigs):
        out = BOTTOM
        for sig in sigs:
            out = _merge(out, sig)
        return out


def invariant_stobj(rows_source, invariant: str):
    """The row's carried stobj: the one formal of its :invariant when that is
    a stobj (`state' or named by :stobjs), else None (a value row)."""
    definition = rows_source.definitions.get(invariant)
    if definition is None or not isinstance(definition.form[2], list):
        return None
    formals = [_s(f) for f in definition.form[2]]
    if len(formals) != 1:
        return None
    if formals[0] in interface_kinds.stobj_formals(definition):
        return formals[0]
    return None


def row_forms(root: Path = ROOT) -> list[dict]:
    """Every top-level def-carried form with an :invariant, as a dict."""
    out = []
    for directory in ("books", "host"):
        for path in sorted((root / directory).glob("*.lisp")):
            text = path.read_text(encoding="utf-8", errors="replace")
            if "(def-carried " not in text:
                continue
            for form, line in ledger.Reader(text).top_level():
                if ledger.head(form) != "def-carried" or len(form) < 2:
                    continue
                kv = ledger.keyword_plist(form[2:])
                incomplete = kv.get(":incomplete")

                def names(key):
                    return [_s(e[0]) for e in (kv.get(key) or [])
                            if isinstance(e, list) and e and isinstance(e[0], str)]

                out.append({
                    "name": _s(form[1]),
                    "where": "{}:{}".format(path.relative_to(root).as_posix(), line),
                    "invariant": _s(kv[":invariant"]) if ":invariant" in kv else None,
                    "established": names(":established"),
                    "transitions": names(":transitions"),
                    "assumption": (_s(incomplete[0]) if isinstance(incomplete, list)
                                   and len(incomplete) == 2 else None),
                    "owed": ([_s(x) for x in incomplete[1]] if isinstance(incomplete, list)
                             and len(incomplete) == 2 and isinstance(incomplete[1], list)
                             else []),
                })
    return out


def stobj_functions(files) -> set[str]:
    """The functions defabsstobj :exports declare: over their abstract stobj."""
    out: set[str] = set()
    for _relative, text in files:
        if "(defabsstobj " not in text:
            continue
        for form, _line in ledger.Reader(text).top_level():
            if ledger.head(form) == "defabsstobj":
                exports = ledger.keyword_plist(form[2:]).get(":exports") or []
                out |= {_s(e[0]) if isinstance(e, list) and e else _s(e) for e in exports}
    return out


def judge(rows: list[dict], entries: list[str], source,
          functions=frozenset()) -> tuple[list[str], list[str]]:
    """(findings, undecided) for the def-carried ROWS over the declared ENTRIES."""
    findings: list[str] = []
    undecided: list[str] = []
    for row in rows:
        st = invariant_stobj(source, row["invariant"]) if row["invariant"] else None
        if st is None:
            continue                         # a value row says :complete-by
        inf = Inference(source, st, functions)
        listed = set(row["established"]) | set(row["transitions"])
        owed = set(row["owed"])
        escape = row["assumption"]
        for name in sorted(listed & owed):
            findings.append(
                "{}: {} is owed under {} and also a transition or establishing point of {}: "
                "its theorem is proved, so remove it from the owed list".format(
                    row["where"], name, (escape or "").upper(), row["name"]))
        for name in row["owed"]:
            verdict = inf.returns(name) if name in source.definitions else False
            if verdict is False:
                findings.append(
                    "{}: {} is owed under {} by {} but is no function returning the carried "
                    "state {} in this world: a stale owed name; remove it".format(
                        row["where"], name, (escape or "").upper(), row["name"], st))
            elif verdict is None:
                undecided.append("{} (owed, row {})".format(name, row["name"]))
        missing = []
        for name in entries:
            if name in listed or name in owed:
                continue
            verdict = inf.returns(name)
            if verdict is True:
                missing.append(name)
            elif verdict is None:
                undecided.append("{} (entry, row {})".format(name, row["name"]))
        for name in missing:
            findings.append(
                "{}: host-called entry {} (fn-interfaces) returns the carried state {} and is "
                "neither a transition nor an establishing point of {}{}: its preservation "
                "theorem is owed".format(
                    row["where"], name, st, row["name"],
                    ", nor owed under {}".format(escape.upper()) if escape else ""))
    return findings, undecided


def findings(decls: list[dict], kinds_module=interface_kinds,
             root: Path = ROOT) -> tuple[list[str], list[str]]:
    """(findings, undecided) of the tree's rows that some declaration's
    :raw-with (:carried NAME) names: definterface re-checks exactly those in
    the image world (def-carried-check).  A pilot row certified in a book,
    where no entry is declared, meets no table and is outside the rule."""
    files = kinds_module.tree_files()
    source = kinds_module.read_source(files)
    named = {d["raw_with_carried"] for d in decls if d.get("raw_with_carried")}
    rows = [r for r in row_forms(root) if r["name"] in named]
    return judge(rows, [d["name"] for d in decls], source, stobj_functions(files))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    from tools import interface_emit
    problems, undecided = findings(interface_emit.declarations())
    print("carried_entries: {} finding(s), {} undecided".format(len(problems), len(undecided)))
    for line in problems:
        print("  " + line)
    for line in sorted(set(undecided)):
        print("  undecided " + line)
    return 1 if (args.check and problems) else 0


if __name__ == "__main__":
    raise SystemExit(main())
