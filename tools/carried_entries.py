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

A-PINS-FRAMED uses that same enumeration, before any carried-row exemptions:
    python3 tools/carried_entries.py --frame fn-owner-pins-carried --write
    python3 tools/carried_entries.py --frame fn-owner-pins-carried --check
The generated planning/pins-framed-escape.json admits only entries with no
may-write path to the invariant's three globals. Unknown ACL2 calls/macros
handed state, unread raw code, computed globals and state replacement cannot
escape. Evidence gives a
call path to the definition containing the write or fail-closed operation.
"""
from __future__ import annotations

import argparse
from collections import deque
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402
from tools import interface_kinds  # noqa: E402
from tools import lisp_source, owner_globals_check  # noqa: E402

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
        missing, unknown = state_entries([n for n in entries if n not in listed | owed],
                                         source, inference=inf)
        undecided.extend("{} (entry, row {})".format(name, row["name"]) for name in unknown)
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


FRAME_GLOBALS = ("fn-owner", "fn-owner-conn-pins", "fn-owner-store-profile")
FRAME_FILE = "planning/pins-framed-escape.json"
# ACL2 state is a distinct stobj: an unread ACL2 call without the variable
# state among its arguments cannot write state globals. Raw Lisp has no such
# restriction; its unread calls remain closed, even without an explicit state.
FRAME_STATE_READ_ONLY = {
    "f-get-global": "reads a named entry of the state global table",
    "get-global": "reads a named entry of the state global table",
    "f-boundp-global": "tests membership in the state global table",
    "boundp-global": "tests membership in the state global table",
    "@": "ACL2 global-table lookup macro; expands to f-get-global",
    "state-p": "recognizes a state without changing it",
    "state-p1": "recognizes the state representation without changing it",
    "global-table": "selects the state global-table field",
    "w": "reads current-acl2-world from the state global table",
}
# Known pure primitives are also safe in raw code, where the ACL2 argument
# rule cannot establish that an unread function is harmless.
FRAME_PURE = PURE_HEADS - {"ec-call", "declare", "the"}
FRAME_PURE |= {"cadr", "caddr", "cadddr", "cddr", "cdddr", "cddddr", "caar", "cdar",
               "nthcdr", "reverse", "revappend", "assoc-equal", "assoc-eq", "member-equal",
               "member-eq", "remove-equal", "no-duplicatesp-equal", "strip-cars", "strip-cdrs",
               "symbol-name", "symbol-package-name", "intern-in-package-of-symbol",
               "acl2-numberp", "rationalp", "booleanp", "bitp", "unsigned-byte-p",
               "characterp", "char-code", "code-char", "coerce", "max", "min", "abs",
               "numerator", "denominator", "lognot", "logxor", "logbitp", "expt",
               "string-equal", "string=", "char", "char=", "subseq", "concatenate",
               "state-p1", "global-table", "w", "fboundp", "boundp"}
FRAME_WRITERS = {"f-put-global", "put-global", "set-global", "makunbound-global", "assign"}
FRAME_RESTORES = {"update-global-table", "update-state", "restore-state", "set-state",
                  "replace-state", "read-state", "load-state"}
# These state primitives affect channels/oracle/timers, not the three globals.
# Printing/configuration/system-call primitives deliberately remain unknown.
FRAME_STATE_PRIMS = {"princ$", "newline", "close-input-channel", "close-output-channel",
                     "write-byte$", "write-char$", "open-input-channel", "open-output-channel",
                     "read-byte$", "read-char$", "read-object", "read-acl2-oracle",
                     "update-acl2-oracle", "value", "value-triple"}


def state_entries(entries, source, functions=frozenset(), inference=None):
    """The same source stobjs-out inference used by def-carried completeness."""
    inf = inference or Inference(source, "state", functions)
    verdicts = {name: inf.returns(name) for name in dict.fromkeys(entries)}
    return ([n for n, v in verdicts.items() if v is True],
            [n for n, v in verdicts.items() if v is None])


def _node_head(node):
    if (isinstance(node, lisp_source.List) and node.items
            and isinstance(node.items[0], lisp_source.Atom) and not node.items[0].marks):
        return _acl2_symbol(node.items[0].text)
    return ""


def _acl2_symbol(name):
    name = name.lower()
    for prefix in ("acl2::", "acl2:"):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


class FrameAnalysis:
    """Conservative may-write graph, with all source variants of a definition.

    No evaluation, reader invocation or speculative macro expansion. Unknown
    ACL2 code handed state, raw code, dynamic calls and state replacement
    write every protected global when their effects cannot be read.
    The positioned reader and quoted-global recognition are the owner-global
    scanner's, including raw Lisp. Generated ACL2 definitions use the existing
    ledger expansions, rather than a second implementation of the generators.
    """

    def __init__(self, files, source, globals, raw_paths=frozenset()):
        self.globals = tuple(sorted(globals))
        self.source = source
        self.definitions = {}
        self.macros = set(source.macros)
        self.abstract = set()
        self.attachments = {}
        self.direct = {}
        for relative, text in files:
            line_of = lisp_source.line_numberer(text)

            def visit(node):
                if node.marks:
                    return
                head = _node_head(node)
                if head in interface_kinds.DEFUN_HEADS and len(node.items) >= 4:
                    name = node.items[1]
                    if isinstance(name, lisp_source.Atom) and not name.marks:
                        self.definitions.setdefault(_acl2_symbol(name.text), []).append(
                            (f"{relative}:{line_of(node.start)}", node.items[3:], relative in raw_paths))
                elif head == "defmacro" and len(node.items) > 1:
                    self.macros.add(_acl2_symbol(node.items[1].text))
                elif head == "defattach":
                    pairs = node.items[1:]
                    if (len(pairs) >= 2 and isinstance(pairs[0], lisp_source.Atom)
                            and isinstance(pairs[1], lisp_source.Atom)):
                        self.attachments.setdefault(_acl2_symbol(pairs[0].text), set()).add(
                            _acl2_symbol(pairs[1].text))
                    else:
                        for pair in pairs:
                            if (isinstance(pair, lisp_source.List) and len(pair.items) >= 2
                                    and all(isinstance(x, lisp_source.Atom) for x in pair.items[:2])):
                                self.attachments.setdefault(_acl2_symbol(pair.items[0].text), set()).add(
                                    _acl2_symbol(pair.items[1].text))
                elif head in {*interface_kinds.NESTING, "eval-when", "progn!"}:
                    if head == "encapsulate" and len(node.items) > 1:
                        signatures = node.items[1]
                        if isinstance(signatures, lisp_source.List):
                            for signature in signatures.items:
                                name = _node_head(signature)
                                if (not name and isinstance(signature, lisp_source.List)
                                        and signature.items):
                                    name = _node_head(signature.items[0])  # ((FN ...) => ...)
                                if name:
                                    self.abstract.add(name)
                    for child in node.items[1:]:
                        if isinstance(child, lisp_source.List):
                            visit(child)

            for node in lisp_source.read_all(text, strict=True):
                if isinstance(node, lisp_source.List):
                    visit(node)
        # Source expands def-loop/def-representation/def-buffer etc. An actual
        # raw definition is always retained alongside an ACL2 definition.
        for name, definition in source.definitions.items():
            if name not in self.definitions:
                bodies = ledger.source_text([Sym("progn"), *_bodies(definition)])
                self.definitions[name] = [(definition.where, lisp_source.read_all(bodies), False)]

    def function(self, name):
        if name in self.direct:
            return self.direct[name]
        effects, edges = [], set(self.attachments.get(name, ()))
        raw = False  # set for each source variant, including raw replacements

        def handed_state(args):
            # Exactly Inference.term's unread-call decidability rule. Other
            # stobjs (fn-arena, fn-hist, ...) are not ACL2 state. Argument
            # expressions are still walked, including their nested writers.
            return any(isinstance(arg, lisp_source.Atom) and not arg.marks
                       and _acl2_symbol(arg.text) == "state" for arg in args)

        def effect(reason, where, globals=None):
            effects.append({"globals": list(self.globals if globals is None else globals),
                            "reason": reason, "where": where})

        def global_write(arg, where, head):
            name = owner_globals_check.quoted_symbol(arg) if arg is not None else ""
            name = _acl2_symbol(name)
            if not name or "|" in name or "\\" in name:
                effect(f"fail-closed: computed global name in {head}", where)
            elif name in self.globals:
                effect(f"write {name} via {head}", where, [name])

        def walk(node, where):
            if isinstance(node, lisp_source.Str):
                return
            if node.marks:
                if any(m in node.marks for m in ("`", ",", ",@", "#.")):
                    effect("fail-closed: unexpanded reader/macro form", where)
                return
            if (raw and isinstance(node, lisp_source.Atom)
                    and _acl2_symbol(node.text) == "*the-live-state*"):
                effect("fail-closed: raw reference to *the-live-state*", where)
            if not isinstance(node, lisp_source.List) or not node.items:
                return
            head = _node_head(node)
            args = node.items[1:]
            if head in {"quote", "function", "declare"}:
                return
            if head in {"let", "let*"} and args and isinstance(args[0], lisp_source.List):
                for binding in args[0].items:
                    if isinstance(binding, lisp_source.List) and binding.items:
                        variable = binding.items[0]
                        value = binding.items[1] if len(binding.items) > 1 else None
                        if (isinstance(variable, lisp_source.Atom)
                                and variable.text.lower() in {"state", "*the-live-state*"}
                                and not self.state_value(value)):
                            effect("fail-closed: wholesale state binding/replacement", where)
                        if value is not None:
                            walk(value, where)
                for body in args[1:]:
                    walk(body, where)
                return
            if head in {"mv-let", "mv?-let", "multiple-value-bind"} and len(args) >= 3:
                # The first argument is a binding list, never a call.
                if isinstance(args[0], lisp_source.List):
                    value_head = _node_head(args[1])
                    sig = (Inference(self.source).function(value_head)
                           if value_head in self.source.definitions else PRIMS.get(value_head))
                    for i, variable in enumerate(args[0].items):
                        if (isinstance(variable, lisp_source.Atom)
                                and _acl2_symbol(variable.text) in {"state", "*the-live-state*"}):
                            safe = (self.state_value(args[1].items[i + 1])
                                    if value_head == "mv" and len(args[1].items) > i + 1
                                    else isinstance(sig, tuple) and len(sig) > i and sig[i])
                            if not safe:
                                effect("fail-closed: wholesale state output binding/replacement", where)
                walk(args[1], where)
                for body in args[2:]:
                    walk(body, where)
                return
            if head == "cond":
                for clause in args:
                    if isinstance(clause, lisp_source.List):
                        for term in clause.items:
                            walk(term, where)
                return
            if head in {"case", "typecase"} and args:
                walk(args[0], where)
                for clause in args[1:]:
                    if isinstance(clause, lisp_source.List):
                        for term in clause.items[1:]:
                            walk(term, where)
                return
            if head in FRAME_WRITERS:
                global_write(args[0] if args else None, where, head)
                if raw:
                    effect(f"fail-closed: raw global setter {head}", where)
            elif head in FRAME_RESTORES:
                effect(f"fail-closed: wholesale state restore/replacement via {head}", where)
            elif head in {"setf", "setq", "psetf", "psetq"}:
                for i in range(0, len(args), 2):
                    place = args[i]
                    if isinstance(place, lisp_source.Atom):
                        if place.text.lower() in {"state", "*the-live-state*"}:
                            effect("fail-closed: wholesale state restore/replacement", where)
                    elif _node_head(place).endswith("-global"):
                        global_write(place.items[1] if len(place.items) > 1 else None, where, head)
                        if raw:
                            effect("fail-closed: raw global setter via generalized assignment", where)
                        for argument in place.items[1:]:
                            walk(argument, where)
                    else:
                        effect("fail-closed: unread generalized assignment", where)
                    if i + 1 < len(args):
                        walk(args[i + 1], where)
                return
            elif head in {"funcall", "apply"}:
                target = args[0] if args else None
                literal = owner_globals_check.quoted_symbol(target)
                if (isinstance(target, lisp_source.Atom) and target.marks == ("#'",)):
                    literal = target.text.lower()
                if (_node_head(target) == "function" and len(target.items) == 2
                        and isinstance(target.items[1], lisp_source.Atom)):
                    literal = target.items[1].text.lower()
                if literal:
                    literal = _acl2_symbol(literal)
                    if (literal in self.definitions or literal in self.attachments
                            or raw or head == "apply" or handed_state(args[1:])):
                        edges.add(literal)
                else:
                    effect(f"fail-closed: non-literal {head}", where)
                for arg in args[1:]:
                    walk(arg, where)
                return
            elif head in {"if", "and", "or", "when", "unless", "mv", "progn", "pprogn",
                          "prog2$", "progn$", "ec-call", "the", "mbe"}:
                pass                        # inspect every executable arm
            elif head in self.macros:
                if raw or handed_state(args):
                    effect(f"fail-closed: unexpanded macro {head}", where)
            elif head in self.definitions:
                if (head not in self.abstract or head in self.attachments or raw
                        or handed_state(args) or any(v[2] for v in self.definitions[head])):
                    edges.add(head)
            elif head in FRAME_STATE_READ_ONLY or head in FRAME_STATE_PRIMS:
                pass
            elif not raw and not handed_state(args):
                pass                        # ACL2 call cannot access state globals
            elif head in FRAME_PURE:
                pass                        # audited pure primitive in raw code
            else:
                effect(f"fail-closed: unread function {head or '<computed call>'}", where)
            for arg in args:
                walk(arg, where)

        variants = self.definitions.get(name)
        if (name in self.abstract and name not in self.attachments
                and not any(v[2] for v in variants or ())):
            effect(f"fail-closed: abstract function {name} has no readable attachment",
                   "encapsulate (local witness is not runtime code)")
        if variants is None:
            if name not in FRAME_PURE and name not in FRAME_STATE_READ_ONLY and name not in FRAME_STATE_PRIMS:
                effect(f"fail-closed: unread function {name}", "no definition in tree")
        else:
            for where, bodies, raw in variants:
                for body in bodies:
                    walk(body, where)
        self.direct[name] = (effects, sorted(edges))
        return self.direct[name]

    def state_value(self, value):
        """Only an unchanged state or a known state-returning call can rebind it."""
        if isinstance(value, lisp_source.Atom):
            return not value.marks and value.text.lower() in {"state", "*the-live-state*"}
        head = _node_head(value)
        if head in FRAME_WRITERS or head in FRAME_RESTORES:
            return True                     # its effects are checked separately
        sig = Inference(self.source).function(head) if head in self.source.definitions else PRIMS.get(head)
        return isinstance(sig, tuple) and sig == (True,)

    def writes(self, name):
        """Shortest witness per effect class/global; cycles terminate by name.

        Visit the whole reachable graph: a fail-closed witness must not hide
        real writes or other fail-closed classes needed by the row report.
        """
        pending = deque([(name, [name])])
        visited, witnesses = set(), {}
        while pending:
            callee, path = pending.popleft()
            if callee in visited:
                continue
            visited.add(callee)
            effects, edges = self.function(callee)
            for effect in effects:
                for global_name in effect["globals"]:
                    witnesses.setdefault((global_name, frame_reason_class(effect["reason"])),
                                         {**effect, "call_path": path})
            pending.extend((edge, [*path, edge]) for edge in edges if edge not in visited)
        evidence = []
        for key in sorted(witnesses):
            witness = witnesses[key]
            if witness not in evidence:
                evidence.append(witness)
        return sorted({g for g, _ in witnesses}), evidence


def frame_reason_class(reason):
    """Stable classes for generated witnesses and the grouped needs-row report."""
    if reason.startswith("write "):
        return "real-write"
    for prefix, kind in (
        ("UNDECIDED", "UNDECIDED"), ("unread function", "unread-function"),
        ("computed global", "computed-global"), ("wholesale state", "wholesale-state"),
        ("unexpanded", "unexpanded-macro"), ("raw reference", "raw-live-state"),
        ("raw global setter", "raw-global-setter"), ("abstract function", "abstract-function"),
        ("non-literal", "dynamic-call"), ("unread generalized", "unread-assignment"),
    ):
        if reason.startswith("fail-closed: " + prefix):
            return kind
    raise ValueError("unclassified frame reason: " + reason)


def frame_register(root=ROOT, row="fn-owner-pins-carried", globals=FRAME_GLOBALS):
    from tools import interface_emit
    files = [(p.relative_to(root).as_posix(), p.read_text(encoding="utf-8"))
             for directory in ("books", "host") for p in sorted((root / directory).rglob("*.lisp"))]
    # Real-tree enumeration uses precisely the existing completeness inputs.
    # Fixture trees have no build inventory; their non-native source is explicit.
    logical = (interface_kinds.tree_files() if root.resolve() == ROOT.resolve()
               else [(p, t) for p, t in files if not p.startswith("host/native/")])
    source = interface_kinds.read_source(logical)
    decls = interface_emit.declarations(root)
    returned, undecided = state_entries([d["name"] for d in decls], source, stobj_functions(logical))
    returned, undecided = sorted(returned), sorted(undecided)
    raw_paths = {p for p, _ in files} - {p for p, _ in logical}
    analysis = FrameAnalysis(files, source, globals, raw_paths)
    escaped, needs = [], []
    for name in returned:
        writes, evidence = analysis.writes(name)
        if writes:
            needs.append({"name": name, "writes": writes, "evidence": evidence})
        else:
            escaped.append(name)
    # An undecidable return is never eligible for this escape.
    for name in undecided:
        needs.append({"name": name, "writes": sorted(globals), "evidence": [{
            "globals": sorted(globals), "reason": "fail-closed: UNDECIDED state return",
            "where": source.definitions[name].where if name in source.definitions else "no definition in tree",
            "call_path": [name]}]})
    return {"_header": "GENERATED by tools/carried_entries.py --frame fn-owner-pins-carried --write; NEVER hand-edit.",
            "row": row, "escape": "A-PINS-FRAMED", "globals": sorted(globals),
            "counts": {"entries_enumerated": len(returned), "escaped": len(escaped),
                       "needs_proved_row": len(needs), "UNDECIDED": len(undecided),
                       "declared_entries": len(set(d["name"] for d in decls))},
            "escaped": escaped, "needs_proved_row": sorted(needs, key=lambda e: e["name"]),
            "UNDECIDED": undecided}


def check_frame(register, path):
    expected = json.dumps(register, indent=2, sort_keys=True) + "\n"
    stored = path.read_text(encoding="utf-8") if path.exists() else ""
    if expected == stored:
        return 0
    print(f"carried_entries frame: stale generated register {path}; regenerate with --write")
    try:
        old = json.loads(stored)
    except ValueError:
        old = {}

    def entries(data):
        return {**{n: "ESCAPED" for n in data.get("escaped", [])},
                **{e["name"]: e for e in data.get("needs_proved_row", [])}}

    before, after = entries(old), entries(register)
    for name in sorted(before.keys() | after.keys()):
        if before.get(name) != after.get(name):
            def status(entry):
                return entry if isinstance(entry, str) else "needs-proved-row" if entry else "absent"
            print(f"  {name}: {status(before.get(name))} -> {status(after.get(name))} (classification/evidence changed)")
    return 1


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true", help="regenerate the frame escape register")
    parser.add_argument("--frame", choices=["fn-owner-pins-carried"])
    parser.add_argument("--globals", default=",".join(FRAME_GLOBALS))
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    if args.frame:
        globals = tuple(sorted(set(args.globals.lower().split(","))))
        if globals != tuple(sorted(FRAME_GLOBALS)):
            parser.error("fn-owner-pins-carried requires exactly " + ",".join(FRAME_GLOBALS))
        register = frame_register(args.root, args.frame, globals)
        print("carried_entries frame: " + json.dumps(register["counts"], sort_keys=True))
        path = args.root / FRAME_FILE
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(register, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return check_frame(register, path) if args.check else 0
    if args.write:
        parser.error("--write requires --frame")
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
