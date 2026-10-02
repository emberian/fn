#!/usr/bin/env python3
"""The raw host reaches a book function only through the dispatcher.

D40 lets the host run a carried entry's raw definition because every way
into it is known: the dispatcher resolves a QUOTED entry name against the
generated `fn-interfaces' table (host/native/io.lisp fnn-dispatch-function,
fnn-fixed-raw-callback), and a def-carried open whose premise is produced
(:produced) is never such an entry.  Codex review r28 (F1) found the hole:
`(funcall 'F ...)', `(apply #'F ...)', a symbol held in a variable, a
symbol built by `intern' -- each reaches F with no table and no lint.  This
rule closes it BY CONSTRUCTION over the raw-loaded host files
(tools/ledger.py raw_host_paths): it does not chase where a book symbol
could flow, it refuses every way one could be made.

NAME   A book function's symbol occurs -- quoted, `#'', inside quoted data
       or as a backquote template's head -- only as the name argument of a
       dispatcher: a base dispatcher below, or a raw function or macro whose
       parameter reaches a dispatcher's name position (derived, to a
       fixpoint, from the source; `(apply #'D 'F ...)' counts).
NAMEVAR A dispatcher's name argument is a quoted literal, unless it is the
       enclosing dispatcher's own name parameter passed through.
MAKE   No symbol is made or looked up at run time: intern, find-symbol,
       read, read-from-string, find-all-symbols, do-symbols, ... (a literal
       KEYWORD package is allowed: a keyword is never a function).
WORLD  No world, property-list or function-cell read: w, table-alist,
       getpropc, getprop, fgetprop, global-val, symbol-function, fdefinition,
       macro-function, symbol-value, symbol-plist, get, eval, compile,
       coerce to 'function -- except symbol-function/fdefinition of a quoted
       raw (non-book) name.
CALL   Every function position (funcall / apply / multiple-value-call, the
       CL higher-order functions' function argument, every :key / :test /
       :test-not) holds a value TRACED to a host function: #'G or 'G with G
       no book function, a lambda, a table resolution (fnn-fixed-raw-callback
       / fnn-dispatch-function of a literal), or a variable, special, struct
       slot or raw function result every one of whose sources is such.  An
       ACL2 value is never a function object, so a value the host cannot
       trace -- a dispatched result, an opaque binding -- is refused, which
       leaves no route from ACL2 data to a call.

Each site outside the rule is either ALLOWED below (a dispatcher internal or
a fixed reference, with its reason: the allow-list never covers a def-carried
function, checked) or PENDING (a host rewrite to a quoted dispatch, waiting
on stage 0: MODE-2026-10-01 §2 forbids served-path host edits before it).
An allow or pending entry that matches no site is itself a finding.

    python3 tools/raw_dispatch_rule.py           # report
    python3 tools/raw_dispatch_rule.py --check   # exit 1 on any finding
(`tools/interface_emit.py --check' runs it: the runner's fast checks.)
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

Sym = ledger.Sym

# The base dispatchers: head -> the argument positions holding an entry
# name.  fnn-call resolves through fnn-dispatch-function (the table, else
# the executable counterpart of a definterface-declared name: interface_emit
# refuses an undeclared dispatched name); fnn-fixed-raw-callback resolves
# only a :raw-with entry of the table; fnn-fixed-callback-fail only names
# the entry in a fault.  Every other dispatcher is derived from these.
BASE_DISPATCHERS = {
    "fnn-call": (0,), "fnn-dispatch-function": (0,), "fnn-fixed-raw-callback": (0,),
    "fnn-fixed-callback-fail": (0,), "fnn-counterpart": (0,),
    "fnn-entry-guard": (0,), "fnn-entry-guard-spec": (0,), "fnn-trailing-kind": (0,),
}
# The positions that only NAME an entry (a fault's subject), never resolve it:
# a literal there need not be a declared entry.
LABELS = {("fnn-fixed-callback-fail", 0)}
# Positions where a quoted symbol is compared or looked up and never escapes
# as a value: a book function's name there names nothing callable.
KEY_POSITIONS = {"assoc": (0,), "rassoc": (0,), "member": (0,), "gethash": (0,),
                 "getf": (1,), "find": (0,), "position": (0,), "eq": (0, 1),
                 "eql": (0, 1), "equal": (0, 1), "fboundp": (0,), "remove": (0,),
                 "fnn-global": (0,), "f-get-global": (0,), "boundp": (0,)}
# Where a value is only printed: a book symbol there labels a message.
LABEL_SINKS = {"format": 1, "fnn-fault": 0, "fnn-refuse": 0, "error": 1, "fnn-out": 0,
               "warn": 0, "cerror": 1, "fnn-fixed-callback-fail": 0}

# The table resolutions: their value is the entry's function object.
RESOLVERS = {"fnn-fixed-raw-callback", "fnn-dispatch-function"}

MAKERS = {"intern", "find-symbol", "read", "read-from-string",
          "read-preserving-whitespace", "find-all-symbols", "do-symbols",
          "do-all-symbols", "do-external-symbols", "with-package-iterator",
          "apropos", "apropos-list", "make-symbol", "gentemp", "gensym-symbol",
          "unintern", "import", "shadowing-import"}
WORLD = {"w", "table-alist", "getpropc", "getprop", "fgetprop", "global-val",
         "symbol-function", "fdefinition", "macro-function", "symbol-value",
         "symbol-plist", "get", "eval", "compile", "f-get-global", "get-global",
         "function-lambda-expression", "sb-int:encapsulate", "sb-int:unencapsulate",
         "trace", "untrace", "sb-profile:profile", "sb-profile:unprofile",
         "fmakunbound", "sb-impl::%defun", "set-symbol-function"}
HOF1 = {"mapcar", "mapc", "mapcan", "mapcon", "maplist", "mapl", "reduce",
        "remove-if", "remove-if-not", "delete-if", "delete-if-not", "find-if",
        "find-if-not", "position-if", "position-if-not", "count-if",
        "count-if-not", "member-if", "member-if-not", "assoc-if", "assoc-if-not",
        "rassoc-if", "rassoc-if-not", "some", "every", "notany", "notevery",
        "funcall", "apply", "multiple-value-call", "sb-thread:make-thread",
        "subst-if", "subst-if-not", "nsubst-if", "sb-ext:make-timer",
        "sb-int:encapsulate"}
HOF2 = {"map", "map-into", "sort", "stable-sort", "merge", "sb-ext:finalize"}
FN_KEYS = {":key", ":test", ":test-not"}
# The functions whose :key / :test / :test-not is a function position.
KEYED = {"member", "assoc", "rassoc", "find", "position", "count", "remove", "delete",
         "sort", "stable-sort", "search", "mismatch", "remove-duplicates",
         "delete-duplicates", "union", "intersection", "set-difference", "subsetp",
         "adjoin", "pushnew", "substitute", "nsubstitute", "merge", "reduce",
         "find-if", "position-if", "count-if", "remove-if", "remove-if-not",
         "delete-if", "member-if", "assoc-if", "rassoc-if", "nunion",
         "nintersection", "nset-difference", "set-exclusive-or", "tree-equal",
         "sublis", "subst", "nsubst"}
OPAQUE = {"declare", "declaim", "in-package", "defpackage", "define-condition",
          "deftype", "defsetf", "defconstant"}
# A value built of traced values is traced; a part selected from a traced
# container is traced (the container argument's index).
CONSTRUCT = {"list", "list*", "cons", "append", "vector", "acons", "make-hash-table"}
SELECT = {"car": 0, "cdr": 0, "first": 0, "second": 0, "third": 0, "fourth": 0,
          "fifth": 0, "rest": 0, "last": 0, "cadr": 0, "cddr": 0, "caar": 0,
          "cdar": 0, "nth": 1, "elt": 0, "aref": 0, "svref": 0, "gethash": 1,
          "assoc": 1, "rassoc": 1, "find": 1, "getf": 0, "member": 1,
          "nthcdr": 1, "copy-list": 0, "reverse": 0, "remove": 1, "delete": 1,
          "remove-if": 1, "remove-if-not": 1, "subseq": 0, "sort": 0,
          "stable-sort": 0, "butlast": 0}
# Functions whose value is never a symbol or function: numbers, strings,
# booleans, characters, octet vectors, OS objects (sockets, threads, mutexes).
NONFUNCTION = {"error", "+", "-", "*", "/", "1+", "1-", "length", "format", "concatenate",
               "string=", "string-equal", "eq", "eql", "equal", "equalp", "=", "<",
               ">", "<=", ">=", "/=", "not", "null", "zerop", "plusp", "minusp",
               "min", "max", "floor", "ceiling", "truncate", "round", "mod", "rem",
               "ash", "logand", "logior", "logxor", "lognot", "integer-length",
               "princ-to-string", "prin1-to-string", "string", "string-downcase",
               "string-upcase", "parse-integer", "char", "code-char", "char-code",
               "make-string", "make-array", "get-internal-real-time",
               "get-universal-time", "consp", "listp", "symbolp", "stringp",
               "integerp", "functionp", "numberp", "characterp", "vectorp",
               "make-condition", "open", "probe-file", "namestring", "pathname"}
NONFUNCTION_PACKAGES = ("sb-bsd-sockets:", "sb-unix:", "sb-posix:", "sb-alien:",
                        "sb-sys:", "sb-thread:make-", "sb-thread:join-thread")
BINDERS_OPAQUE = {"multiple-value-bind", "destructuring-bind", "dolist", "dotimes",
                  "do", "do*", "handler-case", "restart-case", "loop"}


DEBUG = None


@dataclass(frozen=True)
class Site:
    rule: str
    file: str
    context: str
    line: int
    detail: str
    symbols: frozenset = frozenset()


@dataclass
class Allow:
    rule: str
    file: str
    context: str
    reason: str
    pending: bool = False


# ---------------------------------------------------------------------------
# The sites outside the rule, each with its reason.  ALLOWED: the
# dispatcher's own internals and fixed references.  PENDING: a rewrite to a
# quoted dispatch owed after stage 0 (no served-path host edit before it).

INTERNAL = "dispatcher internal: resolves an entry name against the generated table"
DIGEST = ("the BLAKE3 reference/native pair (host/native/digest.lisp): the ACL2 "
          "definitions of these digest functions are captured once and the native "
          "accelerator installed over them; fnn-digest-check compares the two -- a "
          "fixed list, no entry of the table, never a def-carried function (checked)")
LOOKUPS = ("developer lookup counters, FN_NATIVE_COUNT_LOOKUPS only (fnn-developer-"
           "selector; a production image refuses to start with it set): "
           "sb-int:encapsulate wraps each listed read function to count its calls")
ALLOW: list[Allow] = [
    Allow("WORLD", "host/native/io.lisp", "fnn-install-raw-dispatch",
          INTERNAL + " (reads fn-interfaces off the world once, at image build)"),
    Allow("WORLD", "host/native/io.lisp", "fnn-entry-guard-spec",
          INTERNAL + " (reads the entry's formals, stobjs-in and guard, cached)"),
    Allow("WORLD", "host/native/io.lisp", "fnn-trailing-kind",
          INTERNAL + " (reads the entry's stobjs-in, cached)"),
    Allow("WORLD", "host/native/io.lisp", "fnn-fixed-raw-callback",
          INTERNAL + " (the compiled function of a :raw-with entry the table resolved)"),
    Allow("MAKE", "host/native/io.lisp", "fnn-counterpart",
          INTERNAL + " (find-symbol of the entry's *1* counterpart in ACL2_*1*_ACL2)"),
    Allow("CALL", "host/native/io.lisp", "fnn-entry-guard",
          INTERNAL + " (funcalls a kind recognizer of *fn-entry-guard-kinds*, "
          "books/payload-kinds.lisp: guard-t, linear, read off the entry's guard)"),
    Allow("NAMEVAR", "host/native/io.lisp", "fnn-cold-guard-cache-prepare",
          INTERNAL + " (reads the guard spec of each name of ACL2's fixed cold roster "
          "fn-cgb-roster; calls nothing)"),
    Allow("WORLD", "host/native/io.lisp", "fnn-global",
          "reads an ACL2 state global by name (f-get-global); a value read is data, "
          "and CALL refuses any value that reaches a function position untraced"),
    Allow("WORLD", "host/native/io.lisp", "fnn-developer-selector-gate",
          "sb-int:encapsulate of the SBCL condition sb-kernel::control-stack-exhausted-error "
          "only (fnn-stack-exhaustion-report): no book function"),
    Allow("NAME", "host/native/digest.lisp", "*fnn-digest-entries*", DIGEST),
    Allow("NAME", "host/native/digest.lisp", "*fnn-digest-natives*", DIGEST),
    Allow("CALL", "host/native/digest.lisp", "fnn-digest-capture-references", DIGEST),
    Allow("WORLD", "host/native/digest.lisp", "fnn-digest-capture-references", DIGEST),
    Allow("WORLD", "host/native/digest.lisp", "fnn-digest-install-natives", DIGEST),
    Allow("WORLD", "host/native/digest.lisp", "fnn-digest-restore-references", DIGEST),
    Allow("NAME", "host/native/digest.lisp", "fnn-b3-reference-range", DIGEST),
    Allow("NAME", "host/native/digest.lisp", "fnn-b3-reference-list", DIGEST),
    Allow("NAME", "host/native/digest.lisp", "fnn-blake3-list-native", DIGEST),
    Allow("NAME", "host/native/digest.lisp", "fnn-blake3-prefixed-range-native", DIGEST),
    Allow("NAME", "host/native/digest.lisp", "fnn-blake3-prefixed-buffer-native", DIGEST),
    Allow("NAME", "host/native/io.lisp", "+fnn-lookup-functions+", LOOKUPS),
    Allow("CALL", "host/native/io.lisp", "fnn-install-lookup-counters", LOOKUPS),
    Allow("MAKE", "host/native/io.lisp", "fnn-install-lookup-counters", LOOKUPS),
    Allow("WORLD", "host/native/io.lisp", "fnn-install-lookup-counters", LOOKUPS),
    Allow("CALL", "host/native/io.lisp", "fnn-lookup-counter", LOOKUPS),
    Allow("CALL", "host/native/io.lisp", "fnn-lookup-walk-counter", LOOKUPS),
    Allow("MAKE", "host/native/bp.lisp", "fnn-bp-profile-points",
          "developer BP profile, FN_BP_TEST_PROFILE only (a production image refuses it): "
          "names read from +fnn-bp-profile-names+ and the *1* package for sb-profile"),
    Allow("WORLD", "host/native/bp.lisp", "fnn-bp-profile-points",
          "developer BP profile, FN_BP_TEST_PROFILE only: (eval `(sb-profile:profile ...))"),
]

# Rewrites owed after stage 0 (MODE-2026-10-01 section 2: no served-path host
# edit before it lands), each to a quoted dispatch the rule accepts.
STAGE0 = "rewrite after stage 0: "
PENDING: list[Allow] = [
    Allow("MAKE", "host/native/owner.lisp", "fnn-fresh-stobj",
          STAGE0 + "call the creator directly per literal stobj ((create-fn-cat), "
          "(create-fn-hist)) instead of intern + eval", pending=True),
    Allow("WORLD", "host/native/owner.lisp", "fnn-fresh-stobj",
          STAGE0 + "the eval of (CREATOR) goes with the intern", pending=True),
]


def _strip(name: str) -> str:
    for prefix in ("acl2::", "acl2:", "common-lisp-user::", "cl-user::"):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def _head(form) -> str | None:
    return str(form[0]) if isinstance(form, list) and form and isinstance(form[0], Sym) else None


def _quoted_symbol(form) -> str | None:
    if _head(form) in ("quote", "function") and len(form) == 2 and isinstance(form[1], Sym):
        return _strip(str(form[1]))
    return None


def _symbols(data):
    if isinstance(data, list):
        for item in data:
            yield from _symbols(item)
    elif isinstance(data, Sym):
        yield _strip(str(data))


def _lambda_params(formals) -> list[tuple[object, str]]:
    """[(position or keyword, name)] of a lambda list."""
    out = []
    if not isinstance(formals, list):
        return out
    mode, index = "required", 0
    for item in formals:
        text = str(item) if isinstance(item, Sym) else None
        if text and text.startswith("&"):
            mode = text
            continue
        name = item[0] if isinstance(item, list) and item else item
        if isinstance(name, list) and name:  # ((:kw var) default)
            name = name[-1]
        if not isinstance(name, Sym):
            continue
        if mode in ("required", "&optional"):
            out.append((index, str(name)))
            index += 1
        elif mode == "&key":
            out.append((":" + str(name), str(name)))
        elif mode in ("&rest", "&body"):
            out.append(("&rest", str(name)))
    return out


def _detemplate(x):
    """A backquote template read as the code it expands to."""
    if isinstance(x, list) and x:
        h = _head(x)
        if h in ("unquote", "unquote-splicing") and len(x) == 2:
            return x[1]
        return [_detemplate(item) for item in x]
    return x


@dataclass
class Defn:
    name: str
    kind: str
    file: str
    line: int
    params: list
    body: list


@dataclass
class Scan:
    book: set
    raw: dict[str, Defn]
    sites: list[Site] = field(default_factory=list)
    dispatchers: dict[str, set] = field(default_factory=dict)
    resolving: set = field(default_factory=set)    # (head, position) that resolve
    labels: dict = field(default_factory=dict)     # raw function -> label positions
    named: dict = field(default_factory=dict)      # resolved literal -> {file}
    fparams: set = field(default_factory=set)      # (defun, key)
    fspecials: set = field(default_factory=set)
    fslots: set = field(default_factory=set)       # accessor names
    slots: dict[str, tuple] = field(default_factory=dict)  # accessor -> (struct, slot)
    ctors: dict[str, tuple] = field(default_factory=dict)  # ctor -> (struct, boa list|None, conc)


def _definitions(files: dict[str, list]) -> tuple[dict[str, Defn], list]:
    defs: dict[str, Defn] = {}
    tops: list = []  # (file, context, line, form)

    def visit(form, rel, line):
        h = _head(form)
        if h in ("progn", "progn!", "eval-when", "locally"):
            for item in form[1:] if h != "eval-when" else form[2:]:
                visit(item, rel, line)
            return
        if h in ("defun", "defmacro", "defun-inline") and len(form) >= 3 and isinstance(form[1], Sym):
            d = Defn(str(form[1]), h, rel, line, _lambda_params(form[2]), form[3:])
            defs.setdefault(d.name, d)
            tops.append((rel, d.name, line, form))
            return
        if h in ("defvar", "defparameter", "defconstant", "define-condition", "defclass") \
                and len(form) > 1 and isinstance(form[1], Sym):
            ctx = str(form[1])
        elif h:
            ctx = _show(form[:2], 60)
        else:
            ctx = "<top:{}>".format(line)
        if h == "defstruct" and len(form) > 1:
            ctx = str(form[1][0] if isinstance(form[1], list) else form[1])
        tops.append((rel, ctx, line, form))

    for rel, forms in sorted(files.items()):
        for form, line in forms:
            visit(form, rel, line)
    return defs, tops


def _structs(scan: Scan, tops) -> None:
    for _rel, _ctx, _line, form in tops:
        if _head(form) != "defstruct" or len(form) < 2:
            continue
        spec = form[1]
        name = str(spec[0] if isinstance(spec, list) else spec)
        conc, ctors = name + "-", []
        if isinstance(spec, list):
            for option in spec[1:]:
                if isinstance(option, list) and option and str(option[0]) == ":conc-name":
                    conc = str(option[1]) if len(option) > 1 and option[1] not in (None,) else ""
                    if conc == "nil":
                        conc = ""
                if isinstance(option, list) and option and str(option[0]) == ":constructor":
                    if len(option) > 1:
                        ctors.append((str(option[1]), option[2] if len(option) > 2 else None))
        if not ctors:
            ctors = [("make-" + name, None)]
        slot_names = []
        for slot in form[2:]:
            if isinstance(slot, str) and not isinstance(slot, Sym):
                continue  # docstring
            slot_name = slot[0] if isinstance(slot, list) else slot
            if isinstance(slot_name, Sym):
                slot_names.append(str(slot_name))
                scan.slots[conc + str(slot_name)] = (name, str(slot_name))
        for ctor, boa in ctors:
            if ctor != "nil":
                boa_names = ([n for _k, n in _lambda_params(boa)] if boa is not None else None)
                scan.ctors[ctor] = (name, boa_names, conc)


def _dispatchers(scan: Scan) -> None:
    """Base dispatchers plus every raw definition passing a parameter to one."""
    disp = {k: set(v) for k, v in BASE_DISPATCHERS.items()}
    resolving = {(k, p) for k, v in BASE_DISPATCHERS.items() for p in v} - LABELS
    changed = True
    while changed:
        changed = False
        for d in scan.raw.values():
            if d.name in BASE_DISPATCHERS:
                continue
            names = {n: key for key, n in d.params if isinstance(key, int)}
            if not names:
                continue
            found: set = set()
            resolves: set = set()

            def walk(form):
                if not isinstance(form, list) or not form:
                    return
                h = _head(form)
                if h == "quote":
                    return
                if h == "quasiquote":
                    walk(_detemplate(form[1]))
                    return
                args = form[1:]
                target = h
                if h in ("apply", "funcall") and args and _quoted_symbol(args[0]) in disp:
                    target, args = _quoted_symbol(args[0]), args[1:]
                if target in disp:
                    for position in disp[target]:
                        if position < len(args) and isinstance(args[position], Sym) \
                                and str(args[position]) in names:
                            found.add(names[str(args[position])])
                            if (target, position) in resolving:
                                resolves.add(names[str(args[position])])
                for item in form:
                    walk(item)
            for item in d.body:
                walk(item)
            new_resolving = {(d.name, p) for p in resolves}
            if found - disp.get(d.name, set()) or new_resolving - resolving:
                disp.setdefault(d.name, set()).update(found)
                resolving |= new_resolving
                changed = True
    scan.dispatchers = disp
    scan.resolving = resolving


def _passes_name(scan, formals, body, disp) -> set:
    """The positions of FORMALS that BODY passes to a dispatcher's name."""
    names = {n: key for key, n in _lambda_params(formals) if isinstance(key, int)}
    found: set = set()

    def walk(form):
        if not isinstance(form, list) or not form or _head(form) == "quote":
            return
        h, args = _head(form), form[1:]
        if h in ("apply", "funcall") and args and _quoted_symbol(args[0]) in disp:
            h, args = _quoted_symbol(args[0]), args[1:]
        for position in disp.get(h, ()):
            if position < len(args) and isinstance(args[position], Sym) \
                    and str(args[position]) in names:
                found.add(names[str(args[position])])
        for item in form:
            walk(item)
    for item in body or []:
        walk(item)
    return found


def _only_as_name(var: str, body, disp) -> bool:
    """VAR occurs in BODY, and only as a dispatcher's name argument."""
    total = named = 0

    def walk(form):
        nonlocal total, named
        if isinstance(form, Sym):
            total += str(form) == var
            return
        if not isinstance(form, list) or not form or _head(form) == "quote":
            return
        h, args = _head(form), form[1:]
        if h in ("apply", "funcall") and args and _quoted_symbol(args[0]) in disp:
            h, args = _quoted_symbol(args[0]), args[1:]
        for position in disp.get(h, ()):
            if position < len(args) and isinstance(args[position], Sym) \
                    and str(args[position]) == var:
                named += 1
        for item in form:
            walk(item)
    for item in body:
        walk(item)
    return total > 0 and total == named


def _labels(scan: Scan) -> None:
    """Raw definitions' parameters used only as a printed label, to a fixpoint."""
    labels: dict[str, set] = {}
    changed = True
    while changed:
        changed = False
        for d in scan.raw.values():
            for key, name in d.params:
                if not isinstance(key, int) or key in labels.get(d.name, ()):
                    continue
                uses = printed = 0

                def walk(form):
                    nonlocal uses, printed
                    if isinstance(form, Sym):
                        uses += str(form) == name
                        return
                    if not isinstance(form, list) or not form or _head(form) == "quote":
                        return
                    h = _head(form)
                    if h == "quasiquote":
                        walk(_detemplate(form[1]))
                        return
                    for index, item in enumerate(form[1:]):
                        if isinstance(item, Sym) and str(item) == name and (
                                (h in LABEL_SINKS and index >= LABEL_SINKS[h])
                                or index in labels.get(h, ())):
                            printed += 1
                    for item in form:
                        walk(item)
                for item in d.body:
                    walk(item)
                if uses and uses == printed:
                    labels.setdefault(d.name, set()).add(key)
                    changed = True
    scan.labels = labels


def _literal_leaves(arg) -> list | None:
    """The quoted-symbol leaves of a name argument whose every value is a
    quoted literal (a quote, or an if / case / cond over them); else None."""
    if _quoted_symbol(arg) is not None and _head(arg) == "quote":
        return [arg]
    h = _head(arg)
    if h == "if" and len(arg) == 4:
        a, b = _literal_leaves(arg[2]), _literal_leaves(arg[3])
        return a + b if a is not None and b is not None else None
    if h in ("case", "ecase", "cond") and len(arg) > 1:
        out = []
        for clause in arg[2:] if h != "cond" else arg[1:]:
            if not isinstance(clause, list) or len(clause) < 2:
                return None
            leaves = _literal_leaves(clause[-1])
            if leaves is None:
                return None
            out += leaves
        return out
    return None


class Walker:
    """One top-level form's walk: NAME, NAMEVAR, MAKE, WORLD and CALL sites."""

    def __init__(self, scan: Scan, rel: str, ctx: str, line: int, defn: Defn | None):
        self.scan, self.rel, self.ctx, self.line, self.defn = scan, rel, ctx, line, defn
        self.params = {n: key for key, n in (defn.params if defn else [])}
        self.allowed: set[int] = set()     # ids of name literals in dispatcher positions
        self.local_writes: list = []       # (variable, value, env)
        self.fvars: set[str] = set()       # locals reaching a function position
        self.local_calls: list = []        # (local function, args, env)
        self.local_disp: dict = {}         # local function -> its name positions
        self.namevars: set[str] = set()    # let variables holding only literal names
        self.flparams: set = set()         # (local function, key) reaching one

    @property
    def disp(self):
        if not self.local_disp:
            return self.scan.dispatchers
        merged = dict(self.scan.dispatchers)
        merged.update(self.local_disp)
        return merged

    def site(self, rule, detail, symbols=()):
        self.scan.sites.append(Site(rule, self.rel, self.ctx, self.line, detail,
                                    frozenset(symbols)))

    # -- NAME ---------------------------------------------------------------
    def literal(self, form, allowed_positions=False, env=None):
        """A quote/function form not in a dispatcher name position."""
        h = _head(form)
        body = form[1] if len(form) > 1 else None
        if h == "function" and _head(body) == "lambda":
            self.code(body, env or {})
            return
        books = sorted({s for s in _symbols(body) if s in self.scan.book})
        if books and not allowed_positions and id(form) not in self.allowed:
            self.site("NAME", "{} {}".format("#'" if h == "function" else "'", " ".join(books)),
                      books)

    # -- the walk -------------------------------------------------------------
    def code(self, form, env):
        if isinstance(form, Sym) or not isinstance(form, list) or not form:
            return
        h = _head(form)
        if h is None:
            for item in form:
                self.code(item, env)
            return
        if h in OPAQUE:
            return
        if ("#'" + h) in env and h not in self.local_disp:
            # a local function: none of the heads below
            self.local_calls.append((h, form[1:], env))
            for item in form[1:]:
                self.code(item, env)
            return
        if h in ("quote", "function"):
            self.literal(form, env=env)
            return
        # a quoted symbol compared, looked up or printed never escapes as a value
        for index, item in enumerate(form[1:]):
            if _head(item) == "quote" and (
                    index in KEY_POSITIONS.get(h, ())
                    or (h in LABEL_SINKS and index >= LABEL_SINKS[h])
                    or index in self.scan.labels.get(h, ())):
                self.allowed.add(id(item))
        if h == "quasiquote":
            template = _detemplate(form[1])
            # a template's literal symbols become code or data when expanded:
            # a book symbol there is a NAME site unless in a dispatcher position
            self.template(form[1], env)
            return
        if h in ("let", "let*") and len(form) > 1 and isinstance(form[1], list):
            inner = dict(env)
            for i, binding in enumerate(form[1]):
                if isinstance(binding, list) and len(binding) > 1 and isinstance(binding[0], Sym):
                    leaves = _literal_leaves(binding[1])
                    scope = list(form[2:])
                    if h == "let*":
                        scope += [b[1:] for b in form[1][i + 1:] if isinstance(b, list)]
                    if leaves and _only_as_name(str(binding[0]), scope, self.disp):
                        self.allowed.update(id(leaf) for leaf in leaves)
                        self.namevars.add(str(binding[0]))
                        for leaf in leaves:
                            self.scan.named.setdefault(_strip(str(leaf[1])), set()).add(self.rel)
            for binding in form[1]:
                if isinstance(binding, list) and binding:
                    for item in binding[1:]:
                        self.code(item, inner if h == "let*" else env)
                    if isinstance(binding[0], Sym):
                        inner[str(binding[0])] = binding[1] if len(binding) > 1 else Sym("nil")
                        if str(binding[0]).startswith("*"):
                            self.special_write(str(binding[0]), inner[str(binding[0])],
                                               inner if h == "let*" else env)
                elif isinstance(binding, Sym):
                    inner[str(binding)] = Sym("nil")
            for item in form[2:]:
                self.code(item, inner)
            return
        if h in BINDERS_OPAQUE:
            inner = dict(env)
            spec = form[1] if len(form) > 1 else None
            if h in ("multiple-value-bind", "destructuring-bind"):
                for var in _symbols(spec):
                    inner[var] = None  # opaque
                if len(form) > 2:
                    self.code(form[2], env)
                body = form[3:]
            elif h in ("dolist", "dotimes"):
                if isinstance(spec, list) and spec:
                    for item in spec[1:]:
                        self.code(item, env)
                    if isinstance(spec[0], Sym):
                        inner[str(spec[0])] = ([Sym("car"), spec[1]]  # an element of the list
                                               if h == "dolist" and len(spec) > 1 else None)
                body = form[2:]
            elif h in ("do", "do*"):
                for binding in spec if isinstance(spec, list) else []:
                    if isinstance(binding, list) and binding:
                        for item in binding[1:]:
                            self.code(item, inner)
                        if isinstance(binding[0], Sym):
                            inner[str(binding[0])] = None
                    elif isinstance(binding, Sym):
                        inner[str(binding)] = None
                if len(form) > 2 and isinstance(form[2], list):
                    for item in form[2]:
                        self.code(item, inner)
                body = form[3:]
            elif h in ("handler-case", "restart-case"):
                if len(form) > 1:
                    self.code(form[1], env)
                for clause in form[2:]:
                    if isinstance(clause, list) and len(clause) > 1:
                        sub = dict(env)
                        for var in _symbols(clause[1]):
                            sub[var] = None
                        for item in clause[2:]:
                            self.code(item, sub)
                return
            else:  # loop: its variables are opaque
                for i, item in enumerate(form[1:-1], 1):
                    if isinstance(item, Sym) and str(item) in ("for", "with", "as") \
                            and isinstance(form[i + 1], Sym):
                        inner[str(form[i + 1])] = None
                        if i + 3 < len(form) and str(form[i + 2]) == "in":
                            inner[str(form[i + 1])] = [Sym("car"), form[i + 3]]
                body = form[1:]
            for item in body:
                self.code(item, inner)
            return
        if h == "defstruct":
            for slot in form[2:]:
                if isinstance(slot, list) and len(slot) > 1:
                    self.code(slot[1], env)
            return
        if h in ("flet", "labels", "macrolet") and len(form) > 1 and isinstance(form[1], list):
            inner = dict(env)
            for binding in form[1]:
                if isinstance(binding, list) and binding:
                    inner["#'" + str(binding[0])] = "local"
                    positions = _passes_name(self.scan, binding[1] if len(binding) > 1 else None,
                                             binding[2:], self.disp)
                    if positions:
                        self.local_disp[str(binding[0])] = positions
            for binding in form[1]:
                if isinstance(binding, list) and binding:
                    sub = dict(inner if h == "labels" else env)
                    for k, n in _lambda_params(binding[1] if len(binding) > 1 else None):
                        sub[n] = ("lparam", str(binding[0]), k)
                    for item in binding[2:]:
                        self.code(item, sub)
            for item in form[2:]:
                self.code(item, inner)
            return
        if h == "lambda" and len(form) > 1:
            inner = dict(env)
            slot = self.scan.lambda_slot.get(id(form))
            for k, n in _lambda_params(form[1]):
                # a lambda handed to a raw function: its parameters are what
                # that function funcalls it with (checked in the fixpoint)
                inner[n] = ("lam",) + slot + (k,) if slot else None
            for item in form[2:]:
                self.code(item, inner)
            return
        if h in ("setf", "setq", "psetf", "psetq"):
            pairs = form[1:]
            for place, value in zip(pairs[0::2], pairs[1::2]):
                if isinstance(place, Sym) and str(place) in env:
                    self.local_writes.append((str(place), value, env))
                elif isinstance(place, Sym) and str(place).startswith("*"):
                    self.special_write(str(place), value, env)
                elif _head(place) in self.scan.slots:
                    self.slot_write(_head(place), value, env)
                elif _head(place) in SELECT and len(place) > SELECT[_head(place)] + 1:
                    # (setf (gethash k H) v), (setf (car L) v): a write into H / L
                    base = place
                    while _head(base) in SELECT and len(base) > SELECT[_head(base)] + 1:
                        base = base[1 + SELECT[_head(base)]]
                    value = [Sym("list"), value]
                    if isinstance(base, Sym) and str(base) in env:
                        self.local_writes.append((str(base), value, env))
                    elif isinstance(base, Sym) and str(base).startswith("*"):
                        self.special_write(str(base), value, env)
                    elif _head(base) in self.scan.slots:
                        self.slot_write(_head(base), value, env)
                elif _head(place) in ("symbol-function", "fdefinition"):
                    quoted = _quoted_symbol(place[1]) if len(place) > 1 else None
                    if quoted is None or quoted in self.scan.book:
                        self.site("WORLD", "(setf ({} {}))".format(
                            _head(place), _show(place[1]) if len(place) > 1 else ""))
            # walk normally below
        if h in ("push", "pushnew") and len(form) > 2:
            place, value = form[2], [Sym("cons"), form[1], form[2]]
            if isinstance(place, Sym) and str(place) in env:
                self.local_writes.append((str(place), value, env))
            elif isinstance(place, Sym) and str(place).startswith("*"):
                self.special_write(str(place), value, env)
            elif _head(place) in self.scan.slots:
                self.slot_write(_head(place), value, env)
        if h == "multiple-value-setq" and len(form) > 1 and isinstance(form[1], list):
            for var in form[1]:
                if isinstance(var, Sym):
                    self.local_writes.append((str(var), None, env))
        if h in ("defvar", "defparameter") and len(form) > 2 and isinstance(form[1], Sym):
            self.special_write(str(form[1]), form[2], env)
        args = form[1:]
        positions: set = set()
        target = h
        if h in ("apply", "funcall") and args and _quoted_symbol(args[0]) in self.disp:
            target, args = _quoted_symbol(args[0]), args[1:]
        if target in self.disp:
            positions = self.disp[target]
            for position in positions:
                if position >= len(args):
                    continue
                arg = args[position]
                leaves = _literal_leaves(arg)
                if leaves is not None:
                    self.allowed.update(id(leaf) for leaf in leaves)
                    if (target, position) in self.scan.resolving:
                        for leaf in leaves:
                            self.scan.named.setdefault(_strip(str(leaf[1])), set()).add(self.rel)
                    continue
                if isinstance(arg, Sym) and self.defn and str(arg) in self.params \
                        and self.params[str(arg)] in self.scan.dispatchers.get(self.defn.name, ()):
                    continue  # the enclosing dispatcher's own name parameter
                if isinstance(arg, Sym) and isinstance(env.get(str(arg)), tuple) \
                        and env[str(arg)][1] in self.local_disp \
                        and env[str(arg)][2] in self.local_disp[env[str(arg)][1]]:
                    continue  # a local dispatcher's own name parameter
                if isinstance(arg, Sym) and str(arg) in self.namevars:
                    continue  # bound to literal names, used only as one (below)
                self.site("NAMEVAR", "({} {} ...)".format(target, _show(arg)))
        if h in MAKERS:
            package = form[2] if len(form) > 2 and h in ("intern", "find-symbol") else None
            if not (package is not None and (str(package).lower() in (":keyword", "keyword"))):
                self.site("MAKE", _show(form))
        if h in WORLD:
            quoted = _quoted_symbol(args[0]) if args else None
            resolved = (h in ("symbol-function", "fdefinition") and args
                        and _head(args[0]) in RESOLVERS and len(args[0]) == 2
                        and _literal_leaves(args[0][1]) is not None)
            if not resolved and not (h in ("symbol-function", "fdefinition")
                                     and quoted is not None and quoted not in self.scan.book):
                self.site("WORLD", _show(form))
        if h == "coerce" and len(args) > 1 and _quoted_symbol(args[1]) == "function":
            self.site("WORLD", _show(form))
        # CALL: function positions
        fpos = []
        if h in HOF1 and args:
            fpos.append(args[0] if target == h else None)
            if h in ("funcall", "apply") and target == h and isinstance(args[0], Sym) \
                    and self.defn and str(args[0]) in self.params and str(args[0]) not in env:
                self.scan.param_calls.setdefault(
                    (self.defn.name, self.params[str(args[0])]), []).append(
                        (self, args[1:] if h == "funcall" else args[1:-1], env))
        if h in HOF2 and len(args) > 1:
            fpos.append(args[1])
        if h == "sb-int:encapsulate" and len(args) > 2:
            fpos[-1:] = [args[2]]  # the wrapper, not the wrapped name
        if h == "handler-bind" and args and isinstance(args[0], list):
            fpos.extend(b[1] for b in args[0] if isinstance(b, list) and len(b) > 1)
        if h in KEYED:
            for key, value in zip(args, args[1:]):
                if isinstance(key, Sym) and str(key) in FN_KEYS:
                    fpos.append(value)
        for expression in fpos:
            if expression is not None:
                self.fposition(expression, env)
        # function parameters at call sites of raw definitions
        callee = target if target != h else h
        call_args = args
        if h in ("apply", "funcall") and args and _quoted_symbol(args[0]) in self.scan.raw:
            callee, call_args = _quoted_symbol(args[0]), args[1:]
        if callee in self.scan.raw:
            self.scan.calls.append((self, callee, call_args, env))
            for i, arg in enumerate(call_args):
                if _head(arg) == "function" and len(arg) == 2 and _head(arg[1]) == "lambda":
                    arg = arg[1]
                if _head(arg) == "lambda":
                    self.scan.lambda_slot[id(arg)] = (callee, i)
        if callee in self.scan.ctors:
            self.scan.ctor_calls.append((self, callee, call_args, env))
        for index, item in enumerate(form[1:]):
            if index in positions and target == h and _head(item) in ("quote", "function"):
                self.literal(item, allowed_positions=True)
                continue
            if target != h and index == 0:
                continue  # (apply #'dispatcher ...): the dispatcher literal
            if target != h and (index - 1) in positions and _head(item) in ("quote", "function"):
                self.literal(item, allowed_positions=True)
                continue
            self.code(item, env)

    def template(self, template, env):
        code = _detemplate(template)
        # the template's code: dispatcher positions and direct book heads
        self._template_walk(template, env)

    def _template_walk(self, x, env):
        if not isinstance(x, list) or not x:
            if isinstance(x, Sym) and _strip(str(x)) in self.scan.book:
                self.site("NAME", "template symbol {}".format(_strip(str(x))), [_strip(str(x))])
            return
        h = _head(x)
        if h in ("unquote", "unquote-splicing") and len(x) == 2:
            self.code(x[1], env)
            return
        positions = self.scan.dispatchers.get(h, set()) if h else set()
        for index, item in enumerate(x[1:] if h else x):
            if h and index in positions and (_head(item) == "quote" or _head(item) in
                                             ("unquote", "unquote-splicing")):
                if _head(item) != "quote":
                    self.code(item[1], env)
                continue
            if _head(item) == "quote":
                self._template_walk(item[1], env)
                continue
            self._template_walk(item, env)
        if h and _strip(h) in self.scan.book:
            self.site("NAME", "template head {}".format(_strip(h)), [_strip(h)])

    # -- CALL ---------------------------------------------------------------
    def fposition(self, expression, env):
        reason = self.untraced(expression, env, set())
        if reason:
            self.site("CALL", "{} ({})".format(_show(expression), reason))

    def untraced(self, e, env, seen) -> str | None:
        """None when E's value is traced to a host function; else why not."""
        if e is None:
            return "unknown"
        if not isinstance(e, (Sym, list)):
            return None  # a string, number or character names no function
        if isinstance(e, Sym):
            name = str(e)
            if name in ("nil", "t") or name.startswith(":"):
                return None  # no book function is nil, t or a keyword
            if name in env:
                init = env[name]
                if init is None:
                    return "an opaque binding"
                if isinstance(init, tuple) and init[0] == "lam":
                    self.scan.lamparams.add(init[1:])
                    return None
                if isinstance(init, tuple):
                    self.flparams.add(init[1:])
                    return None
                if name in seen:
                    return None
                self.fvars.add(name)
                return self.untraced(init, env, seen | {name})
            if name in self.params and self.defn:
                if DEBUG is not None:
                    DEBUG.append((self.defn.name, self.params[name], self.ctx, self.line))
                self.scan.fparams.add((self.defn.name, self.params[name]))
                return None
            if name.startswith("*") or name.startswith("+"):
                self.scan.fspecials.add(name)
                return None
            return "a free variable"
        if not isinstance(e, list) or not e:
            return "not a function"
        h = _head(e)
        if h in ("function", "quote") and len(e) == 2:
            if _head(e[1]) == "lambda":
                return None
            if isinstance(e[1], Sym):
                s = _strip(str(e[1]))
                if h == "function" and ("#'" + str(e[1])) in env:
                    return None
                return "a book function" if s in self.scan.book else None
            books = sorted({x for x in _symbols(e[1]) if x in self.scan.book})
            return "quoted data naming {}".format(" ".join(books)) if books else None
        if h == "lambda":
            return None
        if h in RESOLVERS and len(e) == 2 and (
                _literal_leaves(e[1]) is not None
                or (isinstance(e[1], Sym) and self.defn and str(e[1]) in self.params
                    and self.params[str(e[1])] in self.scan.dispatchers.get(self.defn.name, ()))):
            return None  # a table resolution of a literal or of the dispatcher's own name
        if h in ("symbol-function", "fdefinition") and len(e) == 2:
            s = _quoted_symbol(e[1])
            return None if s is not None and s not in self.scan.book else "a function cell"
        if h in ("if",):
            return self.untraced(e[2] if len(e) > 2 else None, env, seen) or \
                (self.untraced(e[3], env, seen) if len(e) > 3 else None)
        if h in ("or",):
            for item in e[1:]:
                r = self.untraced(item, env, seen)
                if r:
                    return r
            return None
        if h in ("and", "progn", "the", "when", "unless", "prog1"):
            last = e[1] if h == "prog1" else e[-1]
            return self.untraced(last, env, seen)
        if h in CONSTRUCT:
            for item in e[1:]:
                r = self.untraced(item, env, seen)
                if r:
                    return r
            return None
        if h in SELECT and len(e) > SELECT[h]:
            return self.untraced(e[1 + SELECT[h]], env, seen)
        if h in self.scan.slots and len(e) == 2:
            self.scan.fslots.add(h)
            return None
        if h in self.scan.raw and self.scan.raw[h].kind == "defun":
            return self.scan.returns_traced(h)
        if h in NONFUNCTION or (h.startswith(NONFUNCTION_PACKAGES) and h not in self.scan.raw):
            return None
        return "the value of ({} ...)".format(h)

    def special_write(self, name, value, env):
        self.scan.special_writes.append((self, name, value, env))

    def slot_write(self, accessor, value, env):
        self.scan.slot_writes.append((self, accessor, value, env))


def _show(form, limit=100) -> str:
    def render(x):
        if isinstance(x, list):
            if _head(x) == "quote" and len(x) == 2:
                return "'" + render(x[1])
            if _head(x) == "function" and len(x) == 2:
                return "#'" + render(x[1])
            return "(" + " ".join(render(i) for i in x) + ")"
        if isinstance(x, Sym):
            return str(x)
        if isinstance(x, str):
            return '"' + x + '"'
        return str(x)
    text = render(form)
    return text if len(text) <= limit else text[:limit - 3] + "..."


def _tails(body):
    """The expressions a body may return."""
    if not body:
        return [Sym("nil")]
    last = body[-1]
    h = _head(last)
    if h in ("let", "let*", "progn", "locally", "when", "unless", "block") and isinstance(last, list):
        rest = last[2:] if h in ("let", "let*", "when", "unless", "block") else last[1:]
        return _tails(rest)
    if h == "if":
        return _tails([last[2]]) + (_tails([last[3]]) if len(last) > 3 else [Sym("nil")])
    if h == "cond":
        out = []
        for clause in last[1:]:
            if isinstance(clause, list):
                out += _tails(clause[1:] or clause[:1])
        return out
    return [last]


def scan_sources(files: dict[str, list], book: set[str]) -> Scan:
    defs, tops = _definitions(files)
    scan = Scan(book=book - set(defs), raw=defs)
    scan.calls, scan.ctor_calls = [], []
    scan.lambda_slot, scan.lamparams, scan.param_calls = {}, set(), {}
    scan.special_writes, scan.slot_writes = [], []
    _structs(scan, tops)
    _dispatchers(scan)
    _labels(scan)
    returns: dict[str, str | None] = {}

    def returns_traced(name):
        if name in returns:
            return returns[name]
        returns[name] = None  # assume, for recursion
        d = defs[name]
        w = Walker(scan, d.file, d.name, d.line, d)
        result = None
        for tail in _tails(d.body):
            r = w.untraced(tail, {}, set())
            if r:
                result = "{} returns {}".format(name, r)
                break
        returns[name] = result
        return result
    scan.returns_traced = returns_traced

    walkers = []
    for rel, ctx, line, form in tops:
        defn = defs.get(ctx) if _head(form) in ("defun", "defmacro", "defun-inline") else None
        w = Walker(scan, rel, ctx, line, defn)
        walkers.append(w)
        if defn:
            env = {}
            for item in defn.body:
                w.code(item, env)
        else:
            w.code(form, {})
    # sources of every function parameter, special and slot, to a fixpoint
    done: set = set()
    while True:
        work = []
        for w, callee, args, env in scan.calls:
            d = defs[callee]
            for key, _n in d.params:
                if (callee, key) not in scan.fparams:
                    continue
                if isinstance(key, int) and key < len(args):
                    work.append((w, args[key], env, "argument {} of {}".format(key + 1, callee)))
                elif isinstance(key, str) and key.startswith(":"):
                    for k, v in zip(args, args[1:]):
                        if isinstance(k, Sym) and str(k) == key:
                            work.append((w, v, env, "{} of {}".format(key, callee)))
        for callee, i, k in sorted(scan.lamparams, key=str):
            keys = [key for key, _n in defs[callee].params if key == i]
            for key in keys:
                for w, args, env in scan.param_calls.get((callee, key), []):
                    if isinstance(k, int):
                        work.append((w, args[k] if k < len(args) else None, env,
                                     "argument {} {} passes its lambda".format(k + 1, callee)))
                if not scan.param_calls.get((callee, key)):
                    pass  # never called: the parameter receives nothing
        for w in walkers:
            for local, args, env in w.local_calls:
                for i, arg in enumerate(args):
                    if (local, i) in w.flparams:
                        work.append((w, arg, env, "argument {} of local {}".format(i + 1, local)))
            for var, value, env in w.local_writes:
                if var in w.fvars:
                    work.append((w, value, env, "a write of {}".format(var)))
        for w, name, value, env in scan.special_writes:
            if name in scan.fspecials:
                work.append((w, value, env, "a value of {}".format(name)))
        for w, accessor, value, env in scan.slot_writes:
            if accessor in scan.fslots:
                work.append((w, value, env, "a value of slot {}".format(accessor)))
        for w, ctor, args, env in scan.ctor_calls:
            struct, boa, conc = scan.ctors[ctor]
            if boa is None:
                for k, v in zip(args, args[1:]):
                    if isinstance(k, Sym) and str(k).startswith(":") and \
                            conc + str(k)[1:] in scan.fslots:
                        work.append((w, v, env, "{} of {}".format(k, ctor)))
            else:
                for i, slot in enumerate(boa):
                    if conc + slot in scan.fslots and i < len(args):
                        work.append((w, args[i], env, "argument {} of {}".format(i + 1, ctor)))
        new = [x for x in work if (x[0].rel, x[0].ctx, id(x[1]), x[3]) not in done]
        if not new:
            break
        for w, value, env, what in new:
            done.add((w.rel, w.ctx, id(value), what))
            reason = w.untraced(value, env, set())
            if reason:
                w.site("CALL", "{} reaches a function position as {} ({})".format(
                    _show(value), what, reason))
    scan.sites = sorted(set(scan.sites), key=lambda s: (s.file, s.line, s.rule, s.detail))
    return scan


def judge(scan: Scan, allows: list[Allow], carried: set[str]) -> tuple[list[str], dict]:
    """Findings: every site no entry covers, every stale entry, and every
    entry covering a def-carried function."""
    out: list[str] = []
    used: set[int] = set()
    covered = {"allowed": 0, "pending": 0}
    for s in scan.sites:
        match = [i for i, a in enumerate(allows)
                 if (a.rule, a.file, a.context) == (s.rule, s.file, s.context)]
        bad = sorted(s.symbols & carried)
        if match and not bad:
            used.update(match)
            covered["pending" if allows[match[0]].pending else "allowed"] += 1
            continue
        if match and bad:
            used.update(match)
        out.append("{}:{} ({}) {}: {}{}".format(
            s.file, s.line, s.context, s.rule, s.detail,
            "; names def-carried {}, which no allow entry may cover".format(", ".join(bad))
            if bad else ""))
    for i, a in enumerate(allows):
        if i not in used:
            out.append("tools/raw_dispatch_rule.py: the {} entry {} {} {} matches no site "
                       "(stale; remove it)".format("pending" if a.pending else "allow",
                                                   a.rule, a.file, a.context))
    return out, covered


def raw_sources(tree=None) -> dict[str, list]:
    tree = tree or ledger.load_tree(lazy=True)
    return {rel: tree.hosts[rel].forms for rel in ledger.raw_host_paths(tree)}


def carried_functions() -> set[str]:
    """Every function a def-carried row names: its opens, transitions and
    bridged recognizers, and the opens it says are produced."""
    from tools import interface_emit
    out: set[str] = set()
    for row in interface_emit.carried_rows().values():
        for key in ("established", "transitions", "concludes"):
            out.update(pair[0] for pair in row.get(key, []))
        out.update(row.get("produced", []))
    return out


def book_functions(tree) -> set[str]:
    """Every ACL2 function the tree defines: books, ACL2-mode host files and
    the functions a macro introduces (interface_emit's reading)."""
    from tools import harness_check, interface_emit
    raw = ledger.raw_host_paths(tree)
    return (set(tree.functions) | set(harness_check._acl2_definition_forms(tree, raw))
            | interface_emit.generated_names())


# Entry names a derived dispatcher resolves with no definterface declaration
# (fnn-call takes any name's counterpart).  A ratchet: the count may fall,
# never rise; the dispatcher's own table check is owed after stage 0.
UNDECLARED_CEILING = 148


def findings(tree=None, declared: set[str] | None = None) -> tuple[list[str], dict]:
    from tools import interface_emit
    tree = tree or ledger.load_tree(lazy=True)
    scan = scan_sources(raw_sources(tree), book_functions(tree))
    problems, covered = judge(scan, ALLOW + PENDING, carried_functions())
    # a produced open is never dispatched by any dispatcher (def-carried
    # :produced; interface_emit checks the RAW_DISPATCHERS reading, this the
    # derived dispatchers too)
    for row_name, row in sorted(interface_emit.carried_rows().items()):
        for f in row.get("produced", []):
            if f in scan.named:
                problems.append("the raw host dispatches {} ({}), an open whose argument "
                                "the def-carried row {} says is produced".format(
                                    f, ", ".join(sorted(scan.named[f])), row_name))
    if declared is None:
        declared = {d["name"] for d in interface_emit.declarations()}
    undeclared = sorted(set(scan.named) - declared)
    if len(undeclared) > UNDECLARED_CEILING:
        problems.append("{} names a dispatcher resolves have no definterface declaration "
                        "(ceiling {}); declare the new ones: {}".format(
                            len(undeclared), UNDECLARED_CEILING,
                            " ".join(undeclared[:20])))
    covered["sites"] = len(scan.sites)
    covered["dispatchers"] = len(scan.dispatchers)
    covered["undeclared"] = len(undeclared)
    return problems, covered


def summary(covered: dict, problems: list) -> str:
    return ("raw_dispatch_rule: {} site(s) outside the rule; {} allowed, {} pending stage 0; "
            "{} dispatcher(s); {} undeclared dispatched name(s) (ceiling {}); "
            "{} finding(s)".format(covered["sites"], covered["allowed"], covered["pending"],
                                   covered["dispatchers"], covered["undeclared"],
                                   UNDECLARED_CEILING, len(problems)))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--sites", action="store_true", help="print every site, covered or not")
    args = parser.parse_args(argv)
    if args.sites:
        tree = ledger.load_tree(lazy=True)
        scan = scan_sources(raw_sources(tree), book_functions(tree))
        for s in scan.sites:
            print("{}\t{}\t{}\t{}\t{}".format(s.rule, s.file, s.context, s.line, s.detail))
        return 0
    problems, covered = findings()
    print(summary(covered, problems))
    for problem in problems:
        print("  " + problem)
    return 1 if (args.check and problems) else 0


if __name__ == "__main__":
    raise SystemExit(main())
