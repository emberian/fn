#!/usr/bin/env python3
"""Emit the shallow embedding of fn2's closed subset from the world ACL2 printed.

Input: the `(:embed ...)` part of the S-expression print-world.lisp writes. Outputs:

  WORLD.lean  every function of the closure as a Lean `def` over `Fn2.ACL2.Val` (its translated
              ACL2 body, read term for term), its guard as `F.guard`, and the dispatch `fns`;
  KINDS.lean  the kinds declared in the step language, as `Fn2.Arms.Kind` terms (every
              expression as the declaration writes it, a `Val` that `Fn2.Arms.readExpr` reads),
              each kind's phase values, the declared operations they call, the declared wait
              kinds and the constants the arms name, assembled as `world : Fn2.Arms.World`.

The subset is closed and its edge is named, never guessed:
  * a function whose body calls something neither translated nor native stops the emission
    (the printer lists bodiless functions under :refused; the natives are Fn2.ACL2.Native);
  * a recursive function is emitted with fuel `measure + 1` (its ACL2 measure, translated): if
    its measure is not a natural-number term, or it is mutually recursive, it stops the emission;
  * a quoted object outside the subset (a rational, a complex) stops the emission.

  EQNS.lean   the dispatch equations `fns "F" [a0 ...] = some («F» a0 ...)` and
              `guardOf "F" [a0 ...] = some («F».guard a0 ...)`, each by `rfl`, split over the
              files given (PW3 rewrites by them instead of unfolding the dispatch).

Usage: emit_embed.py WORLD.sexp WORLD.lean KINDS.lean NAMESPACE [EQNS.lean ...]
"""
import re
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from emit_lean import read_all, Atom, Str, List, show, as_list, is_nil, val, term, lean_str, is_lambda, die, ident  # noqa: E402

NATIVE = {
    "EQUAL": "Prim.equal", "CONS": "Val.cons", "CAR": "Val.car", "CDR": "Val.cdr",
    "CONSP": "Prim.consp", "INTEGERP": "Prim.integerp", "ACL2-NUMBERP": "Prim.acl2Numberp",
    "RATIONALP": "Prim.rationalp", "COERCE": "Prim.coerce", "SYMBOLP": "Prim.symbolp",
    "STRINGP": "Prim.stringp", "CHARACTERP": "Prim.characterp", "CHAR-CODE": "Prim.charCode", "CODE-CHAR": "Prim.codeChar",
    "CEILING": "Native.ceiling", "<": "Prim.lt",
    "BINARY-+": "Prim.plus", "BINARY-*": "Prim.times", "UNARY--": "Prim.neg",
    "BINARY-LOGAND": "Native.logand", "BINARY-LOGIOR": "Native.logior",
    "BINARY-LOGXOR": "Native.logxor", "BINARY-LOGEQV": "Native.logeqv", "LOGNOT": "Native.lognot",
    "LOGORC1": "Native.logorc1", "FLOOR": "Native.floor", "MOD": "Native.mod",
    "EVENP": "Native.evenp", "NONNEGATIVE-INTEGER-QUOTIENT": "Native.niq", "EXPT": "Native.expt", "ASH": "Native.ash",
    "LEN": "Native.len", "NTH": "Native.nth", "MV-NTH": "Native.nth",
    "UPDATE-NTH": "Native.updateNth", "MEMBER-EQUAL": "Native.memberEqual",
    "ACL2-COUNT": "(fun x => Val.int (Val.acl2Count x))",
}
SPECIAL = {"IF", "RETURN-LAST"}
# natives computed only where ACL2's value is an integer (EXPT at a negative exponent is a
# rational): a native whose definition calls one may pass through a rational, so its definition
# is outside the subset, recorded with the rational primitive it reaches (ASH: (expt 2 c), c < 0)
INTEGER_DOMAIN = {"EXPT": "UNARY-/"}
# ---------------------------------------------------------------- shallow functions

class Fn:
    def __init__(self, entry):
        self.name = str(entry[0])
        d = {}
        xs = list(entry[1:])
        for k, v in zip(xs[::2], xs[1::2]):
            d[str(k)] = v
        self.formals = [str(v) for v in as_list(d[":FORMALS"])]
        self.body = d[":BODY"]
        self.guard = d[":GUARD"]
        self.measure = d[":MEASURE"]
        self.recursive = [str(v) for v in as_list(d[":RECURSIVE"])]
        # a constrained function translated as its attachment (print-world.lisp meta-body): the
        # attached function, and its encapsulate's constraint as translated terms
        a = d.get(":ATTACHMENT")
        self.attachment = None if a is None or is_nil(a) else str(a)
        self.constraint = [] if self.attachment is None else list(as_list(d.get(":CONSTRAINT", List([]))))


def free_vars(t, acc):
    """The variables of a translated term, in first-occurrence order (a lambda's body is closed)."""
    if isinstance(t, List):
        if len(t) == 0 or t[0] == "QUOTE":
            return acc
        if is_lambda(t[0]):
            for a in t[1:]:
                free_vars(a, acc)
            return acc
        for a in t[1:]:
            free_vars(a, acc)
        return acc
    a = str(t)
    if isinstance(t, Str) or re.fullmatch(r"[+-]?\d+", a) or a in ("NIL", "T") or a.startswith(":"):
        return acc
    if a not in acc:
        acc.append(a)
    return acc


def calls_of(t, acc):
    if isinstance(t, List) and len(t):
        if t[0] == "QUOTE":
            return acc
        if is_lambda(t[0]):
            calls_of(t[0][2], acc)
        else:
            acc.add(str(t[0]))
        for a in t[1:]:
            calls_of(a, acc)
    return acc


def shallow(t, defined, self_name=None):
    if isinstance(t, List):
        if len(t) == 0:
            return "Val.nil"
        if t[0] == "QUOTE":
            return val(t[1])
        if is_lambda(t[0]):
            formals = [str(v) for v in as_list(t[0][1])]
            actuals = [shallow(a, defined, self_name) for a in t[1:]]
            if not formals:
                return shallow(t[0][2], defined, self_name)
            binders = " ".join(f"({ident(v)} : Val)" for v in formals)
            return f"((fun {binders} => {shallow(t[0][2], defined, self_name)}) {' '.join(actuals)})"
        f = str(t[0])
        args = [shallow(a, defined, self_name) for a in t[1:]]
        if f == "IF":
            return f"(if ({args[0]}).truthy then {args[1]} else {args[2]})"
        if f == "RETURN-LAST":
            return args[2]
        if f in NATIVE:
            return f"({NATIVE[f]} {' '.join(args)})"
        if f == self_name:
            return f"({ident(f)}.go fuel {' '.join(args)})"
        if f not in defined:
            die(f"a call of {f}, which is neither translated nor native")
        return f"({ident(f)}{' ' if args else ''}{' '.join(args)})"
    a = str(t)
    if re.fullmatch(r"[+-]?\d+", a) or isinstance(t, Str):
        return val(t)
    if a in ("NIL", "T") or a.startswith(":"):
        return val(t)
    return ident(a)


def emit_fn(fn, defined, out):
    binders = " ".join(f"({ident(v)} : Val)" for v in fn.formals)
    sig = f"{binders} : Val" if binders else ": Val"
    if fn.attachment:
        out.append(f"/-- {fn.name}, constrained (an encapsulate), runs as its attachment {fn.attachment}")
        out.append(f"(`defattach`): ACL2's evaluator calls the attached function. Its constraint is")
        out.append(f"`{fn.name}.constraint`, stated over this function. -/")
    if fn.recursive:
        if fn.recursive != [fn.name]:
            die(f"{fn.name} is mutually recursive with {fn.recursive}: outside the subset")
        if is_nil(fn.measure):
            die(f"{fn.name} is recursive without a measure")
        if not (isinstance(fn.measure, List) and str(fn.measure[0]) in ("NFIX", "ACL2-COUNT")):
            die(f"{fn.name}: measure {show(fn.measure)} is not (NFIX ...) or (ACL2-COUNT ...), a natural number")
        nf = len(fn.formals)
        pats = ", ".join(ident(v) for v in fn.formals)
        under = ", ".join("_" for _ in fn.formals)
        types = " → ".join(["Nat"] + ["Val"] * nf + ["Val"])
        out.append(f"/-- {fn.name}, recursive: fuel `measure + 1` suffices by ACL2's admitted measure. -/")
        out.append(f"def {ident(fn.name)}.go : {types}")
        out.append(f"  | 0{', ' + under if nf else ''} => Val.nil")
        out.append(f"  | fuel + 1{', ' + pats if nf else ''} =>")
        out.append(f"    {shallow(fn.body, defined, fn.name)}")
        out.append(f"def {ident(fn.name)} {sig} :=")
        out.append(f"  {ident(fn.name)}.go ((({shallow(fn.measure, defined)})).nfix + 1){' ' if nf else ''}"
                   + " ".join(ident(v) for v in fn.formals))
    else:
        out.append(f"def {ident(fn.name)} {sig} :=")
        out.append(f"  {shallow(fn.body, defined)}")
    out.append("")


def emit_native_def(fn, defined, out):
    """ACL2's definition of a native F as `«F».acl2`, its body with every native call (its own
    recursive calls included) going to the Lean natives: `∀ x, Native.f x = «F».acl2 x` says the
    native satisfies ACL2's defining equation, which determines the function (ACL2 admitted it
    with its measure)."""
    binders = " ".join(f"({ident(v)} : Val)" for v in fn.formals)
    out.append(f"def {ident(fn.name)}.acl2 {binders} : Val :=")
    out.append(f"  {shallow(fn.body, defined)}")
    out.append("")


def emit_world(emb, path, ns):
    fns = [Fn(as_list(e)) for e in as_list(emb[":FUNCTIONS"])]
    refused = [str(r) for r in as_list(emb[":REFUSED"])]
    natives = [str(r) for r in as_list(emb[":NATIVES"])]
    missing = [n for n in natives if n not in NATIVE and n not in SPECIAL]
    if missing:
        die(f"the printer's natives {missing} have no Lean implementation")
    names = {f.name for f in fns}
    # a function that calls a refused one is itself outside the subset: named, then dropped
    outside = set(refused)
    changed = True
    while changed:
        changed = False
        for f in fns:
            if f.name not in outside and (calls_of(f.body, set()) | calls_of(f.measure, set())) & outside:
                outside.add(f.name)
                changed = True
    dropped = sorted(n for n in outside if n in names)
    kept = [f for f in fns if f.name not in outside]
    defined = set()
    L = []
    L.append("-- GENERATED by meta/emit/emit_embed.py from the world print-world.lisp printed.")
    L.append("-- Do not edit: change a book and re-emit (meta/emit/emit.sh).")
    L.append(f"-- {len(kept)} functions translated, {len(natives)} natives, refused {refused},")
    L.append(f"-- dropped as callers of a refused function {dropped}.")
    L.append("import Fn2.ACL2.Val")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("set_option linter.unusedVariables false")
    L.append("")
    L.append(f"namespace {ns}")
    L.append("open Fn2.ACL2")
    L.append("")
    for f in kept:
        emit_fn(f, defined, L)
        defined.add(f.name)
    L.append("/-! ## Guards: each function's guard, a precondition (ACL2's `guard` property, translated) -/")
    L.append("")
    guards = []
    guard_outside = []
    for f in kept:
        if is_nil(f.guard) or str(f.guard) == "T" or (isinstance(f.guard, List) and f.guard[0] == "QUOTE" and str(f.guard[1]) == "T"):
            continue
        gcalls = calls_of(f.guard, set())
        if gcalls & outside:
            guard_outside.append(f.name)
            continue
        binders = " ".join(f"({ident(v)} : Val)" for v in f.formals)
        L.append(f"def {ident(f.name)}.guard {binders}{' ' if binders else ''}: Val :=")
        L.append(f"  {shallow(f.guard, defined)}")
        L.append("")
        guards.append(f)
    # an attached function's constraint, each term a `Val` over its free variables: the Lean side
    # proves of the function (through its attachment) the conjuncts it can (Fn2.Arms.Attach)
    L.append("/-! ## Attached functions: each runs as its attachment; its encapsulate's constraint, translated -/")
    L.append("")
    attached = []
    for f in kept:
        if not f.attachment:
            continue
        parts = []
        for i, c in enumerate(f.constraint):
            missing = sorted(g for g in calls_of(c, set()) if g not in defined and g not in NATIVE and g not in SPECIAL)
            if missing:
                L.append(f"-- {f.name}'s constraint, term {i}: calls {missing}, outside the translated closure")
                L.append("")
                continue
            vs = free_vars(c, [])
            binders = " ".join(f"({ident(v)} : Val)" for v in vs)
            L.append(f"/-- {f.name}'s constraint, term {i}: `{show(c)[:300]}` -/")
            L.append(f"def {ident(f.name)}.constraint{i} {binders}{' ' if binders else ''}: Val :=")
            L.append(f"  {shallow(c, defined)}")
            L.append("")
            parts.append((i, vs))
        attached.append((f, parts))
    L.append(f"def attached : List (String × String) := [{', '.join(f'({lean_str(f.name)}, {lean_str(f.attachment)})' for f, _ in attached)}]")
    L.append("")
    # ACL2's definitions of the natives, where they stay inside the subset: `«F».acl2`, with every
    # call of another native going to its Lean implementation (the statement is per native)
    L.append("/-! ## ACL2's definitions of the natives, translated (`F.acl2`): Fn2.ACL2.Faithful states")
    L.append("that each native agrees with its definition. A definition that leaves the subset (through the")
    L.append("reciprocal, `NUMERATOR`, `REALPART` ...) is named in `nativeOutside`. -/")
    L.append("")
    nd_in, nd_out = [], []
    for e in as_list(emb.get(":NATIVE-DEFINITIONS", List([]))):
        nf = Fn(as_list(e))
        calls = calls_of(nf.body, set()) | calls_of(nf.measure, set())
        outside_calls = sorted(c for c in calls if c not in defined and c not in NATIVE and c not in SPECIAL
                               and c != nf.name)
        outside_calls = sorted(set(outside_calls) | {INTEGER_DOMAIN[c] for c in calls if c in INTEGER_DOMAIN
                                                       and nf.name not in INTEGER_DOMAIN})
        if outside_calls or (nf.recursive and nf.recursive != [nf.name]) or nf.name in SPECIAL:
            nd_out.append((nf.name, outside_calls))
            continue
        emit_native_def(nf, defined, L)
        nd_in.append(nf.name)
    L.append(f"def nativeTranslated : List String := [{', '.join(lean_str(n) for n in nd_in)}]")
    L.append(f"def nativeOutside : List (String × List String) := [{', '.join(f'({lean_str(n)}, [{chr(44).join(lean_str(c) for c in cs)}])' for n, cs in nd_out)}]")
    L.append("")
    # the dispatch: a binary search tree keyed by `nameKey` (Fn2.ACL2.Val), so each function's
    # dispatch equation holds by `rfl` (PW3); the equations themselves go to the EQNS files
    fn_rows = []
    for f in kept:
        vs = [f"a{i}" for i in range(len(f.formals))]
        call = f"{ident(f.name)}{' ' if vs else ''}{' '.join(vs)}"
        fn_rows.append((f.name, vs, call))
    guard_rows = []
    for f in guards:
        vs = [f"a{i}" for i in range(len(f.formals))]
        call = f"{ident(f.name)}.guard{' ' if vs else ''}{' '.join(vs)}"
        guard_rows.append((f.name, vs, call))
    # each row's arity match is its own small definition (`F.dispatch`, `F.guardDispatch`) and the
    # tree is cut into named subtrees of at most DISPATCH_CHUNK rows: one term of 12,769 lambdas
    # and matches cost the elaborator and compiler about 2,700 s per tree; this shape about 170 s
    L.append("/-! ## The dispatch: each row's arity match, then the trees -/")
    L.append("")
    fn_defs, fn_root = dispatch_tree(fn_rows, "dispatch", "fnTree")
    gd_defs, gd_root = dispatch_tree(guard_rows, "guardDispatch", "guardTree")
    L.extend(fn_defs)
    L.append("/-- The translated functions by ACL2 name, for the term evaluator and the interpreter. -/")
    L.append(f"def fnTree : Dispatch :=\n  {fn_root}")
    L.append("")
    L.extend(gd_defs)
    L.append("/-- The stated guards by ACL2 name. -/")
    L.append(f"def guardTree : Dispatch :=\n  {gd_root}")
    L.append("")
    L.append("def fns : Fns := fun f args => match fnTree.find (nameKey f) with")
    L.append("  | some g => g args")
    L.append("  | none => none")
    L.append("")
    L.append(f"def guardOutside : List String := [{', '.join(lean_str(n) for n in guard_outside)}]")
    L.append("")
    L.append("/-- A function's guard on its arguments (`T` for a function with no stated guard). -/")
    L.append("def guardOf (f : String) (args : List Val) : Option Val := match guardTree.find (nameKey f) with")
    L.append("  | some g => g args")
    L.append("  | none => if (fnTree.find (nameKey f)).isSome && !guardOutside.contains f then some Val.t else none")
    L.append("")
    # the dispatch equations go through these: the name's key is computed once (`rfl` on
    # `nameKey`), then the tree is searched with the key a literal. Stated whole by `rfl`, the
    # elaborator's lazy unfolding opened the called function's body instead (a 25-argument
    # FN2-CONN-WRITE+... ran past 200000 heartbeats); `decide +kernel` on the key held ~8 MB per
    # equation (24 GB for one Eqns file)
    L.append("/-- `fns` at a name whose key is `k` searches the tree for `k`. -/")
    L.append("theorem fns_key {f : String} {k : Nat} (args : List Val) (h : nameKey f = k) :")
    L.append("    fns f args = (match fnTree.find k with | some g => g args | none => none) := by")
    L.append("  subst h; rfl")
    L.append("")
    L.append("/-- `guardOf` at a name whose key is `k` searches the trees for `k`. -/")
    L.append("theorem guardOf_key {f : String} {k : Nat} (args : List Val) (h : nameKey f = k) :")
    L.append("    guardOf f args = (match guardTree.find k with")
    L.append("      | some g => g args")
    L.append("      | none => if (fnTree.find k).isSome && !guardOutside.contains f then some Val.t else none) := by")
    L.append("  subst h; rfl")
    L.append("")
    L.append(f"def refused : List String := [{', '.join(lean_str(r) for r in refused)}]")
    L.append(f"def dropped : List String := [{', '.join(lean_str(r) for r in dropped)}]")
    L.append(f"def translated : List String := [{', '.join(lean_str(f.name) for f in kept)}]")
    L.append("")
    L.append(f"end {ns}")
    L.append("")
    open(path, "w").write("\n".join(L))
    return len(kept), refused, dropped, len(guards), fn_rows, guard_rows


def name_key(n):
    """`Fn2.ACL2.nameKey`: the name's UTF-8 bytes as a base-256 numeral."""
    k = 0
    for b in n.encode():
        if b == 0:
            die(f"a NUL byte in the name {n!r}: nameKey would not be injective")
        k = k * 256 + b
    return k


DISPATCH_CHUNK = 256


def dispatch_tree(rows, suffix, tree):
    """A balanced `Fn2.ACL2.Dispatch` over the rows `(name, formals, call)`: (definitions, root).
    Each row's match on its arity is the definition `«F».SUFFIX`; every subtree of at most
    DISPATCH_CHUNK rows is a definition `TREE.cN`, so no definition is one giant term."""
    rows = sorted(rows, key=lambda r: name_key(r[0]))
    for a, b in zip(rows, rows[1:]):
        if name_key(a[0]) == name_key(b[0]):
            die(f"two dispatch rows for {a[0]}")
    defs = []
    for name, vs, call in rows:
        defs.append(f"def {ident(name)}.{suffix} : List Val → Option Val\n"
                    f"  | [{', '.join(vs)}] => some ({call})\n  | _ => none")
    defs.append("")
    nchunks = [0]

    def node(lo, hi, sub):
        mid = (lo + hi) // 2
        name = rows[mid][0]
        return f"(.node {name_key(name)} {ident(name)}.{suffix} {sub(lo, mid)} {sub(mid + 1, hi)})"

    def inner(lo, hi):
        return ".leaf" if lo >= hi else node(lo, hi, inner)

    def outer(lo, hi):
        if hi - lo > DISPATCH_CHUNK:
            return node(lo, hi, outer)
        n = f"{tree}.c{nchunks[0]}"
        nchunks[0] += 1
        defs.append(f"def {n} : Dispatch :=\n  {inner(lo, hi)}\n")
        return n
    return defs, outer(0, len(rows))


def emit_eqns(fn_rows, guard_rows, paths, world_mod, world_ns):
    """The dispatch equations, one per translated function and one per stated guard, split over
    `paths` so they elaborate in parallel. Each is `fns_key` (`guardOf_key`) at the name's key,
    then `rfl` (the tree searched for the literal key)."""
    eqs = []
    for name, vs, call in fn_rows:
        bs = " ".join(f"({v} : Val)" for v in vs)
        eqs.append(f"@[fn2_dispatch] theorem {ident(name)}.fns_eq {bs}{' ' if bs else ''}:\n"
                   f"    fns {lean_str(name)} [{', '.join(vs)}] = some ({call}) :=\n"
                   f"  (fns_key (k := {name_key(name)}) _ rfl).trans rfl")
    for name, vs, call in guard_rows:
        bs = " ".join(f"({v} : Val)" for v in vs)
        eqs.append(f"@[fn2_dispatch] theorem {ident(name)}.guard_eq {bs}{' ' if bs else ''}:\n"
                   f"    guardOf {lean_str(name)} [{', '.join(vs)}] = some ({call}) :=\n"
                   f"  (guardOf_key (k := {name_key(name)}) _ rfl).trans rfl")
    n = len(paths)
    for i, path in enumerate(paths):
        part = eqs[i::n]
        L = ["-- GENERATED by meta/emit/emit_embed.py: the dispatch equations (PW3), part "
             f"{i + 1} of {n}.",
             "-- Do not edit: change a book and re-emit (meta/emit/emit.sh).",
             f"import {world_mod}", "import Fn2.ACL2.SimpAttr", "",
             "set_option maxRecDepth 100000", "set_option linter.unusedVariables false", "",
             f"namespace {world_ns}", "open Fn2.ACL2", ""]
        L.extend(part)
        L.extend(["", f"end {world_ns}", ""])
        open(path, "w").write("\n".join(L))
    return len(eqs)


# ---------------------------------------------------------------- kinds

def plist(xs):
    xs = list(xs)
    return {str(k): v for k, v in zip(xs[::2], xs[1::2])}


def arm(e, rc="{}"):
    # an arm as the declaration writes it; Fn2.Arms.readSteps reads its steps. RC is the kind's
    # refusal context (the facts `(:refuse WORD)` desugars by: machine-arms.lisp fn2-arms-steps :refuse)
    e = as_list(e)
    d = plist(e[1:])
    sig = as_list(d.get(":SIG", List([])))
    if sig:
        takes, returns, results = as_list(sig[0]), as_list(sig[1]), int(str(sig[2]))
        sigl = (f"some ⟨[{', '.join(lean_str(str(x)) for x in takes)}], "
                f"[{', '.join(lean_str(str(x)) for x in returns)}], {results}⟩")
    else:
        sigl = "none"
    return (f"{{ tag := {lean_str(str(e[0]))}, sig := {sigl},\n"
            f"      decl := {val(d[':DECL'])},\n"
            f"      fn := {lean_str(str(d[':FUNCTION']))}, refuse := {rc} }}")


def refuse_ctx(cols, subarms):
    # the word field: the first of WORD, REPLY, REASON among the kind's columns; a REFUSE sub-arm or not
    names = [str(c[0]) for c in cols]
    field = next((f for f in ("WORD", "REPLY", "REASON") if f in names), None)
    sub = any(str(as_list(a)[0]) == "REFUSE" for a in subarms)
    fl = "none" if field is None else f"(some {lean_str(field)})"
    return f"{{ field := {fl}, sub := {'true' if sub else 'false'} }}"


def coltype(k):
    if isinstance(k, List):
        if k[0] != ":ENUM":
            die(f"column kind {show(k)}")
        return f".enum {len(as_list(k[2]))}"
    w = {":U8": 8, ":U16": 16, ":U32": 32, ":LINK": 32, ":U60": 60, ":U64": 64, ":BOOL": 1}.get(str(k))
    if w is None:
        die(f"column kind {k}")
    return f".uw {w}"


def link_entry(e):
    e = as_list(e)
    d = plist(e[1:])
    kf = f"(some {lean_str(str(d[':KIND-FIELD']))})" if ":KIND-FIELD" in d and not is_nil(d[":KIND-FIELD"]) else "none"
    back = [lean_str(str(x)) for x in as_list(d.get(":BACK", List([])))]
    reads = [lean_str(str(x)) for x in as_list(d.get(":READS", List([])))]
    return (f"{{ name := {lean_str(str(e[0]))}, kind := {lean_str(str(d[':KIND']))}, "
            f"slot := {lean_str(str(d[':SLOT']))}, gen := {lean_str(str(d[':GEN']))}, "
            f"kindField := {kf}, back := [{', '.join(back)}], reads := [{', '.join(reads)}] }}")


def kind(e, reg_links=None):
    e = as_list(e)
    d = plist(e[1:])
    cols = [as_list(c) for c in as_list(d[":COLUMNS"])]
    raw_links = d.get(":LINKS")
    if (raw_links is None or is_nil(raw_links)) and reg_links is not None:
        raw_links = reg_links.get(str(e[0]), List([]))
    links = [link_entry(l) for l in as_list(raw_links or List([]))]
    rc = refuse_ctx(cols, as_list(d[":SUBARMS"]))
    return (f"{{ name := {lean_str(str(e[0]))},\n"
            f"    childForm := {'true' if str(d[':FORM']) == ':CHILDREN' else 'false'},\n"
            f"    tuple := [{', '.join(lean_str(str(x)) for x in as_list(d[':TUPLE']))}],\n"
            f"    states := [{', '.join(lean_str(str(x)) for x in as_list(d[':STATES']))}],\n"
            f"    phases := [{', '.join(f'({lean_str(str(as_list(p)[0]))}, {as_list(p)[1]})' for p in as_list(d[':PHASES']))}],\n"
            f"    columns := [{', '.join(f'({lean_str(str(c[0]))}, {coltype(c[1])})' for c in cols)}],\n"
            f"    table := [{', '.join(lean_str(str(as_list(c)[0])) for c in as_list(d[':TABLE']))}],\n"
            f"    stops := [{', '.join(lean_str(str(x).lstrip(':')) for x in as_list(d[':STOPS']))}],\n"
            f"    links := [{', '.join(links)}],\n"
            f"    subarms := [\n    {(',' + chr(10) + '    ').join(arm(a, rc) for a in as_list(d[':SUBARMS']))}],\n"
            f"    arms := [\n    {(',' + chr(10) + '    ').join(arm(a, rc) for a in as_list(d[':ARMS']))}],\n"
            f"    observes := [\n    {(',' + chr(10) + '    ').join(arm(a, rc) for a in as_list(d[':OBSERVES']))}] }}")


def op(e):
    e = as_list(e)
    d = plist(e[1:])
    ans = d[":ANSWERS"]
    answers = ".none" if is_nil(ans) else (".open_" if str(ans) == "T" else
                                           f"(.list [{', '.join(val(c) for c in as_list(ans))}])")
    callee = f"(some {lean_str(str(d[':CALLEE']))})" if not is_nil(d[":CALLEE"]) else "none"

    def so(xs):
        return "[" + ", ".join("none" if is_nil(x) else f"(some {lean_str(str(x))})" for x in as_list(xs)) + "]"
    return (f"{{ name := {lean_str(str(e[0]))}, callee := {callee}, "
            f"formals := [{', '.join(lean_str(str(x)) for x in as_list(d[':FORMALS']))}], "
            f"stobjsIn := {so(d[':STOBJS-IN'])}, stobjsOut := {so(d[':STOBJS-OUT'])}, answers := {answers}, "
            f"faults := [{', '.join(val(c) for c in as_list(d[':FAULTS']))}], "
            f"bound := {bound(d.get(':BOUND'))}"
            + (f", coreFormals := [{', '.join(lean_str(str(x)) for x in as_list(d[':CORE-FORMALS']))}], "
               f"coreIn := {so(d[':CORE-STOBJS-IN'])}, coreOut := {so(d[':CORE-STOBJS-OUT'])}"
               if not is_nil(d.get(':CORE-FORMALS', List([]))) else "")
            + " }")


def bound(b):
    # the declared cost's static bound (bytes steps descriptors); none where a dimension has none
    xs = as_list(b) if b is not None and not is_nil(b) else []
    if len(xs) != 3 or any(is_nil(x) for x in xs):
        return "none"
    return f"(some ({int(str(xs[0]))}, {int(str(xs[1]))}, {int(str(xs[2]))}))"


def emit_kinds(emb, registry_waits, path, ns, world_ns, reg_links=None):
    kinds = [kind(k, reg_links) for k in as_list(emb[":KINDS"])]
    ops = [op(o) for o in as_list(emb[":OPERATIONS"])]
    consts = [as_list(c) if isinstance(c, List) else c for c in as_list(emb[":CONSTANTS"])]
    cs = []
    for c in as_list(emb[":CONSTANTS"]):
        c = list(c)
        v = c[2] if len(c) == 3 else c[1]
        cs.append(f"({lean_str(str(c[0]))}, {val(v)})")
    waits = []
    for name, row in registry_waits:
        d = plist(row)
        park = f"(some {lean_str(str(d[':PARK']))})" if ":PARK" in d and not is_nil(d[":PARK"]) else "none"
        waits.append(f"{{ kind := {lean_str(str(d[':KIND']).lstrip(':'))}, park := {park} }}")
    L = []
    L.append("-- GENERATED by meta/emit/emit_embed.py from the world print-world.lisp printed.")
    L.append("-- Do not edit: change a declaration and re-emit (meta/emit/emit.sh).")
    nchild = sum(1 for k in kinds if "childForm := true" in k)
    L.append(f"-- {len(kinds)} kinds in the step language ({nchild} in child form), {len(ops)} declared operations,")
    L.append(f"-- {len(waits)} wait kinds,")
    L.append(f"-- {len(cs)} constants.")
    L.append("import Fn2.Arms")
    L.append(f"import {world_ns}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append(f"namespace {ns}")
    L.append("open Fn2.ACL2 Fn2.Arms")
    L.append("")
    L.append("def kinds : List Kind := [\n  " + ",\n  ".join(kinds) + "]")
    L.append("")
    L.append("def ops : List Op := [\n  " + ",\n  ".join(ops) + "]")
    L.append("")
    L.append("def waits : List Wait := [" + ", ".join(waits) + "]")
    L.append("")
    L.append("def consts : List (String × Val) := [" + ", ".join(cs) + "]")
    L.append("")
    tup = ", ".join(lean_str(str(x)) for x in as_list(emb.get(":CORE-TUPLE", List([]))))
    L.append("/-- `fn2-core`'s children in field order (its logical value is their list). -/")
    L.append(f"def coreTuple : List String := [{tup}]")
    L.append("")
    L.append(f"def world : World := {{ kinds, ops, waits, consts, fns := {world_ns}.fns }}")
    L.append("")
    L.append(f"end {ns}")
    L.append("")
    open(path, "w").write("\n".join(L))
    return len(kinds), len(ops)


def main():
    src, world_out, kinds_out, ns = sys.argv[1:5]
    eqn_outs = sys.argv[5:]
    # newline='': a CR inside a string literal is data (universal newlines turned CR LF into LF)
    forms = read_all(open(src, newline='').read())
    top = as_list(forms[0])
    if str(top[0]) != ":FN2-WORLD":
        die("expected (:FN2-WORLD ...)")
    reg = {str(as_list(e)[0]): as_list(e)[1] for e in as_list(top[1])[1:]}
    emb = {str(as_list(e)[0]): as_list(e)[1] for e in as_list(top[2])[1:]}
    waits = [(r[0], List(as_list(r)[1:])) for r in as_list(reg.get(":WAITS", List([])))]
    reg_links = {str(as_list(r)[0]): plist(as_list(r)[1:]).get(":LINKS", List([]))
                 for r in as_list(reg.get(":MACHINE-KINDS", List([])))}
    world_ns = ns + "World"
    n, refused, dropped, ng, fn_rows, guard_rows = emit_world(emb, world_out, world_ns)
    ne = emit_eqns(fn_rows, guard_rows, eqn_outs, world_ns, world_ns) if eqn_outs else 0
    nk, no = emit_kinds(emb, waits, kinds_out, ns + "Kinds", world_ns, reg_links)
    print(f"EMBED functions={n} guards={ng} refused={refused} dropped={dropped} kinds={nk} operations={no} equations={ne}")


if __name__ == "__main__":
    main()
