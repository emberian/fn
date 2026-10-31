#!/usr/bin/env python3
"""Emit the shallow embedding of fn2's closed subset from the world ACL2 printed.

Input: the `(:embed ...)` part of the S-expression print-world.lisp writes. Outputs:

  WORLD.lean  every function of the closure as a Lean `def` over `Fn2.ACL2.Val` (its translated
              ACL2 body, read term for term), its guard as `F.guard`, and the dispatch `fns`;
  KINDS.lean  the kinds declared in the step language and defined in child form, as
              `Fn2.Arms.Kind` terms (every expression a translated `Term`), the declared
              operations they call, the declared wait kinds and the constants the step language
              names, assembled as `world : Fn2.Arms.World`.

The subset is closed and its edge is named, never guessed:
  * a function whose body calls something neither translated nor native stops the emission
    (the printer lists bodiless functions under :refused; the natives are Fn2.ACL2.Native);
  * a recursive function is emitted with fuel `measure + 1` (its ACL2 measure, translated): if
    its measure is not a natural-number term, or it is mutually recursive, it stops the emission;
  * a quoted object outside the subset (a rational, a complex) stops the emission.

Usage: emit_embed.py WORLD.sexp WORLD.lean KINDS.lean NAMESPACE
"""
import re
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from emit_lean import read_all, Atom, Str, List, show, as_list, is_nil, val, term, lean_str, is_lambda, die, ident  # noqa: E402

NATIVE = {
    "EQUAL": "Prim.equal", "CONS": "Val.cons", "CAR": "Val.car", "CDR": "Val.cdr",
    "CONSP": "Prim.consp", "INTEGERP": "Prim.integerp", "ACL2-NUMBERP": "Prim.acl2Numberp",
    "RATIONALP": "Prim.rationalp", "COERCE": "Prim.coerce", "SYMBOLP": "Prim.symbolp",
    "STRINGP": "Prim.stringp", "CHARACTERP": "Prim.characterp", "<": "Prim.lt",
    "BINARY-+": "Prim.plus", "BINARY-*": "Prim.times", "UNARY--": "Prim.neg",
    "BINARY-LOGAND": "Native.logand", "BINARY-LOGIOR": "Native.logior",
    "BINARY-LOGXOR": "Native.logxor", "BINARY-LOGEQV": "Native.logeqv", "LOGNOT": "Native.lognot",
    "LOGORC1": "Native.logorc1", "FLOOR": "Native.floor", "MOD": "Native.mod",
    "EVENP": "Native.evenp", "NONNEGATIVE-INTEGER-QUOTIENT": "Native.niq", "EXPT": "Native.expt",
    "LEN": "Native.len", "NTH": "Native.nth", "MV-NTH": "Native.nth",
    "UPDATE-NTH": "Native.updateNth", "MEMBER-EQUAL": "Native.memberEqual",
    "ACL2-COUNT": "(fun x => Val.int (Val.acl2Count x))",
}
SPECIAL = {"IF", "RETURN-LAST"}
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
    if fn.recursive:
        if fn.recursive != [fn.name]:
            die(f"{fn.name} is mutually recursive with {fn.recursive}: outside the subset")
        if is_nil(fn.measure):
            die(f"{fn.name} is recursive without a measure")
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
    L.append("-- GENERATED by fn2/meta/emit/emit_embed.py from the world print-world.lisp printed.")
    L.append("-- Do not edit: change a book and re-emit (fn2/meta/emit/emit.sh).")
    L.append(f"-- {len(kept)} functions translated, {len(natives)} natives, refused {refused},")
    L.append(f"-- dropped as callers of a refused function {dropped}.")
    L.append("import Fn2.ACL2.Val")
    L.append("import Std.Data.HashMap")
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
    for f in kept:
        if is_nil(f.guard) or str(f.guard) == "T" or (isinstance(f.guard, List) and f.guard[0] == "QUOTE" and str(f.guard[1]) == "T"):
            continue
        gcalls = calls_of(f.guard, set())
        if gcalls & outside:
            continue
        binders = " ".join(f"({ident(v)} : Val)" for v in f.formals)
        L.append(f"def {ident(f.name)}.guard {binders}{' ' if binders else ''}: Val :=")
        L.append(f"  {shallow(f.guard, defined)}")
        L.append("")
        guards.append(f)
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
        if outside_calls or (nf.recursive and nf.recursive != [nf.name]) or nf.name in SPECIAL:
            nd_out.append((nf.name, outside_calls))
            continue
        emit_native_def(nf, defined, L)
        nd_in.append(nf.name)
    L.append(f"def nativeTranslated : List String := [{', '.join(lean_str(n) for n in nd_in)}]")
    L.append(f"def nativeOutside : List (String × List String) := [{', '.join(f'({lean_str(n)}, [{chr(44).join(lean_str(c) for c in cs)}])' for n, cs in nd_out)}]")
    L.append("")
    L.append("/-- The translated functions by ACL2 name, for the term evaluator and the interpreter. -/")
    L.append("def fnTable : Std.HashMap String (List Val → Option Val) := Std.HashMap.ofList [")
    rows = []
    for f in kept:
        vs = [f"a{i}" for i in range(len(f.formals))]
        pat = "[" + ", ".join(vs) + "]"
        call = f"{ident(f.name)}{' ' if vs else ''}{' '.join(vs)}"
        rows.append(f"  ({lean_str(f.name)}, fun (xs : List Val) => match xs with | {pat} => some ({call}) | _ => none)")
    L.append(",\n".join(rows))
    L.append("]")
    L.append("")
    L.append("def guardTable : Std.HashMap String (List Val → Option Val) := Std.HashMap.ofList [")
    rows = []
    for f in guards:
        vs = [f"a{i}" for i in range(len(f.formals))]
        pat = "[" + ", ".join(vs) + "]"
        call = f"{ident(f.name)}.guard{' ' if vs else ''}{' '.join(vs)}"
        rows.append(f"  ({lean_str(f.name)}, fun (xs : List Val) => match xs with | {pat} => some ({call}) | _ => none)")
    L.append(",\n".join(rows))
    L.append("]")
    L.append("")
    L.append("def fns : Fns := fun f args => match fnTable.get? f with")
    L.append("  | some g => g args")
    L.append("  | none => none")
    L.append("")
    L.append("/-- A function's guard on its arguments (`T` for a function with no stated guard). -/")
    L.append("def guardOf (f : String) (args : List Val) : Option Val := match guardTable.get? f with")
    L.append("  | some g => g args")
    L.append("  | none => if fnTable.contains f then some Val.t else none")
    L.append("")
    L.append(f"def refused : List String := [{', '.join(lean_str(r) for r in refused)}]")
    L.append(f"def dropped : List String := [{', '.join(lean_str(r) for r in dropped)}]")
    L.append(f"def translated : List String := [{', '.join(lean_str(f.name) for f in kept)}]")
    L.append("")
    L.append(f"end {ns}")
    L.append("")
    open(path, "w").write("\n".join(L))
    return len(kept), refused, dropped, len(guards)


# ---------------------------------------------------------------- kinds

def plist(xs):
    xs = list(xs)
    return {str(k): v for k, v in zip(xs[::2], xs[1::2])}


def tm(x):
    xs = as_list(x)
    if not (len(xs) == 2 and xs[0] == ":TERM"):
        die(f"expected (:TERM t), got {show(x)}")
    return term(xs[1])


def opt_tm(d, key):
    return f"(some {tm(d[key])})" if key in d and not is_nil(d[key]) else "none"


def codes(cs):
    if isinstance(cs, Atom) and cs == ":OTHERWISE":
        return "none"
    return "(some [" + ", ".join(val(c) for c in as_list(cs)) + "])"


def steps(xs):
    return "[" + ", ".join(step(s) for s in as_list(xs)) + "]"


def call(d):
    keys = [as_list(k) for k in as_list(d[":KEYS"])]
    return (f"⟨{lean_str(str(d[':OP']))}, [{', '.join(tm(a) for a in as_list(d[':ARGS']))}], "
            f"[{', '.join(f'({lean_str(str(k[0]))}, {tm(k[1])})' for k in keys)}]⟩")


def step(s):
    s = as_list(s)
    h = str(s[0])
    a = s[1:]
    if h == ":LET":
        return f"(.let_ {lean_str(str(a[0]))} {tm(a[1])})"
    if h == ":SET":
        return "(.set [" + ", ".join(f"({lean_str(str(as_list(p)[0]))}, {tm(as_list(p)[1])})" for p in a) + "])"
    if h == ":NEXT":
        return f"(.next {tm(a[0])})"
    if h == ":DO":
        d = plist(a)
        cases = []
        for c in as_list(d[":CASE"]):
            c = as_list(c)
            cases.append(f"({codes(c[0])}, {steps(List(c[1:]))})")
        when = f"(some {tm(d[':WHEN'])})" if not is_nil(d[":WHEN"]) else "none"
        return (f"(.do_ [{', '.join(lean_str(str(v)) for v in as_list(d[':VARS']))}] {call(d)} "
                f"{'true' if not is_nil(d[':ACCEPT-GIVEN']) else 'false'} "
                f"[{', '.join(val(c) for c in as_list(d[':ACCEPT']))}] {when} "
                f"[{', '.join(tm(e) for e in as_list(d[':ELSE']))}] [{', '.join(cases)}])")
    if h == ":ISSUE":
        d = plist(a)
        return f"(.issue {call(d)} {steps(d[':OK'])} {steps(d[':REFUSED'])})"
    if h == ":REPEAT":
        d = plist(a)
        return f"(.repeat_ {tm(d[':N'])} {steps(d[':STEPS'])} {tm(d[':UNTIL'])})"
    if h == ":WAKE-ROW":
        return f"(.wakeRow {tm(a[0])})"
    if h == ":IF":
        return f"(.if_ {tm(a[0])} {steps(a[1])} {steps(a[2])})"
    if h == ":COND":
        cl = []
        for c in a:
            c = as_list(c)
            cl.append(f"({tm(c[0])}, {steps(List(c[1:]))})")
        return f"(.cond [{', '.join(cl)}])"
    if h == ":CASE":
        arms = []
        for c in a[1:]:
            c = as_list(c)
            arms.append(f"({codes(c[0])}, {steps(List(c[1:]))})")
        return f"(.case_ {tm(a[0])} [{', '.join(arms)}])"
    if h == ":CHARGE":
        d = plist(a)
        return f"(.charge {opt_tm(d, ':BYTES')} {opt_tm(d, ':STEPS')} {opt_tm(d, ':DESCRIPTORS')} {opt_tm(d, ':RUNNABLE')})"
    if h == ":WAIT":
        if str(a[0]) != ":COMPLETION":
            die(f"wait {show(List(s))}")
        d = plist(a[1:])
        return f"(.wait {opt_tm(d, ':BYTES')} {opt_tm(d, ':STEPS')})"
    if h == ":PARK":
        wait = str(a[0]).lstrip(":")
        d = plist(a[1:])
        kind = f"(some {lean_str(str(d[':KIND']))})" if ":KIND" in d else "none"
        return f"(.park {lean_str(wait)} {opt_tm(d, ':ARG')} {kind} {opt_tm(d, ':STEPS')})"
    if h == ":STOP":
        d = plist(a[1:])
        return f"(.stop {lean_str(str(a[0]).lstrip(':'))} {opt_tm(d, ':STEPS')})"
    if h in (":HALT", ":IDLE", ":YIELD", ":WAKE", ":NOWAKE"):
        return "." + h[1:].lower()
    if h == ":GOTO":
        return f"(.goto {lean_str(str(a[0]))})"
    die(f"unknown step {show(List(s))}")


def arm(e):
    e = as_list(e)
    d = plist(e[1:])
    sig = as_list(d.get(":SIG", List([])))
    if sig:
        takes, returns, results = as_list(sig[0]), as_list(sig[1]), int(str(sig[2]))
        sigl = (f"some ⟨[{', '.join(lean_str(str(x)) for x in takes)}], "
                f"[{', '.join(lean_str(str(x)) for x in returns)}], {results}⟩")
    else:
        sigl = "none"
    return (f"{{ tag := {lean_str(str(e[0]))}, sig := {sigl}, from_ := [{', '.join(lean_str(str(x)) for x in as_list(d[':FROM']))}],\n"
            f"      onRefusal := {steps(d[':ON-REFUSAL'])},\n"
            f"      steps := {steps(d[':STEPS'])},\n"
            f"      fn := {lean_str(str(d[':FUNCTION']))} }}")


def coltype(k):
    if isinstance(k, List):
        if k[0] != ":ENUM":
            die(f"column kind {show(k)}")
        return f".enum {len(as_list(k[2]))}"
    w = {":U8": 8, ":U16": 16, ":U32": 32, ":LINK": 32, ":U60": 60, ":U64": 64, ":BOOL": 1}.get(str(k))
    if w is None:
        die(f"column kind {k}")
    return f".uw {w}"


def kind(e):
    e = as_list(e)
    d = plist(e[1:])
    cols = [as_list(c) for c in as_list(d[":COLUMNS"])]
    return (f"{{ name := {lean_str(str(e[0]))},\n"
            f"    childForm := {'true' if str(d[':FORM']) == ':CHILDREN' else 'false'},\n"
            f"    tuple := [{', '.join(lean_str(str(x)) for x in as_list(d[':TUPLE']))}],\n"
            f"    states := [{', '.join(lean_str(str(x)) for x in as_list(d[':STATES']))}],\n"
            f"    columns := [{', '.join(f'({lean_str(str(c[0]))}, {coltype(c[1])})' for c in cols)}],\n"
            f"    table := [{', '.join(lean_str(str(as_list(c)[0])) for c in as_list(d[':TABLE']))}],\n"
            f"    stops := [{', '.join(lean_str(str(x).lstrip(':')) for x in as_list(d[':STOPS']))}],\n"
            f"    subarms := [\n    {(',' + chr(10) + '    ').join(arm(a) for a in as_list(d[':SUBARMS']))}],\n"
            f"    arms := [\n    {(',' + chr(10) + '    ').join(arm(a) for a in as_list(d[':ARMS']))}],\n"
            f"    observes := [\n    {(',' + chr(10) + '    ').join(arm(a) for a in as_list(d[':OBSERVES']))}] }}")


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
            f"stobjsIn := {so(d[':STOBJS-IN'])}, stobjsOut := {so(d[':STOBJS-OUT'])}, answers := {answers} }}")


def emit_kinds(emb, registry_waits, path, ns, world_ns):
    kinds = [kind(k) for k in as_list(emb[":KINDS"])]
    ops = [op(o) for o in as_list(emb[":OPERATIONS"])]
    consts = [as_list(c) if isinstance(c, List) else c for c in as_list(emb[":CONSTANTS"])]
    cs = []
    for c in as_list(emb[":CONSTANTS"]):
        c = list(c)
        cs.append(f"({lean_str(str(c[0]))}, {int(str(c[2])) if len(c) == 3 else int(str(c[1]))})")
    waits = []
    for name, row in registry_waits:
        d = plist(row)
        park = f"(some {lean_str(str(d[':PARK']))})" if ":PARK" in d and not is_nil(d[":PARK"]) else "none"
        waits.append(f"{{ kind := {lean_str(str(d[':KIND']).lstrip(':'))}, park := {park} }}")
    L = []
    L.append("-- GENERATED by fn2/meta/emit/emit_embed.py from the world print-world.lisp printed.")
    L.append("-- Do not edit: change a declaration and re-emit (fn2/meta/emit/emit.sh).")
    L.append(f"-- {len(kinds)} kinds in child form, {len(ops)} declared operations, {len(waits)} wait kinds,")
    L.append(f"-- {len(cs)} constants.")
    L.append("import Fn2.Arms")
    L.append(f"import {world_ns}")
    L.append("")
    L.append("set_option maxRecDepth 100000")
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
    L.append("def consts : List (String × Int) := [" + ", ".join(cs) + "]")
    L.append("")
    L.append(f"def world : World := {{ kinds, ops, waits, consts, fns := {world_ns}.fns }}")
    L.append("")
    L.append(f"end {ns}")
    L.append("")
    open(path, "w").write("\n".join(L))
    return len(kinds), len(ops)


def main():
    src, world_out, kinds_out, ns = sys.argv[1:5]
    forms = read_all(open(src).read())
    top = as_list(forms[0])
    if str(top[0]) != ":FN2-WORLD":
        die("expected (:FN2-WORLD ...)")
    reg = {str(as_list(e)[0]): as_list(e)[1] for e in as_list(top[1])[1:]}
    emb = {str(as_list(e)[0]): as_list(e)[1] for e in as_list(top[2])[1:]}
    waits = [(r[0], List(as_list(r)[1:])) for r in as_list(reg.get(":WAITS", List([])))]
    world_ns = ns + "World"
    n, refused, dropped, ng = emit_world(emb, world_out, world_ns)
    nk, no = emit_kinds(emb, waits, kinds_out, ns + "Kinds", world_ns)
    print(f"EMBED functions={n} guards={ng} refused={refused} dropped={dropped} kinds={nk} operations={no}")


if __name__ == "__main__":
    main()
