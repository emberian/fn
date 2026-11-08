#!/usr/bin/env python3
"""Emit the shallow embedding of fn2's closed subset from the world ACL2 printed.

Input: the `(:embed ...)` part of the S-expression print-world.lisp writes. Outputs:

  WORLD/M.lean     every function of the closure as a Lean `def` over `Fn2.ACL2.Val` (its translated
                   ACL2 body, read term for term) and its guard as `F.guard`, in modules M split by
                   the kinds that reach each function and by call depth (`partition`); each module
                   carries its own dispatch trees `M.fnTree` and `M.guardTree`;
  WORLD/MKeys.lean each of M's names' `nameKey` (`F.key`), a module of names only;
  WORLD/MEqns.lean each function's row in M's trees (`F.find`, `F.gfind`), importing only M;
  WORLD/Index.lean each name's key to its module's number (`ix`), names only; IndexEqnsJ its entries;
  WORLD/Natives.lean  ACL2's definitions of the natives (`F.acl2`);
  WORLD.lean       the aggregate: the modules' trees by number and the dispatch `fns`, `guardOf`;
  KINDS.lean       the kinds declared in the step language, as `Fn2.Arms.Kind` terms (every
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
              `guardOf "F" [a0 ...] = some («F».guard a0 ...)`, each assembled from the name's
              key, its index entry and its module row (`Dispatch.via_eq`), split over the files
              given (PW3 rewrites by them instead of unfolding the dispatch).

A module whose text is unchanged is not rewritten, so a change to one kind's functions rebuilds
that kind's modules, the aggregate and what imports it; the other modules keep their traces.

Usage: emit_embed.py WORLD.sexp WORLD.lean KINDS.lean NAMESPACE [EQNS.lean ...]
"""
import hashlib
import os
import re
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from emit_lean import read_all, Atom, Str, List, show, as_list, is_nil, val, term, lean_str, is_lambda, die, ident, as_module  # noqa: E402

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


def subset(emb):
    """The translated functions: (kept, refused, natives, dropped, outside)."""
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
    return kept, refused, natives, dropped, outside


def has_guard(f):
    return not (is_nil(f.guard) or str(f.guard) == "T" or
                (isinstance(f.guard, List) and f.guard[0] == "QUOTE" and str(f.guard[1]) == "T"))


# ---------------------------------------------------------------- the world's modules
#
# The world is emitted as modules so that a change to one kind re-elaborates only its own
# functions, and independent functions elaborate in parallel. The call graph (bodies, measures,
# stated guards, emitted constraint terms) has no mutual recursion, so its dependency SCCs are
# single functions and it is a DAG. Each function is grouped by the set of kinds whose arms reach
# it: none (Rest), one (that kind's own module), or several (a shared band, by how many kinds
# reach it; the bands of many kinds are the shared primitive closure). A callee is reached by
# every kind that reaches its caller, so calls go from a group to itself or to a band of more
# kinds. Each group is then cut by call depth (longest call path to a leaf): a call goes to a
# smaller depth, so a run of depths is one module and a single depth may be split freely. The
# resulting module graph is acyclic by construction (and checked).

WORLD_CAP = 400
WORLD_CLASS = 60


def camel(kind):
    parts = [p for p in re.split(r"[^A-Za-z0-9]+", kind) if p]
    if parts and parts[0] == "FN2":
        parts = parts[1:]
    return "".join(p[:1].upper() + p[1:].lower() for p in parts) or "X"


def world_deps(kept, emb):
    """Each kept function's translated callees: body, measure, emitted guard, emitted constraint terms."""
    names = {f.name for f in kept}
    D = {}
    for f in kept:
        s = calls_of(f.body, set()) | calls_of(f.measure, set())
        if has_guard(f):
            s |= calls_of(f.guard, set())
        for c in f.constraint:
            cs = calls_of(c, set())
            if all(g in names or g in NATIVE or g in SPECIAL for g in cs):
                s |= cs
        D[f.name] = {g for g in s if g in names and g != f.name}
    return D


def kind_roots(emb):
    out = []
    for k in as_list(emb[":KINDS"]):
        k = as_list(k)
        d = plist(k[1:])
        roots = set()
        for key in (":SUBARMS", ":ARMS", ":OBSERVES"):
            for a in as_list(d[key]):
                roots.add(str(plist(as_list(a)[1:])[":FUNCTION"]))
        out.append((str(k[0]), roots))
    return out


def partition(kept, emb):
    """(module of each function, modules in import order, imports of each module)."""
    order = [f.name for f in kept]
    D = world_deps(kept, emb)
    # call depth (a stated guard may call a function defined after its own: guards follow every
    # definition in a module, so the depth is over the whole graph, not the definition order)
    depth = {}
    for n0 in order:
        stack = [n0]
        while stack:
            n = stack[-1]
            if n in depth:
                stack.pop()
                continue
            todo = [g for g in D[n] if g not in depth]
            if todo:
                if len(stack) > len(order):
                    die(f"a call cycle through {n}: the world is not a DAG")
                stack.extend(todo)
                continue
            depth[n] = 1 + max((depth[g] for g in D[n]), default=-1)
            stack.pop()
    reach = {n: set() for n in order}
    for kname, roots in kind_roots(emb):
        stack = [r for r in roots if r in reach]
        seen = set()
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            reach[x].add(kname)
            stack.extend(D[x])

    # the shared groups: each set of kinds reaching at least WORLD_CLASS functions is its own group
    # (named by its kinds, or by their count and a digest when there are many); the smaller sets
    # reached by the same number of kinds share one group. Two sets of the same size are never
    # caller and callee (a callee's set contains its caller's), so these groups are independent.
    sets = {}
    for n in order:
        sets.setdefault(frozenset(reach[n]), []).append(n)

    def group_of(r):
        if not r:
            return (0, "Rest")
        if len(r) == 1:
            return (1, "K" + camel(next(iter(r))))
        if len(sets[r]) < WORLD_CLASS:
            return (len(r), f"S{len(r)}")
        ks = sorted(r)
        if len(ks) <= 3:
            return (len(r), "S" + "".join(camel(k) for k in ks))
        return (len(r), f"S{len(r)}x" + hashlib.sha256(" ".join(ks).encode()).hexdigest()[:6])
    groups = {}
    for n in order:
        groups.setdefault(group_of(frozenset(reach[n])), []).append(n)
    mod_of = {}
    for g, members in groups.items():
        by_depth = {}
        for n in members:
            by_depth.setdefault(depth[n], []).append(n)
        band, lo = [], None

        def close(band, lo, hi):
            m = f"{g[1]}_d{lo}" if lo == hi else f"{g[1]}_d{lo}to{hi}"
            for n in band:
                mod_of[n] = m
        prev = None
        for d in sorted(by_depth):
            ns = by_depth[d]
            if len(ns) > WORLD_CAP:
                if band:
                    close(band, lo, prev)
                    band, lo = [], None
                k = -(-len(ns) // WORLD_CAP)
                for j in range(k):
                    for n in ns[j::k]:
                        mod_of[n] = f"{g[1]}_d{d}b{j}"
                prev = d
                continue
            if band and len(band) + len(ns) > WORLD_CAP:
                close(band, lo, prev)
                band, lo = [], None
            if lo is None:
                lo = d
            band.extend(ns)
            prev = d
        if band:
            close(band, lo, prev)
    imports = {}
    for n in order:
        m = mod_of[n]
        imports.setdefault(m, set())
        for c in D[n]:
            if mod_of[c] != m:
                imports[m].add(mod_of[c])
    # a topological order of the modules (callees first); a cycle is a defect of the grouping
    done, mods, onpath = set(), [], set()
    for m0 in sorted(imports):
        stack = [(m0, iter(sorted(imports[m0])))]
        if m0 in done:
            continue
        onpath.add(m0)
        while stack:
            m, it = stack[-1]
            for c in it:
                if c in onpath:
                    die(f"module cycle through {m} and {c}")
                if c not in done:
                    onpath.add(c)
                    stack.append((c, iter(sorted(imports[c]))))
                    break
            else:
                stack.pop()
                onpath.discard(m)
                done.add(m)
                mods.append(m)
    return mod_of, mods, imports, depth, reach


def chunked_ix(rows, tree):
    """A balanced `KeyIx` over (key, value) rows, cut into definitions of at most DISPATCH_CHUNK rows."""
    rows = sorted(rows)
    defs = []
    nchunks = [0]

    def node(lo, hi, sub):
        mid = (lo + hi) // 2
        return f"(.node {rows[mid][0]} {rows[mid][1]} {sub(lo, mid)} {sub(mid + 1, hi)})"

    def inner(lo, hi):
        return ".leaf" if lo >= hi else node(lo, hi, inner)

    def outer(lo, hi):
        if hi - lo > DISPATCH_CHUNK:
            return node(lo, hi, outer)
        n = f"{tree}.c{nchunks[0]}"
        nchunks[0] += 1
        defs.append(f"def {n} : KeyIx :=\n  {inner(lo, hi)}\n")
        return n
    return defs, outer(0, len(rows))


GEN = ["-- GENERATED by meta/emit/emit_embed.py from the world print-world.lisp printed.",
       "-- Do not edit: change a book and re-emit (meta/emit/emit.sh)."]


def write(path, lines, written, expose=False, import_all=()):
    """LINES as a module (`as_module`): public, its bodies exposed only when EXPOSE."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    text = as_module("\n".join(lines), expose, import_all)
    # a module whose text is unchanged is not rewritten, so its build trace stays as it was
    if not (os.path.exists(path) and open(path, newline='').read() == text):
        open(path, "w").write(text)
    written.add(os.path.abspath(path))


def header(ns, imports, opts=("set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
                              "set_option linter.unusedVariables false")):
    return GEN + [f"import {m}" for m in imports] + [""] + list(opts) + ["", f"namespace {ns}", "open Fn2.ACL2", ""]


def emit_world(emb, path, ns, eqn_paths):
    """The world as modules under PATH's directory (`PATH` minus `.lean`), the aggregate at PATH,
    and the dispatch equations at EQN_PATHS. Returns the counts."""
    kept, refused, natives, dropped, outside = subset(emb)
    names = {f.name for f in kept}
    by = {f.name: f for f in kept}
    mod_of, mods, imports, depth, reach = partition(kept, emb)
    ix_of = {m: i for i, m in enumerate(mods)}
    base = path[:-len(".lean")]
    pkg = ns  # module path of the aggregate equals its namespace (Fn2.Instances.LayerAWorld)
    written = set()
    guard_outside = [f.name for f in kept if has_guard(f) and calls_of(f.guard, set()) & outside]
    members = {m: [] for m in mods}
    for f in kept:
        members[mod_of[f.name]].append(f)
    attached = []
    fn_rows_all, guard_rows_all = [], []
    for m in mods:
        fs = members[m]
        L = header(ns, ["Fn2.ACL2.Val"] + [f"{pkg}.{c}" for c in sorted(imports[m])])
        L.insert(2, f"-- World module {m}: {len(fs)} functions.")
        for f in fs:
            emit_fn(f, names, L)
        gs = []
        for f in fs:
            if not has_guard(f) or f.name in guard_outside:
                continue
            binders = " ".join(f"({ident(v)} : Val)" for v in f.formals)
            L.append(f"def {ident(f.name)}.guard {binders}{' ' if binders else ''}: Val :=")
            L.append(f"  {shallow(f.guard, names)}")
            L.append("")
            gs.append(f)
        for f in fs:
            if not f.attachment:
                continue
            for i, c in enumerate(f.constraint):
                missing = sorted(g for g in calls_of(c, set()) if g not in names and g not in NATIVE and g not in SPECIAL)
                if missing:
                    L.append(f"-- {f.name}'s constraint, term {i}: calls {missing}, outside the translated closure")
                    L.append("")
                    continue
                vs = free_vars(c, [])
                binders = " ".join(f"({ident(v)} : Val)" for v in vs)
                L.append(f"/-- {f.name}'s constraint, term {i}: `{show(c)[:300]}` -/")
                L.append(f"def {ident(f.name)}.constraint{i} {binders}{' ' if binders else ''}: Val :=")
                L.append(f"  {shallow(c, names)}")
                L.append("")
            attached.append(f)
        fn_rows = [(f.name, [f"a{i}" for i in range(len(f.formals))]) for f in fs]
        fn_rows = [(n, vs, f"{ident(n)}{' ' if vs else ''}{' '.join(vs)}") for n, vs in fn_rows]
        g_rows = [(f.name, [f"a{i}" for i in range(len(f.formals))]) for f in gs]
        g_rows = [(n, vs, f"{ident(n)}.guard{' ' if vs else ''}{' '.join(vs)}") for n, vs in g_rows]
        fn_defs, fn_root = dispatch_tree(fn_rows, "dispatch", f"{m}.fnTree")
        gd_defs, gd_root = dispatch_tree(g_rows, "guardDispatch", f"{m}.guardTree")
        L.extend(fn_defs)
        L.append(f"def {m}.fnTree : Dispatch :=\n  {fn_root}")
        L.append("")
        L.extend(gd_defs)
        L.append(f"def {m}.guardTree : Dispatch :=\n  {gd_root}")
        L.append("")
        L += [f"end {ns}", ""]
        write(f"{base}/{m}.lean", L, written)
        # the module's names, their keys: a module of names only
        K = header(ns, ["Fn2.ACL2.Val"], ("set_option maxRecDepth 100000",))
        K.insert(2, f"-- The keys of world module {m}'s names (`nameKey`): rebuilt only when its names change.")
        for f in fs:
            K.append(f"theorem {ident(f.name)}.key : nameKey {lean_str(f.name)} = {name_key(f.name)} :=")
            K.append("  Nat.eq_of_beq_eq_true rfl")
        K += ["", f"end {ns}", ""]
        write(f"{base}/{m}Keys.lean", K, written)
        # each function's row in its module's trees: beside the module, importing only it
        E = header(ns, [f"{pkg}.{m}"], ("set_option maxRecDepth 100000",))
        E.insert(2, f"-- World module {m}'s rows: each function's (and stated guard's) entry in the module's tree.")
        # the row's match, stated whole so the dispatch equation is assembled without unfolding
        # (an elaborated `rfl` against a postponed `?g args` opened the called function's body)
        for n, vs, call in fn_rows:
            bs = " ".join(f"({v} : Val)" for v in vs)
            E.append(f"theorem {ident(n)}.find : {m}.fnTree.find {name_key(n)} = some {ident(n)}.dispatch := by rfl")
            E.append(f"theorem {ident(n)}.row {bs}{' ' if bs else ''}: {ident(n)}.dispatch [{', '.join(vs)}] = some ({call}) := by rfl")
        for n, vs, call in g_rows:
            bs = " ".join(f"({v} : Val)" for v in vs)
            E.append(f"theorem {ident(n)}.gfind : {m}.guardTree.find {name_key(n)} = some {ident(n)}.guardDispatch := by rfl")
            E.append(f"theorem {ident(n)}.grow {bs}{' ' if bs else ''}: {ident(n)}.guardDispatch [{', '.join(vs)}] = some ({call}) := by rfl")
        E += ["", f"end {ns}", ""]
        write(f"{base}/{m}Eqns.lean", E, written, import_all=[f"{pkg}.{m}"])
        fn_rows_all += fn_rows
        guard_rows_all += g_rows
    # the index: each name's key to its module's number (names only)
    nix = len(eqn_paths) or 1
    I = header(ns, ["Fn2.ACL2.Val"], ("set_option maxRecDepth 100000",))
    I.insert(2, f"-- The world's index: {len(kept)} names to their modules' numbers ({len(mods)} modules).")
    ix_defs, ix_root = chunked_ix([(name_key(f.name), ix_of[mod_of[f.name]]) for f in kept], "ix")
    I.extend(ix_defs)
    I.append(f"def ix : KeyIx :=\n  {ix_root}")
    I.append("")
    I.append("/-- The modules in index order. -/")
    I.append(f"def worldModules : List String := [{', '.join(lean_str(m) for m in mods)}]")
    I.append("")
    I.append(f"def guardOutside : List String := [{', '.join(lean_str(n) for n in guard_outside)}]")
    I += ["", f"end {ns}", ""]
    write(f"{base}/Index.lean", I, written, expose=True)
    for j in range(nix):
        X = header(ns, [f"{pkg}.Index"], ("set_option maxRecDepth 100000",))
        X.insert(2, f"-- The index entries, part {j + 1} of {nix}.")
        for f in kept[j::nix]:
            X.append(f"theorem {ident(f.name)}.ix : ix.find {name_key(f.name)} = some {ix_of[mod_of[f.name]]} := rfl")
        X += ["", f"end {ns}", ""]
        write(f"{base}/IndexEqns{j + 1}.lean", X, written)
    # ACL2's definitions of the natives, where they stay inside the subset: `«F».acl2`, with every
    # call of another native going to its Lean implementation (the statement is per native)
    nd_in, nd_out, nd_lines, nd_imports = [], [], [], set()
    for e in as_list(emb.get(":NATIVE-DEFINITIONS", List([]))):
        nf = Fn(as_list(e))
        calls = calls_of(nf.body, set()) | calls_of(nf.measure, set())
        outside_calls = sorted(c for c in calls if c not in names and c not in NATIVE and c not in SPECIAL
                               and c != nf.name)
        outside_calls = sorted(set(outside_calls) | {INTEGER_DOMAIN[c] for c in calls if c in INTEGER_DOMAIN
                                                       and nf.name not in INTEGER_DOMAIN})
        if outside_calls or (nf.recursive and nf.recursive != [nf.name]) or nf.name in SPECIAL:
            nd_out.append((nf.name, outside_calls))
            continue
        nd_imports |= {mod_of[c] for c in calls if c in names}
        emit_native_def(nf, names, nd_lines)
        nd_in.append(nf.name)
    N = header(ns, ["Fn2.ACL2.Val"] + [f"{pkg}.{m}" for m in sorted(nd_imports)])
    N.append("/-! ## ACL2's definitions of the natives, translated (`F.acl2`): Fn2.ACL2.Faithful states")
    N.append("that each native agrees with its definition. A definition that leaves the subset (through the")
    N.append("reciprocal, `NUMERATOR`, `REALPART` ...) is named in `nativeOutside`. -/")
    N.append("")
    N += nd_lines
    N.append(f"def nativeTranslated : List String := [{', '.join(lean_str(n) for n in nd_in)}]")
    N.append(f"def nativeOutside : List (String × List String) := [{', '.join(f'({lean_str(n)}, [{chr(44).join(lean_str(c) for c in cs)}])' for n, cs in nd_out)}]")
    N += ["", f"end {ns}", ""]
    write(f"{base}/Natives.lean", N, written)
    # the aggregate: the modules' trees by number, the dispatch through the index
    A = list(GEN)
    A.append(f"-- {len(kept)} functions translated in {len(mods)} modules, {len(natives)} natives, refused {refused},")
    A.append(f"-- dropped as callers of a refused function {dropped}.")
    A += [f"import {pkg}.{m}" for m in mods] + [f"import {pkg}.Index", f"import {pkg}.Natives", ""]
    A += ["set_option maxRecDepth 100000", "", f"namespace {ns}", "open Fn2.ACL2", ""]
    A.append("/-- Each world module's function tree, by its index number. -/")
    A.append("def fnTrees : Nat → Dispatch")
    A += [f"  | {i} => {m}.fnTree" for i, m in enumerate(mods)]
    A.append("  | _ => .leaf")
    A.append("")
    A.append("/-- Each world module's guard tree, by its index number. -/")
    A.append("def guardTrees : Nat → Dispatch")
    A += [f"  | {i} => {m}.guardTree" for i, m in enumerate(mods)]
    A.append("  | _ => .leaf")
    A.append("")
    A.append("/-- The translated functions by ACL2 name, for the term evaluator and the interpreter. -/")
    A.append("def fns : Fns := Dispatch.via ix fnTrees")
    A.append("")
    A.append("/-- A function's guard on its arguments (`T` for a function with no stated guard). -/")
    A.append("def guardOf (f : String) (args : List Val) : Option Val :=")
    A.append("  Dispatch.guardVia ix guardTrees fnTrees guardOutside f args")
    A.append("")
    A.append(f"def attached : List (String × String) := [{', '.join(f'({lean_str(f.name)}, {lean_str(f.attachment)})' for f in attached)}]")
    A.append(f"def refused : List String := [{', '.join(lean_str(r) for r in refused)}]")
    A.append(f"def dropped : List String := [{', '.join(lean_str(r) for r in dropped)}]")
    A.append(f"def translated : List String := [{', '.join(lean_str(f.name) for f in kept)}]")
    A += ["", f"end {ns}", ""]
    write(path, A, written, expose=True)
    # the dispatch equations: each assembled from the name's key, its index entry and its row
    eqs = []
    for name, vs, call in fn_rows_all:
        bs = " ".join(f"({v} : Val)" for v in vs)
        eqs.append(f"@[fn2_dispatch] theorem {ident(name)}.fns_eq {bs}{' ' if bs else ''}:\n"
                   f"    fns {lean_str(name)} [{', '.join(vs)}] = some ({call}) :=\n"
                   f"  (Dispatch.via_eq (T := fnTrees) _ {ident(name)}.key {ident(name)}.ix {ident(name)}.find).trans\n"
                   f"    ({ident(name)}.row {' '.join(vs)})")
    for name, vs, call in guard_rows_all:
        bs = " ".join(f"({v} : Val)" for v in vs)
        eqs.append(f"@[fn2_dispatch] theorem {ident(name)}.guard_eq {bs}{' ' if bs else ''}:\n"
                   f"    guardOf {lean_str(name)} [{', '.join(vs)}] = some ({call}) :=\n"
                   f"  (Dispatch.guardVia_eq (G := guardTrees) _ {ident(name)}.key {ident(name)}.ix {ident(name)}.gfind).trans\n"
                   f"    ({ident(name)}.grow {' '.join(vs)})")
    n = len(eqn_paths)
    eq_imports = ([pkg] + [f"{pkg}.{m}Keys" for m in mods] + [f"{pkg}.{m}Eqns" for m in mods]
                  + [f"{pkg}.IndexEqns{j + 1}" for j in range(nix)] + ["Fn2.ACL2.SimpAttr"])
    for i, ep in enumerate(eqn_paths):
        L = ["-- GENERATED by meta/emit/emit_embed.py: the dispatch equations (PW3), part "
             f"{i + 1} of {n}.", "-- Do not edit: change a book and re-emit (meta/emit/emit.sh)."]
        L += [f"import {m}" for m in eq_imports]
        L += ["", "set_option maxRecDepth 100000", "set_option linter.unusedVariables false", "",
              f"namespace {ns}", "open Fn2.ACL2", ""]
        L.extend(eqs[i::n])
        L.extend(["", f"end {ns}", ""])
        write(ep, L, written)
    # the modules of an earlier emission that this one did not write
    for fn in os.listdir(base):
        p = os.path.abspath(os.path.join(base, fn))
        if fn.endswith(".lean") and p not in written:
            os.remove(p)
    return len(kept), refused, dropped, len(guard_rows_all), len(eqs), mods


# ---------------------------------------------------------------- the world bodies a consumer opens
#
# A world module's bodies are not exposed (`as_module`): an importer sees each function's type, so
# a change to a body rebuilds that module, its rows, and only the files that `import all` it. A file
# that unfolds world bodies (by `rfl`, `decide`, `simp only [F]`) states what it opens in a block
# among its imports, and the emitter writes the block's `import all` lines: every module holding a
# function of the closure (callees included) of what the block names:
#   -- BEGIN world bodies (emit_embed.py): kinds FN2-CURSOR; names FN2-MACHINES-READY-PREV; natives; scan
#   import all Fn2.Instances.LayerAWorld.KCursor_d0to20
#   -- END world bodies
# `kinds K ..` every function a kind's arms reach; `names F ..` those functions; `prefixes P ..` every
# function whose name starts with one; `accessors K ..` each kind's column getters and setters (its
# own, and the directory's in `fn2-machines` for READY-PREV, READY-NEXT, WAIT-REASON); `natives` the module of
# ACL2's native definitions and their callees; `scan` every `«F»` the file itself names.

DIRECTORY_FIELDS = ("READY-PREV", "READY-NEXT", "WAIT-REASON")
WB = re.compile(r"^-- BEGIN world bodies \(emit_embed\.py\): (.*)\n(?:import all .*\n)*-- END world bodies$", re.M)


def world_layout(emb):
    """What the blocks are computed from: the modules, each function's module, callees and kinds."""
    kept = subset(emb)[0]
    mod_of, mods, imports, depth, reach = partition(kept, emb)
    D = world_deps(kept, emb)
    native_callees = set()
    for e in as_list(emb.get(":NATIVE-DEFINITIONS", List([]))):
        nf = Fn(as_list(e))
        native_callees |= {c for c in calls_of(nf.body, set()) | calls_of(nf.measure, set()) if c in mod_of}
    columns = {}
    for k in as_list(emb[":KINDS"]):
        k = as_list(k)
        columns[str(k[0])] = [str(as_list(c)[0]) for c in as_list(plist(k[1:])[":COLUMNS"])]
    return dict(mod_of=mod_of, mods=mods, D=D, reach=reach, native_callees=native_callees, columns=columns)


def world_bodies(text, layout, pkg):
    """TEXT with its world-bodies block (if any) written from LAYOUT."""
    m = WB.search(text)
    if not m:
        return text
    spec = m.group(1).strip()
    rest = text[:m.start()] + text[m.end():]
    mod_of, D, reach = layout["mod_of"], layout["D"], layout["reach"]
    roots, extra = set(), []
    for clause in (c.split() for c in spec.split(";")):
        if not clause:
            continue
        if clause[0] == "kinds":
            ks = set(clause[1:])
            roots |= {f for f, r in reach.items() if r & ks}
        elif clause[0] == "names":
            missing = [n for n in clause[1:] if n not in mod_of]
            if missing:
                die(f"world bodies: {missing} are not translated functions")
            roots |= set(clause[1:])
        elif clause[0] == "accessors":
            for kn in clause[1:]:
                for c in layout["columns"][kn]:
                    own = kn if c not in DIRECTORY_FIELDS else "FN2-MACHINES"
                    roots |= {n for n in (f"{own}-{c}", f"{own}-SET-{c}") if n in mod_of}
        elif clause[0] == "prefixes":
            roots |= {f for f in mod_of if any(f.startswith(x) for x in clause[1:])}
        elif clause[0] == "natives":
            roots |= layout["native_callees"]
            extra.append(f"{pkg}.Natives")
        elif clause[0] == "scan":
            roots |= {n for n in re.findall(r"«([^»]+)»", rest) if n in mod_of}
        else:
            die(f"world bodies: unknown clause {clause[0]!r} in {spec!r}")
    seen, stack = set(), list(roots)
    while stack:
        f = stack.pop()
        if f not in seen:
            seen.add(f)
            stack.extend(D[f])
    used = {mod_of[f] for f in seen}
    lines = [f"-- BEGIN world bodies (emit_embed.py): {spec}"]
    lines += [f"import all {pkg}.{x}" for x in layout["mods"] if x in used] + [f"import all {x}" for x in extra]
    lines.append("-- END world bodies")
    return text[:m.start()] + "\n".join(lines) + text[m.end():]


def refresh_world_bodies(fn2_dir, layout, pkg, skip=()):
    """Rewrite the world-bodies block of every Lean file under FN2_DIR (the world's own modules aside)."""
    base = os.path.join(fn2_dir, *pkg.split(".")[1:])
    for d, _, fs in os.walk(fn2_dir):
        if os.path.abspath(d).startswith(os.path.abspath(base) + os.sep) or os.path.abspath(d) == os.path.abspath(base):
            continue
        for f in fs:
            p = os.path.join(d, f)
            if not f.endswith(".lean") or os.path.abspath(p) in skip:
                continue
            s = open(p, newline='').read()
            t = world_bodies(s, layout, pkg)
            if t != s:
                open(p, "w", newline='').write(t)


def world_imports(path, ns):
    """The generated modules of the world at PATH whose facts assemble a dispatch equation."""
    base = path[:-len(".lean")]
    fs = sorted(f[:-5] for f in os.listdir(base) if f.endswith("Keys.lean") or f.endswith("Eqns.lean")
                or re.fullmatch(r"IndexEqns\d+\.lean", f))
    return [f"{ns}.{f}" for f in fs]


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


# ---------------------------------------------------------------- kinds

def plist(xs):
    xs = list(xs)
    return {str(k): v for k, v in zip(xs[::2], xs[1::2])}


def arm(e, rc="{}", cc=""):
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
            f"      fn := {lean_str(str(d[':FUNCTION']))}, refuse := {rc}{cc} }}")


def refuse_ctx(cols, subarms):
    # the word field: the first of WORD, REPLY, REASON among the kind's columns; a REFUSE sub-arm or not
    names = [str(c[0]) for c in cols]
    field = next((f for f in ("WORD", "REPLY", "REASON") if f in names), None)
    sub = any(str(as_list(a)[0]) == "REFUSE" for a in subarms)
    fl = "none" if field is None else f"(some {lean_str(field)})"
    return f"{{ field := {fl}, sub := {'true' if sub else 'false'} }}"


def contains_atom(tree, atom):
    return any(contains_atom(x, atom) for x in tree) if isinstance(tree, List) else str(tree) == atom


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
    # The independent reader expands :commit. Export declaration facts only;
    # never feed it the generator's already-expanded body.
    cc = ""
    if contains_atom(e, ":COMMIT"):
        cc = (", commit := { phases := [" + ", ".join(lean_str(str(p)) for p in as_list(d[":STATES"]))
              + "], tickets := [" + ", ".join(lean_str(str(c[0])) for c in cols if str(c[1]) == ":U60") + "] }")
    # The generator expands subarms with a NIL tag, even when their name
    # happens to equal a phase. Run arms/handlers use their declared tag.
    subcc = cc.replace("commit := {", 'commit := { tag := "NIL",')
    return (f"{{ name := {lean_str(str(e[0]))},\n"
            f"    childForm := {'true' if str(d[':FORM']) == ':CHILDREN' else 'false'},\n"
            f"    tuple := [{', '.join(lean_str(str(x)) for x in as_list(d[':TUPLE']))}],\n"
            f"    states := [{', '.join(lean_str(str(x)) for x in as_list(d[':STATES']))}],\n"
            f"    phases := [{', '.join(f'({lean_str(str(as_list(p)[0]))}, {as_list(p)[1]})' for p in as_list(d[':PHASES']))}],\n"
            f"    columns := [{', '.join(f'({lean_str(str(c[0]))}, {coltype(c[1])})' for c in cols)}],\n"
            f"    table := [{', '.join(lean_str(str(as_list(c)[0])) for c in as_list(d[':TABLE']))}],\n"
            f"    stops := [{', '.join(lean_str(str(x).lstrip(':')) for x in as_list(d[':STOPS']))}],\n"
            f"    links := [{', '.join(links)}],\n"
            f"    subarms := [\n    {(',' + chr(10) + '    ').join(arm(a, rc, subcc) for a in as_list(d[':SUBARMS']))}],\n"
            f"    arms := [\n    {(',' + chr(10) + '    ').join(arm(a, rc, cc) for a in as_list(d[':ARMS']))}],\n"
            f"    observes := [\n    {(',' + chr(10) + '    ').join(arm(a, rc, cc) for a in as_list(d[':OBSERVES']))}] }}")


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
        v = alist_value(c)
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
    open(path, "w").write(as_module("\n".join(L)))
    return len(kinds), len(ops)


def alist_value(row):
    """CDR of a printed association, including list-valued constants."""
    if len(row) == 3 and str(row[1]) == ".":
        return row[2]
    return List(row[1:])


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--world-bodies":
        # after every emitter: fill the world-bodies blocks of the Lean files under FN2_DIR
        src, fn2_dir = sys.argv[2:4]
        top = as_list(read_all(open(src, newline='').read())[0])
        emb = {str(as_list(e)[0]): as_list(e)[1] for e in as_list(top[2])[1:]}
        refresh_world_bodies(fn2_dir, world_layout(emb), "Fn2.Instances.LayerAWorld")
        return
    if len(sys.argv) > 1 and sys.argv[1] == "--served-certificate":
        from emit_served_certificate import generate
        generate(sys.argv[2])
        return
    if len(sys.argv) > 1 and sys.argv[1] == "--certificate":
        from emit_certificate import main as certificate_main
        certificate_main(*sys.argv[2:])
        return
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
    n, refused, dropped, ng, ne, mods = emit_world(emb, world_out, world_ns, eqn_outs)
    # the consumers' world-bodies blocks (meta/Fn2, the directory above Instances)
    refresh_world_bodies(os.path.dirname(os.path.dirname(os.path.abspath(world_out))), world_layout(emb), world_ns)
    nk, no = emit_kinds(emb, waits, kinds_out, ns + "Kinds", world_ns, reg_links)
    print(f"EMBED functions={n} guards={ng} modules={len(mods)} refused={refused} dropped={dropped} kinds={nk} operations={no} equations={ne}")


if __name__ == "__main__":
    main()
