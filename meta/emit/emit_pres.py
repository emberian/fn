#!/usr/bin/env python3
"""Emit projection-preservation lemmas over the shallow embedding (Fn2.Instances.LayerAWorld).

A *projection* of a value is a path of literal `NTH` indices, outermost first: `P [n1, n2] v` is
`(NTH n2 (NTH n1 v))`. For a translated function F and a path p, the analysis here reads F's
translated body symbolically (variables, `NTH`/`MV-NTH`, `UPDATE-NTH` and `CONS` at literal
indices, `IF`, `LAMBDA`, calls of other translated functions) and finds, where it can, a formal x
and a path q with `P p (F xs) = P q x` on every argument. Each such fact is emitted as a Lean
theorem proved by unfolding F once and rewriting with its callees' facts and the list lemmas of
Fn2.ACL2.Pres, so the analysis is never trusted: a wrong claim fails the build.

Queries, the facts the contracts consume:
  * every attached function (print-world.lisp meta-body) whose constraint frames children of
    `fn2-core` (`(EQUAL (C (MV-NTH k (F ...))) (C FN2-CORE))`): the path [k, i] for each such child i;
  * every operation without a `:child` that a served core-form kind (`FN2-CNS`, `FN2-CONN`) calls
    and that returns `fn2-core`:
    the kind's `PHASE` column, the path [r, i, 0] (r the core's result position, i the kind's
    child, 0 its first column).
Recursive functions are not read (their fuel's base case is outside the facts): a query reaching
one fails, and the operation is listed as uncovered.

Usage: emit_pres.py WORLD-PROBE.sexp PRES.lean WORLD-NAMESPACE [PHASE.lean]
"""
import os
import re
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from emit_lean import read_all, Atom, Str, List, as_list, is_nil, lean_str, is_lambda, ident, show  # noqa: E402
from emit_embed import Fn, name_key, subset, partition  # noqa: E402

sys.setrecursionlimit(100000)


def lit_index(t):
    if isinstance(t, List) and len(t) == 2 and t[0] == "QUOTE":
        a = str(t[1])
        if a.isdigit():
            return int(a)
    return None


class Analysis:
    def __init__(self, fns):
        self.fns = fns
        self.abs = {}          # F -> abstract body
        self.summ = {}         # (F, path) -> (i, q, used) | None
        self.busy = set()
        self.lemmas = []       # (F, path, i, q, used), callees first
        self.qmemo = {}

    def absval(self, t, env):
        if isinstance(t, List):
            if len(t) == 0 or t[0] == "QUOTE":
                return ("unk",)
            if is_lambda(t[0]):
                formals = [str(v) for v in as_list(t[0][1])]
                vals = [self.absval(a, env) for a in t[1:]]
                return self.absval(t[0][2], dict(zip(formals, vals)))
            f = str(t[0])
            args = list(t[1:])
            if f == "IF":
                return ("if", self.absval(args[1], env), self.absval(args[2], env))
            if f == "RETURN-LAST":
                return self.absval(args[2], env)
            if f in ("NTH", "MV-NTH"):
                n = lit_index(args[0])
                return ("unk",) if n is None else ("nth", n, self.absval(args[1], env))
            if f == "UPDATE-NTH":
                n = lit_index(args[0])
                return ("unk",) if n is None else ("upd", n, self.absval(args[1], env), self.absval(args[2], env))
            if f == "CONS":
                return ("cons", self.absval(args[0], env), self.absval(args[1], env))
            if f in self.fns:
                return ("call", f, tuple(self.absval(a, env) for a in args))
            return ("unk",)
        a = str(t)
        return env.get(a, ("unk",))

    def body(self, f):
        if f not in self.abs:
            fn = self.fns[f]
            self.abs[f] = self.absval(fn.body, {v: ("arg", i) for i, v in enumerate(fn.formals)})
        return self.abs[f]

    def q(self, node, path):
        key = (id(node), path)
        if key in self.qmemo:
            return self.qmemo[key][1]
        r = self.q1(node, path)
        self.qmemo[key] = (node, r)   # keep node alive so its id is not reused
        return r

    def q1(self, node, path):
        tag = node[0]
        if tag == "arg":
            return (node[1], path, frozenset())
        if tag == "nth":
            return self.q(node[2], (node[1],) + path)
        if tag == "cons":
            if not path:
                return None
            return self.q(node[1], path[1:]) if path[0] == 0 else self.q(node[2], (path[0] - 1,) + path[1:])
        if tag == "upd":
            if not path:
                return None
            return self.q(node[2], path[1:]) if path[0] == node[1] else self.q(node[3], path)
        if tag == "if":
            a = self.q(node[1], path)
            if a is None:
                return None
            b = self.q(node[2], path)
            if b is None or a[:2] != b[:2]:
                return None
            return (a[0], a[1], a[2] | b[2])
        if tag == "call":
            s = self.summary(node[1], path)
            if s is None:
                return None
            j, p2, _ = s
            r = self.q(node[2][j], p2)
            if r is None:
                return None
            return (r[0], r[1], r[2] | {(node[1], path)})
        return None

    def qcons(self, node):
        """(used) when the node is a cons on every path, else None."""
        tag = node[0]
        if tag == "cons":
            return frozenset()
        if tag == "if":
            a = self.qcons(node[1])
            b = None if a is None else self.qcons(node[2])
            return None if b is None else a | b
        if tag == "call":
            return None if self.summary_cons(node[1]) is None else frozenset({(node[1], "consp")})
        return None

    def summary_cons(self, f):
        key = (f, "consp")
        if key in self.summ:
            return self.summ[key]
        fn = self.fns[f]
        if fn.recursive or key in self.busy:
            return None
        self.busy.add(key)
        r = self.qcons(self.body(f))
        self.busy.discard(key)
        self.summ[key] = r
        if r is not None:
            self.lemmas.append((f, "consp", None, None, r))
        return r

    def summary_rec(self, f, path):
        """A countdown loop (measure `(NFIX V)`, every recursive call passing `(BINARY-+ '-1 (NFIX V))`
        at V): a candidate fact is assumed at the recursive calls and checked over the body; the Lean
        proof is by induction on the fuel, the measure decreasing at each call (Fn2.ACL2.Fuel)."""
        key = (f, path)
        fn = self.fns[f]
        mi = countdown_formal(fn)
        if mi is None:
            self.summ[key] = None
            return None
        cands = [(i, path[1:]) for i in range(len(fn.formals)) if path] + \
                [(i, path) for i in range(len(fn.formals))]
        for cand in cands:
            self.summ[key] = (cand[0], cand[1], frozenset())
            self.qmemo.clear()
            r = self.q(self.body(f), path)
            if r is not None and r[:2] == cand:
                used = r[2] - {key}
                self.summ[key] = (cand[0], cand[1], used)
                self.lemmas.append((f, path, cand[0], cand[1], used | {("REC", mi)}))
                return self.summ[key]
            del self.summ[key]
            self.qmemo.clear()
        self.summ[key] = None
        return None

    def summary(self, f, path):
        key = (f, path)
        if key in self.summ:
            return self.summ[key]
        fn = self.fns[f]
        if fn.recursive:
            return self.summary_rec(f, path)
        if key in self.busy:
            return None
        self.busy.add(key)
        r = self.q(self.body(f), path)
        self.busy.discard(key)
        self.summ[key] = r
        if r is not None:
            self.lemmas.append((f, path, r[0], r[1], r[2]))
        return r


def countdown_formal(fn):
    m = fn.measure
    if not (isinstance(m, List) and len(m) == 2 and str(m[0]) == "NFIX" and str(m[1]) in fn.formals):
        return None
    v = str(m[1])
    mi = fn.formals.index(v)
    want = show(List([Atom("BINARY-+"), List([Atom("QUOTE"), Atom("-1")]), List([Atom("NFIX"), Atom(v)])]))
    ok = [True]

    def walk(t):
        if isinstance(t, List) and len(t):
            if t[0] == "QUOTE":
                return
            if is_lambda(t[0]):
                walk(t[0][2])
            elif str(t[0]) == fn.name:
                if len(t) != len(fn.formals) + 1 or show(t[1 + mi]) != want:
                    ok[0] = False
            for a in t[1:]:
                walk(a)
    walk(fn.body)
    return mi if ok[0] else None


def proj(path, e):
    for n in path:
        e = f"(Native.nth (Val.int {n}) {e})"
    return e


def lemma_name(f, path):
    if path == "consp":
        return f"{ident(f)}.consp"
    return f"{ident(f)}.pres_{'_'.join(str(n) for n in path) or 'self'}"


# the served core-form kinds whose arms' phases the contracts check (Fn2.Arms.ServedCore)
SERVED = ("FN2-CNS", "FN2-CONN")

SIMP = ("Pres.nth_ite, Pres.nth_cons_zero, Pres.nth_cons_succ, Pres.nth_upd_same, Pres.nth_upd_ne, "
        "ite_self, Int.reduceSub")


def main():
    src, out, ns = sys.argv[1:4]
    world = read_all(open(src).read())[0]
    emb = next(p for p in as_list(world)[1:] if str(as_list(p)[0]) == ":EMBED")
    d = {str(as_list(e)[0]): as_list(e)[1] for e in as_list(emb)[1:]}
    fns = {f.name: f for f in (Fn(as_list(e)) for e in as_list(d[":FUNCTIONS"]))}
    ops = {}
    for o in as_list(d[":OPERATIONS"]):
        o = as_list(o)
        ops[str(o[0])] = dict(zip([str(k) for k in o[1::2]], o[2::2]))
    tup = [str(c) for c in as_list(d[":CORE-TUPLE"])]
    A = Analysis(fns)
    roots = []   # (what, F, path, ok)
    # attached functions: the constraint's frame conjuncts over fn2-core's children
    acc = {}
    for f in fns.values():
        if f.name.startswith("FN2-CORE-") and len(f.formals) == 1 and f.formals[0] == "FN2-CORE":
            # a child accessor (nth i fn2-core)
            b = f.body
            while isinstance(b, List) and str(b[0]) == "RETURN-LAST":
                b = b[3]
            if isinstance(b, List) and str(b[0]) == "NTH" and lit_index(b[1]) is not None:
                acc[f.name] = lit_index(b[1])
    for f in fns.values():
        if not f.attachment:
            continue
        for c in f.constraint:
            for k, child in frame_claims(c, f.name, acc):
                roots.append((f"{f.name} frames {child}", f.name, (k, acc[child])))
        A.summary_cons(f.name)
    # core-only operations of the core-form kinds: their PHASE column
    opq = []
    for kd in as_list(d[":KINDS"]):
        kd = as_list(kd)
        kn = str(kd[0]); kp = dict(zip([str(x) for x in kd[1::2]], kd[2::2]))
        if str(kp[":FORM"]) != ":CORE" or kn not in tup or kn not in SERVED:
            continue
        used = set()
        for sec in (":SUBARMS", ":ARMS", ":OBSERVES"):
            ops_in(kp[sec], ops, used)
        for o in sorted(used):
            row = ops[o]
            if not is_nil(row.get(":CALLEE", "NIL")) or is_nil(row.get(":CORE-FORMALS", "NIL")):
                continue
            so = [str(x) for x in as_list(row[":CORE-STOBJS-OUT"])]
            if "FN2-CORE" not in so:
                continue
            r = so.index("FN2-CORE")
            path = (r, tup.index(kn), 0) if len(so) > 1 else (tup.index(kn), 0)
            roots.append((f"{o} keeps {kn} PHASE", o, path))
            opq.append((o, kn, r if len(so) > 1 else 0, tup.index(kn), path))
    report = []
    for what, f, path in roots:
        s = A.summary(f, path) if f in fns else None
        report.append((what, f, path, s))
    L = ["-- GENERATED by meta/emit/emit_pres.py from the world print-world.lisp printed.",
         "-- Do not edit: change a book and re-emit (meta/emit/emit.sh).",
         f"-- {len(A.lemmas)} projection facts; queries {sum(1 for r in report if r[3])} of {len(report)} answered.",
         "import Fn2.ACL2.Pres", "import Fn2.ACL2.Fuel", f"import {ns}", "",
         "set_option maxHeartbeats 0", "set_option maxRecDepth 100000", "set_option linter.unusedVariables false", "set_option linter.unusedSimpArgs false", "",
         f"namespace {ns}", "open Fn2.ACL2", ""]
    for f, path, i, q, used in A.lemmas:
        fn = fns[f]
        xs = " ".join(ident(v) for v in fn.formals)
        binders = " ".join(f"({ident(v)} : Val)" for v in fn.formals)
        if path == "consp":
            callee = ", ".join(lemma_name(g, p) for g, p in sorted(used, key=str))
            L.append(f"theorem {lemma_name(f, path)} {binders} :")
            L.append(f"    Prim.consp ({ident(f)}{' ' if xs else ''}{xs}) = Val.t := by")
            L.append(f"  simp only [{ident(f)}, Pres.consp_ite, Pres.consp_cons, ite_self{', ' + callee if callee else ''}]")
            L.append("")
            continue
        lhs = proj(path, f"({ident(f)}{' ' if xs else ''}{xs})")
        rhs = proj(q, ident(fn.formals[i]))
        rec = [u for u in used if u[0] == "REC"]
        used = {u for u in used if u[0] != "REC"}
        callee = ", ".join(lemma_name(g, p) for g, p in sorted(used, key=str))
        if rec:
            mv = ident(fn.formals[rec[0][1]])
            go = f"{lemma_name(f, path)}_go"
            simp = f"{SIMP}{', ' + callee if callee else ''}"
            L.append(f"theorem {go} (fuel : Nat) : ∀ {binders}, («NFIX» {mv}).nfix < fuel →")
            L.append(f"    {proj(path, f'({ident(f)}.go fuel {xs})')} = {rhs} := by")
            L.append(f"  induction fuel with")
            L.append(f"  | zero => intro {' '.join('_' for _ in fn.formals)} h; omega")
            L.append(f"  | succ n ih =>")
            L.append(f"    intro {xs} hf")
            L.append(f"    simp (config := {{ decide := true }}) only [{ident(f)}.go, {simp}]")
            L.append(f"    repeat' split")
            L.append(f"    all_goals first")
            L.append(f"      | rfl")
            L.append(f"      | (rw [ih] <;> first")
            L.append(f"          | (simp (config := {{ decide := true }}) only [{simp}]; done)")
            L.append(f"          | (rw [Fuel.nfix_nfix]")
            L.append(f"             exact Nat.lt_of_lt_of_le (Fuel.nfix_pred_lt (by rw [Fuel.zp_nfix]; assumption)) (by omega)))")
            L.append("")
            L.append(f"theorem {lemma_name(f, path)} {binders} :")
            L.append(f"    {lhs} = {rhs} :=")
            L.append(f"  {go} _ {xs} (by omega)")
            L.append("")
            continue
        L.append(f"theorem {lemma_name(f, path)} {binders} :")
        L.append(f"    {lhs} = {rhs} := by")
        L.append(f"  simp (config := {{ decide := true }}) only [{ident(f)}, {SIMP}{', ' + callee if callee else ''}]")
        L.append("")
    # each attached function's constraint conjuncts proved of it, hypothesis-free, from its attachment
    L.append("/-! ## Attached functions: the constraint's conjuncts proved of the function (through its")
    L.append("attachment, with no hypothesis), and the conjuncts not proved here, by name -/")
    L.append("")
    facts, owed = [], []
    for f in sorted((g for g in fns.values() if g.attachment), key=lambda g: g.name):
        xs = " ".join(ident(v) for v in f.formals)
        binders = " ".join(f"({ident(v)} : Val)" for v in f.formals)
        call = f"({ident(f.name)}{' ' if xs else ''}{xs})"
        for ci, c in enumerate(f.constraint):
            for kind, k, child, text in conjuncts(c, f.name, acc):
                if kind == "frame" and A.summ.get((f.name, (k, acc[child]))) and "FN2-CORE" in f.formals:
                    nm = f"{ident(f.name)}.constraint{ci}_frame_{child.replace('-', '_')}"
                    L.append(f"/-- `{f.name}`'s constraint {ci}: `{text}`, with no hypothesis. -/")
                    L.append(f"theorem {nm} {binders} :")
                    L.append(f"    {ident(child)} (Native.nth (Val.int {k}) {call}) = {ident(child)} «FN2-CORE» := by")
                    L.append(f"  simp only [{ident(child)}, {lemma_name(f.name, (k, acc[child]))}]")
                    L.append("")
                    facts.append((f.name, nm))
                elif kind == "consp" and A.summ.get((f.name, "consp")) is not None:
                    nm = f"{ident(f.name)}.constraint{ci}_consp"
                    L.append(f"/-- `{f.name}`'s constraint {ci}: `{text}`. -/")
                    L.append(f"theorem {nm} {binders} : Prim.consp {call} = Val.t :=")
                    L.append(f"  {lemma_name(f.name, 'consp')} {xs}")
                    L.append("")
                    facts.append((f.name, nm))
                else:
                    owed.append((f.name, ci, text))
    L.append("/-- The attached functions' constraint conjuncts proved above, by function. -/")
    L.append("def attachedFacts : List (String × String) := [" + ", ".join(f"({lean_str(a)}, {lean_str(b)})" for a, b in facts) + "]")
    L.append("/-- The conjuncts not proved here (their constraint term, conjunct text): ACL2 proves each of")
    L.append("the attachment when `defattach` admits it; the Lean side does not restate those proofs. -/")
    L.append("def attachedOwed : List (String × Nat × String) := [" + ", ".join(f"({lean_str(a)}, {b}, {lean_str(c)})" for a, b, c in owed) + "]")
    L.append("")
    # each answered operation's fact through the dispatch, the shape Fn2.Arms.CorePhase reads
    L.append("/-! ## The core-only operations' facts through the dispatch (`Fn2.Arms.CorePhase.keepsPhase_of_pres`) -/")
    L.append("")
    keeps = []
    # each such fact goes through its function's key, index entry and module row (emit_embed.py)
    mod_of = partition(subset(d)[0], d)[0]
    through = set()
    for o, kn, r, iK, path in opq:
        sm = A.summ.get((o, path))
        if not sm:
            continue
        fn = fns[o]
        j = sm[0]
        if fn.formals[j] != "FN2-CORE" or sm[1] != (iK, 0):
            continue
        n = len(fn.formals)
        vs = " ".join(f"a{i}" for i in range(n))
        nm = f"{ident(o)}.fns_keepsPhase_{kn.replace('-', '_')}"
        cond = "rw [if_pos rfl]" if r == 0 else "rw [if_neg (by decide)]"
        L.append(f"/-- `{o}` keeps `{kn}`'s `PHASE` column of the core it is passed (through the dispatch). -/")
        L.append(f"theorem {nm} (acts : List Val) (v : Val) (h : fns {lean_str(o)} acts = some v) :")
        L.append(f"    Native.nth (Val.int 0) (Native.nth (Val.int {iK}) (if {r} = 0 then v else Native.nth (Val.int {r}) v)) =")
        L.append(f"      Native.nth (Val.int 0) (Native.nth (Val.int {iK}) (acts.getD {j} Val.nil)) := by")
        L.append(f"  have h2 : fns {lean_str(o)} acts = {ident(o)}.dispatch acts :=")
        L.append(f"    Dispatch.via_eq (T := fnTrees) acts {ident(o)}.key {ident(o)}.ix {ident(o)}.find")
        through.add(mod_of[o])
        L.append(f"  rw [h2] at h")
        L.append(f"  unfold {ident(o)}.dispatch at h")
        L.append(f"  split at h")
        L.append(f"  · cases h; {cond}; exact {lemma_name(o, path)} {' '.join('_' for _ in range(n))}")
        L.append(f"  · cases h")
        L.append("")
        keeps.append((o, kn, nm, j, r, iK))
    L.append("/-- The operations with a `PHASE` fact above, by kind. -/")
    L.append("def keepsPhaseOps : List (String × String) := [" + ", ".join(f"({lean_str(kn)}, {lean_str(o)})" for o, kn, *_ in keeps) + "]")
    L.append("")
    L.append("/-- The queries and whether each is answered (a fact above) or not (`none`). -/")
    rows = []
    for what, f, path, s in report:
        ans = "none" if s is None else f"some ({s[0]}, [{', '.join(str(n) for n in s[1])}])"
        rows.append(f"  ({lean_str(f)}, [{', '.join(str(n) for n in path)}], {ans})")
    L.append("def presQueries : List (String × List Nat × Option (Nat × List Nat)) := [\n" + ",\n".join(rows) + "]")
    L.append("")
    L.append(f"end {ns}")
    L.append("")
    at = L.index(f"import {ns}") + 1
    nix = len([f for f in os.listdir(os.path.join(os.path.dirname(out), ns.split(".")[-1]))
               if re.fullmatch(r"IndexEqns\d+\.lean", f)])
    L[at:at] = ([f"import {ns}.{m}Keys" for m in sorted(through)] + [f"import {ns}.{m}Eqns" for m in sorted(through)]
                + [f"import {ns}.IndexEqns{j + 1}" for j in range(nix)])
    open(out, "w").write("\n".join(L))
    if len(sys.argv) > 4:
        emit_phase(sys.argv[4], ns, keeps)
    for what, f, path, s in report:
        print(("PRES   " if s else "UNPRES ") + what)
    print(f"PRES facts={len(A.lemmas)} answered={sum(1 for r in report if r[3])}/{len(report)}")


KIND_SHORT = {"FN2-CNS": "cns", "FN2-CONN": "conn"}


def emit_phase(path, ns, keeps):
    """PHASE.lean: each served kind's operations that keep its `PHASE` column, as
    `Fn2.Arms.Columns.KeepsPhase` over the core face (`Fn2.Arms.CorePhase.keepsPhase_found`)."""
    L = ["-- GENERATED by meta/emit/emit_pres.py from the world print-world.lisp printed.",
         "-- Do not edit: change a book and re-emit (meta/emit/emit.sh).",
         "import Fn2.Arms.CorePhase", "import Fn2.Arms.ServedCore", "import Fn2.Instances.LayerAPres", "",
         "set_option maxHeartbeats 0", "set_option maxRecDepth 100000", "",
         "namespace Fn2.Instances.LayerAPhase",
         "open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Arms.Columns Fn2.Arms.CorePhase Fn2.Arms.ServedCore",
         f"open {ns} Fn2.Instances.LayerAKinds", ""]
    for kn, sh in KIND_SHORT.items():
        kc = f"{sh}C"
        rows = [k for k in keeps if k[1] == kn]
        L.append(f"/-- `{kn}`'s `PHASE` getter over the core face: `(NTH s (NTH 0 t))`. -/")
        L.append(f"theorem {sh}_phase_get (s t : Val) : callFn cw ({kc}.name ++ \"-\" ++ \"PHASE\") [s, t] =")
        L.append(f"    .ok (Native.nth s (Native.nth (Val.int 0) t)) := by")
        L.append(f"  rw [show {kc}.name = {lean_str(kn)} by decide +kernel]")
        L.append(f"  exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)")
        L.append("")
        names = []
        for i, (o, _, nm, j, r, iK) in enumerate(rows):
            tn = f"{sh}_keeps_{i}"
            L.append(f"/-- `{o}` keeps `{kn}`'s `PHASE` column. -/")
            L.append(f"theorem {tn} : KeepsPhase cw {kc} {lean_str(o)} :=")
            L.append(f"  keepsPhase_found world coreTuple {kc} {lean_str(o)} {j} {r} {iK} (by decide +kernel) {sh}_phase_get")
            L.append(f"    (fun acts v h => {nm} acts v h)")
            L.append("")
            names.append((o, tn))
        L.append(f"/-- `{kn}`'s operations with a proved `KeepsPhase`. -/")
        L.append(f"def {sh}PK : List String := [{', '.join(lean_str(o) for o, _ in names)}]")
        L.append("")
        L.append(f"theorem {sh}_keeps : ∀ op ∈ {sh}PK, KeepsPhase cw {kc} op := by")
        L.append(f"  intro op hop")
        L.append(f"  simp only [{sh}PK, List.mem_cons, List.not_mem_nil, or_false] at hop")
        if names:
            L.append(f"  rcases hop with {' | '.join('rfl' for _ in names)}")
            for _, tn in names:
                L.append(f"  · exact {tn}")
        else:
            L.append(f"  exact hop.elim")
        L.append("")
    L.append("end Fn2.Instances.LayerAPhase")
    L.append("")
    open(path, "w").write("\n".join(L))


def ops_in(x, ops, acc):
    if isinstance(x, list):
        if len(x) and str(x[0]) in ops:
            acc.add(str(x[0]))
        for y in x:
            ops_in(y, ops, acc)
    return acc


def conjuncts(c, f, acc):
    """A translated constraint split at its conclusion's conjuncts: (IMPLIES H (AND C1 ..)) or a bare
    conclusion, each conjunct classified: ("frame", k, child, text), ("consp", .., text) or ("other", ..)."""
    t = c
    if isinstance(t, List) and str(t[0]) == "IMPLIES":
        t = t[2]
    parts = []

    def split(x):
        # translated AND: (IF A B 'NIL)
        if isinstance(x, List) and str(x[0]) == "IF" and len(x) == 4 and isinstance(x[3], List) \
                and str(x[3][0]) == "QUOTE" and is_nil(x[3][1]):
            split(x[1]); split(x[2])
        else:
            parts.append(x)
    split(t)
    out = []
    for p in parts:
        fc = frame_claims(p, f, acc)
        text = show(p)[:200]
        if len(fc) == 1 and str(p[0]) == "EQUAL":
            out.append(("frame", fc[0][0], fc[0][1], text))
        elif isinstance(p, List) and str(p[0]) == "CONSP" and isinstance(p[1], List) and str(p[1][0]) == f:
            out.append(("consp", None, None, text))
        else:
            out.append(("other", None, None, text))
    return out


def frame_claims(c, f, acc):
    """`(EQUAL (C (MV-NTH k (F ...))) (C FN2-CORE))` conjuncts of a translated constraint, as (k, C)."""
    out = []

    def walk(t):
        if not isinstance(t, List) or len(t) == 0:
            return
        if str(t[0]) == "EQUAL" and len(t) == 3:
            a, b = t[1], t[2]
            if (isinstance(a, List) and isinstance(b, List) and len(a) == 2 and len(b) == 2
                    and str(a[0]) == str(b[0]) and str(a[0]) in acc and str(b[1]) == "FN2-CORE"):
                m = a[1]
                if isinstance(m, List) and str(m[0]) == "MV-NTH" and lit_index(m[1]) is not None \
                        and isinstance(m[2], List) and str(m[2][0]) == f:
                    out.append((lit_index(m[1]), str(a[0])))
                    return
        for y in t[1:]:
            walk(y)
    walk(c)
    return out


if __name__ == "__main__":
    main()
