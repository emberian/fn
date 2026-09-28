#!/usr/bin/env python3
"""tools/extract/cl.py -- backend 2 of the extractor: Common Lisp, for the
served product (ember, 2026-09-28): an SBCL core holding fn's functions and
the host code, and nothing of ACL2 (A-TARGET-COMPILER, specs/failures.md;
planning/extrapolation-2026-09-27.md section 2.5).

Input: the front end's IR (tools/extract/frontend.lisp; xt-core-export's
roots are every function host/native names).  Output: one Lisp file of
definitions in the ACL2 package, compiled by the same SBCL that runs the
ACL2 image under ACL2's own policy (speed 3, safety 0: acl2.lisp
*acl2-optimize-form*).  Most of the translation is the identity: a
translated ACL2 term is already Common Lisp once its symbols are written
with their home packages.  What is not:
  * multiple values: a function with k>1 results returns (values ...); a
    formal bound to a k-valued actual (mv-let's translation) is a
    multiple-value-bind and (mv-nth 'i mv) its i-th variable;
  * the body a function runs: a guard-verified or :program function runs its
    raw body (Common Lisp's car, +, ...), exactly as the image runs it; an
    :ideal one (logic, guards unverified) runs its logic body with ACL2's
    total primitives (xl-car, xl-+ ... in clruntime.lisp), as the image's *1*
    function does;
  * the executable counterparts the host calls (host/native's fnn-call finds
    ACL2_*1*_ACL2::F): each checks F's guard, then calls F, as ACL2's *1*
    function under guard-checking t; an invariant-risk :program function's
    *1* is its body with every call guard-checked (ACL2's oneify);
  * stobjs: ACL2's raw layout on SBCL (a simple-vector of fields, an array
    field its array, a scalar its value: basis-a.lisp make-stobj-scalar-field),
    so host/native's own reads of a stobj (svref) see what they see in the
    image;
  * a constrained function without an attachment is not emitted: the host
    defines it (host/native/extent.lisp, signatures.lisp), as in the image.
No check is erased that ACL2's raw code performs: the policy is ACL2's.

    cl.py IR.json --out defs.lisp --inventory inv.json
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from chicken import NIL, T, Backend, PRIMS, PREDS, datum_is_nil, datum_list, short  # noqa: E402

# ACL2 primitives: the raw Common Lisp form, and the total (logic) form an
# :ideal body and a *1* body use (clruntime.lisp defines the xl- functions).
RAW = {
    "COMMON-LISP::CAR": "car", "COMMON-LISP::CDR": "cdr", "COMMON-LISP::CONS": "cons",
    "ACL2::BINARY-+": "+", "ACL2::BINARY-*": "*", "ACL2::UNARY--": "-", "ACL2::UNARY-/": "/",
    "COMMON-LISP::<": "<", "COMMON-LISP::EQUAL": "equal", "COMMON-LISP::CONSP": "consp",
    "COMMON-LISP::INTEGERP": "integerp", "COMMON-LISP::RATIONALP": "rationalp",
    "ACL2::ACL2-NUMBERP": "numberp", "COMMON-LISP::COMPLEX-RATIONALP": "|ACL2|::|XL-COMPLEX-RATIONALP|",
    "ACL2::COMPLEX-RATIONALP": "|ACL2|::|XL-COMPLEX-RATIONALP|",
    "COMMON-LISP::CHARACTERP": "characterp", "COMMON-LISP::STRINGP": "stringp",
    "COMMON-LISP::SYMBOLP": "symbolp", "COMMON-LISP::CHAR-CODE": "char-code",
    "COMMON-LISP::CODE-CHAR": "code-char", "COMMON-LISP::COERCE": "|ACL2|::|XL-COERCE|",
    "COMMON-LISP::DENOMINATOR": "denominator", "COMMON-LISP::NUMERATOR": "numerator",
    "COMMON-LISP::REALPART": "realpart", "COMMON-LISP::IMAGPART": "imagpart",
    "COMMON-LISP::COMPLEX": "complex", "COMMON-LISP::SYMBOL-NAME": "symbol-name",
    "COMMON-LISP::SYMBOL-PACKAGE-NAME": "|ACL2|::|XL-SYMBOL-PACKAGE-NAME|",
    "ACL2::SYMBOL-PACKAGE-NAME": "|ACL2|::|XL-SYMBOL-PACKAGE-NAME|",
    "COMMON-LISP::INTERN-IN-PACKAGE-OF-SYMBOL": "|ACL2|::|XL-INTERN-IN-PACKAGE-OF-SYMBOL|",
    "ACL2::INTERN-IN-PACKAGE-OF-SYMBOL": "|ACL2|::|XL-INTERN-IN-PACKAGE-OF-SYMBOL|",
    "ACL2::BAD-ATOM<=": "|ACL2|::|XL-BAD-ATOM<=|",
    # ACL2 built-ins whose raw definition is Common Lisp's (logand ...):
    # their logical definitions (bit recursions) are not what the image runs
    "ACL2::BINARY-LOGAND": "logand", "ACL2::BINARY-LOGIOR": "logior", "ACL2::BINARY-LOGXOR": "logxor",
    "ACL2::BINARY-LOGEQV": "logeqv", "COMMON-LISP::LOGNOT": "lognot", "COMMON-LISP::ASH": "ash",
    "ACL2::LEN": "|ACL2|::|XL-LEN|",
    # raw-only: the :exec branch is Common Lisp's (string-append's is
    # (concatenate 'string ...), which translates back to string-append)
    "ACL2::STRING-APPEND": "|ACL2|::|XL-STRING-APPEND|",
    "ACL2::NONNEGATIVE-INTEGER-QUOTIENT": "|ACL2|::|XL-NIQ|",
}
LOGIC = {"COMMON-LISP::CAR": "|ACL2|::|XL-CAR|", "COMMON-LISP::CDR": "|ACL2|::|XL-CDR|",
         "ACL2::BINARY-+": "|ACL2|::|XL-+|", "ACL2::BINARY-*": "|ACL2|::|XL-*|",
         "ACL2::UNARY--": "|ACL2|::|XL-NEG|", "ACL2::UNARY-/": "|ACL2|::|XL-RECIP|",
         "COMMON-LISP::<": "|ACL2|::|XL-<|", "COMMON-LISP::CHAR-CODE": "|ACL2|::|XL-CHAR-CODE|",
         "COMMON-LISP::CODE-CHAR": "|ACL2|::|XL-CODE-CHAR|", "COMMON-LISP::DENOMINATOR": "|ACL2|::|XL-DENOMINATOR|",
         "COMMON-LISP::NUMERATOR": "|ACL2|::|XL-NUMERATOR|", "COMMON-LISP::REALPART": "|ACL2|::|XL-REALPART|",
         "COMMON-LISP::IMAGPART": "|ACL2|::|XL-IMAGPART|", "COMMON-LISP::COMPLEX": "|ACL2|::|XL-COMPLEX|",
         "COMMON-LISP::SYMBOL-NAME": "|ACL2|::|XL-SYMBOL-NAME|",
         "ACL2::BINARY-LOGAND": "|ACL2|::|XL-LOGAND|", "ACL2::BINARY-LOGIOR": "|ACL2|::|XL-LOGIOR|",
         "ACL2::BINARY-LOGXOR": "|ACL2|::|XL-LOGXOR|", "ACL2::BINARY-LOGEQV": "|ACL2|::|XL-LOGEQV|",
         "COMMON-LISP::LOGNOT": "|ACL2|::|XL-LOGNOT|", "COMMON-LISP::ASH": "|ACL2|::|XL-ASH|"}


# ACL2 runtime names clruntime.lisp defines over this process's objects (the
# state globals, the world properties host/native reads, the live stobjs, the
# error path): never emitted from their logical definitions.
RUNTIME = {"ACL2::" + n for n in (
    "W", "GETPROPC", "GETPROP", "USER-STOBJ-ALIST", "F-GET-GLOBAL", "F-PUT-GLOBAL", "F-BOUNDP-GLOBAL",
    "GET-GLOBAL", "PUT-GLOBAL", "BOUNDP-GLOBAL", "STOBJS-IN", "HARD-ERROR", "ILLEGAL",
    "THROW-NONEXEC-ERROR", "FMT-TO-COMMENT-WINDOW", "FMT-TO-COMMENT-WINDOW!", "FMT-TO-COMMENT-WINDOW+",
    "FMT-TO-COMMENT-WINDOW!+", "CW-PRINT-BASE-RADIX")}


def esc(s):
    return s.replace("\\", "\\\\").replace("|", "\\|")


def sym(name):
    pkg, n = name.split("::", 1)
    if pkg == "KEYWORD":
        return ":|%s|" % esc(n)
    return "|%s|::|%s|" % (esc(pkg), esc(n))


def star1(name):
    pkg, n = name.split("::", 1)
    return "|ACL2_*1*_%s|::|%s|" % (esc(pkg), esc(n))


def string(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def datum(d):
    """A readable Common Lisp external representation (written Latin-1)."""
    if isinstance(d, int):
        return str(d)
    tag = d[0]
    if tag == "r":
        return "%d/%d" % (d[1], d[2])
    if tag == "x":
        return "#C(%s %s)" % (datum(d[1]), datum(d[2]))
    if tag == "ch":
        return "#.(code-char %d)" % d[1]
    if tag == "s":
        return string(d[1])
    if tag == "y":
        return "nil" if d[1] == NIL else sym(d[1])
    if tag == "L":
        elems = " ".join(datum(e) for e in d[1])
        return "(%s)" % elems if datum_is_nil(d[2]) else "(%s . %s)" % (elems, datum(d[2]))
    raise ValueError("bad datum %r" % (d,))


def quoted(d):
    if isinstance(d, int) or d[0] in ("r", "x", "s") or (d[0] == "y" and d[1] in (NIL, T)):
        return datum(d)
    if d[0] == "ch":
        return datum(d)
    if d[0] == "y" and d[1].startswith("KEYWORD::"):
        return datum(d)
    return "'" + datum(d)


class CL(Backend):
    def __init__(self, ir):
        super().__init__(ir)
        self.boundary = {b["name"]: b for b in ir.get("boundary", [])}
        self.types = {}
        self.star1_needed = set()
        self.counter = 0

    # --- terms --------------------------------------------------------------------------
    def var(self, v):
        return sym(v)

    def tmp(self):
        self.counter += 1
        return "#:|m%d|" % self.counter if False else "|m%d|" % self.counter

    def emit(self, t, env, want, mode):
        tag = t[0]
        if tag == "v":
            b = env.get(t[1])
            if b:
                return ("(values %s)" if want > 1 else "(list %s)") % " ".join(b)
            return self.var(t[1]) if want == 1 else "(values-list %s)" % self.var(t[1])
        if tag == "q":
            if want == 1:
                return quoted(t[1])
            elems = datum_list(t[1])
            if elems is not None and len(elems) == want:
                return "(values %s)" % " ".join(quoted(e) for e in elems)
            return "(values-list %s)" % quoted(t[1])
        if tag == "l":
            return self.emit_lambda(t, env, want, mode)
        fn, args = t[1], t[2]
        if fn == "COMMON-LISP::IF":
            return "(if %s %s %s)" % (self.emit(args[0], env, 1, mode), self.emit(args[1], env, want, mode),
                                      self.emit(args[2], env, want, mode))
        if want > 1 and fn == "COMMON-LISP::CONS":
            elems, cur = [], t
            while cur[0] == "c" and cur[1] == "COMMON-LISP::CONS" and len(elems) < want:
                elems.append(cur[2][0])
                cur = cur[2][1]
            if len(elems) == want and cur[0] == "q" and datum_is_nil(cur[1]):
                return "(values %s)" % " ".join(self.emit(e, env, 1, mode) for e in elems)
        if fn == "ACL2::MV-NTH" and args[0][0] == "q" and args[1][0] == "v" and args[1][1] in env:
            return env[args[1][1]][args[0][1]]
        if fn == "ACL2::RETURN-LAST":
            key = args[0][1] if args[0][0] == "q" else None
            if key == ["y", "COMMON-LISP::PROGN"]:
                return "(progn %s %s)" % (self.emit(args[1], env, 1, mode), self.emit(args[2], env, want, mode))
            return self.emit(args[2], env, want, mode)
        if fn == "ACL2::THE-CHECK":
            x = self.emit(args[2], env, want, mode)
            if mode == "raw" and want == 1 and args[1][0] == "q":
                return "(the %s %s)" % (datum(args[1][1]), x)
            return x
        xs = " ".join(self.emit(a, env, 1, mode) for a in args)
        if fn in RAW:
            head = LOGIC.get(fn, RAW[fn]) if mode != "raw" else RAW[fn]
            call = "(%s %s)" % (head, xs)
        else:
            f0 = f = self.fns.get(fn)
            target = fn
            while f and f["kind"] == "alias":
                target = f["target"]
                f = self.fns.get(target)
            if mode == "star1" and f and f["kind"] in ("defun", "stobj-prim"):
                # an abstract stobj's export is checked against ITS guard
                name = fn if f0["kind"] == "alias" else target
                self.star1_needed.add(name)
                call = "(%s %s)" % (star1(name), xs)
            else:
                call = "(%s %s)" % (sym(target), xs)
        return call if want == 1 or self.nvalues(t) > 1 else "(values-list %s)" % call

    def shimmed(self):
        return set()

    def emit_lambda(self, t, env, want, mode):
        formals, body, actuals = t[1], t[2], t[3]
        the = self.the_pattern(t)
        if the is not None:
            return self.emit(the[0], env, want, mode)
        new_env = {k: v for k, v in env.items() if k not in formals}
        plain, tuples = [], []
        for v, a in zip(formals, actuals):
            n = self.nvalues(a)
            if n > 1:
                names = [self.tmp() for _ in range(n)]
                tuples.append((names, self.emit(a, env, n, mode)))
                new_env[v] = names
            else:
                plain.append((v, self.emit(a, env, 1, mode)))
        inner = self.emit(body, new_env, want, mode)
        if plain:
            inner = "(let (%s) (declare (ignorable %s)) %s)" % (
                " ".join("(%s %s)" % (self.var(v), x) for v, x in plain),
                " ".join(self.var(v) for v, _ in plain), inner)
        for names, expr in reversed(tuples):
            inner = "(multiple-value-bind (%s) %s (declare (ignorable %s)) %s)" % (
                " ".join(names), expr, " ".join(names), inner)
        return inner

    # --- definitions -------------------------------------------------------------------------
    def mode_of(self, f):
        return "logic" if f.get("class") == "ideal" else "raw"

    def defun(self, f):
        self.counter = 0
        formals = " ".join(self.var(v) for v in f["formals"])
        mode = self.mode_of(f)
        body = self.emit(f["body"], {}, self.nout(f["name"]), mode)
        decls = ""
        if mode == "raw":
            # the type declarations ACL2 compiled this definition with
            # (core-export.lisp: its CLTL-COMMAND defun), on its formals
            items = []
            for t in self.types.get(f["name"], []):
                elems = datum_list(t)
                if elems and all(isinstance(v, list) and v[0] == "y" and v[1] in f["formals"] for v in elems[1:]):
                    items.append("(type %s %s)" % (datum(elems[0]), " ".join(sym(v[1]) for v in elems[1:])))
            if items:
                decls = " (declare %s)" % " ".join(items)
        return "(defun %s (%s) (declare (ignorable %s))%s %s)" % (sym(f["name"]), formals, formals, decls, body)

    def guard_test(self, f):
        formals = f["formals"]
        stobjs_in = f.get("stobjs_in") or [None] * len(formals)
        live = {v for v, st in zip(formals, stobjs_in) if st}
        g = self.drop_live_recognizers(f.get("guard", ["q", ["y", T]]), live, self.stobj_recognizers())
        if g == ["q", ["y", T]]:
            return None
        self.counter = 0
        return self.emit(g, {}, 1, "logic")

    def star1_def(self, name):
        """ACL2_*1*_PKG::F: F's guard (a violation halts, as fnn-call reports
        it: `ACL2 error in F: ACL2 Halted'), then F; an invariant-risk
        :program function's *1* runs its body with each call checked."""
        f = self.fns[name]
        if f["kind"] == "alias":
            # an alias (an abstract stobj's export, an attached constrained
            # function): ITS guard (the export's :logic guard, not its
            # :exec's), then the target raw
            target, g = name, f
            while g and g["kind"] == "alias":
                target = g["target"]
                g = self.fns[target]
            guard = f.get("guard") or (self.boundary.get(name) or {}).get("guard") or ["q", ["y", T]]
            f = {"name": name, "formals": g["formals"], "stobjs_in": g.get("stobjs_in"), "guard": guard,
                 "_call": target}
        formals = " ".join(self.var(v) for v in f["formals"])
        test = self.guard_test(f) if "guard" in f else None
        if "_call" in f:
            call = "(%s %s)" % (sym(f["_call"]), formals)
        elif f.get("class") == "program" and f.get("invariant_risk"):
            self.counter = 0
            call = self.emit(f["body"], {}, self.nout(name), "star1")
        else:
            call = "(%s %s)" % (sym(name), formals)
        if test:
            call = "(if %s %s (|ACL2|::|XL-GUARD-VIOLATION| '%s (list %s)))" % (test, call, sym(name), formals)
        return "(defun %s (%s) (declare (ignorable %s)) %s)" % (star1(name), formals, formals, call)

    def alias_defs(self, f):
        target = f["name"]
        g = f
        while g and g["kind"] == "alias":
            target = g["target"]
            g = self.fns.get(target)
        if not g or g["kind"] not in ("defun", "stobj-prim"):
            return []
        formals = " ".join(self.var(v) for v in g["formals"])
        out = ["(defun %s (%s) (%s %s))" % (sym(f["name"]), formals, sym(target), formals)]
        return out

    # --- stobjs: ACL2's raw layout on SBCL -------------------------------------------------------
    def cl_type(self, d):
        return datum(d)

    def creator_form(self, stname):
        s = self.stobjs[stname]
        if s.get("abstract"):
            return self.creator_form(s["foundation"])
        parts = []
        for fld in s["fields"]:
            kind = fld["_kind"]
            if kind == "array":
                et = self.elt_type(fld)
                n = self.array_dim(fld)
                if isinstance(et, tuple):
                    parts.append("(let ((a (make-array %d))) (dotimes (i %d a) (setf (svref a i) %s)))"
                                 % (n, n, self.creator_form(et[1])))
                else:
                    parts.append("(make-array %d :element-type '%s :initial-element %s)"
                                 % (n, datum(fld["type"][1][1]), quoted(fld["init"])))
            elif kind == "hash":
                test = fld["type"][1][1][1] if len(fld["type"][1]) > 1 else "COMMON-LISP::EQL"
                parts.append("(make-hash-table :test '%s)" % sym(test))
            elif fld["type"][0] == "y" and fld["type"][1] in self.stobjs:
                parts.append(self.creator_form(fld["type"][1]))     # a nested stobj
            else:
                parts.append(quoted(fld["init"]))
        return "(vector %s)" % " ".join(parts)

    def stobj_prim(self, name):
        f = self.fns[name]
        s = self.stobjs[f["stobj"]]
        if name == s["creator"]:
            return "(defun %s () %s)" % (sym(name), self.creator_form(f["stobj"]))
        if name == s["recognizer"]:
            return "(defun %s (x) (declare (ignore x)) t)" % sym(name)
        info = self.prim_info.get(name)
        if not info:
            return "(defun %s (&rest args) (error \"stobj primitive not extracted: ~s ~s\" '%s args))" % (
                sym(name), sym(name), sym(name))
        _, fld, op = info
        i = fld["_index"]
        n = sym(name)
        slot = "(svref st %d)" % i
        return {
            "scalar-get": "(defun %s (st) %s)" % (n, slot),
            "scalar-set": "(defun %s (v st) (setf %s v) st)" % (n, slot),
            "array-get": "(defun %s (i st) (aref %s i))" % (n, slot),
            "array-set": "(defun %s (i v st) (setf (aref %s i) v) st)" % (n, slot),
            "array-length": "(defun %s (st) (length %s))" % (n, slot),
            "array-resize": "(defun %s (k st) (setf %s (|ACL2|::|XL-RESIZE| %s k %s)) st)" % (
                n, slot, slot, self.fill_form(fld)),
            "hash-get": "(defun %s (k st) (values (gethash k %s)))" % (n, slot),
            "hash-put": "(defun %s (k v st) (setf (gethash k %s) v) st)" % (n, slot),
            "hash-boundp": "(defun %s (k st) (nth-value 1 (gethash k %s)))" % (n, slot),
            "hash-rem": "(defun %s (k st) (remhash k %s) st)" % (n, slot),
            "hash-count": "(defun %s (st) (hash-table-count %s))" % (n, slot),
            "hash-clear": "(defun %s (st) (clrhash %s) st)" % (n, slot),
            "hash-init": "(defun %s (size rehash-size rehash-threshold st) (declare (ignore size rehash-size "
                         "rehash-threshold)) (setf %s (make-hash-table :test (hash-table-test %s))) st)"
                         % (n, slot, slot),
        }.get(op, "(defun %s (&rest args) (error \"stobj op ~s\" '%s args))" % (n, op))

    def fill_form(self, fld):
        et = self.elt_type(fld)
        if isinstance(et, tuple):
            return "(lambda () %s)" % self.creator_form(et[1])
        return "(lambda () %s)" % quoted(fld["init"])

    # --- the program ------------------------------------------------------------------------------
    def program(self):
        out = [";;; generated by tools/extract/cl.py; do not edit",
               "(in-package \"ACL2\")",
               # ACL2's own compilation policy (acl2.lisp *acl2-optimize-form*)
               "(declaim (optimize (compilation-speed 0) (speed 3) (space 1) (safety 0)))"]
        inv = {"defun": 0, "star1": 0, "stobj-prim": 0, "alias": 0, "host-defined": [], "blocker": []}
        # the stobj primitives first, proclaimed inline as ACL2 proclaims a
        # defstobj's (*stobj-inline-declare*); a NAME$INLINE function inline
        # (ACL2's define-inline); then every defun, every alias, the *1*s
        prims = [f["name"] for f in self.ir["functions"] if f["kind"] == "stobj-prim"]
        inl = [f["name"] for f in self.ir["functions"] if f["kind"] == "defun" and f["name"].endswith("$INLINE")]
        if prims or inl:
            out.append("(declaim (inline %s))" % " ".join(sym(n) for n in prims + inl))
        for n in prims:
            out.append(self.stobj_prim(n))
            inv["stobj-prim"] += 1
        fs = sorted((f for f in self.ir["functions"] if f["kind"] == "defun"),
                    key=lambda f: not f["name"].endswith("$INLINE"))
        for f in fs:
            n = f["name"]
            if n.startswith("COMMON-LISP::") or n in RAW or n in RUNTIME:
                continue
            out.append(self.defun(f))
            inv["defun"] += 1
        for f in self.ir["functions"]:
            if f["kind"] == "blocker":
                inv["host-defined"].append(f["name"])
        for f in self.ir["functions"]:
            if f["kind"] == "alias" and not f["name"].startswith("COMMON-LISP::"):
                defs = self.alias_defs(f)
                out.extend(defs)
                inv["alias"] += len(defs)
        wanted = {n for n in self.boundary if n in self.fns and self.fns[n]["kind"] in ("defun", "stobj-prim", "alias")}
        done = set()
        pending = sorted(wanted)
        while pending:
            n = pending.pop()
            if n in done or n not in self.fns or self.fns[n]["kind"] not in ("defun", "stobj-prim", "alias"):
                continue
            done.add(n)
            before = set(self.star1_needed)
            out.append(self.star1_def(n))
            inv["star1"] += 1
            pending.extend(sorted(self.star1_needed - before - done))
        inv["star1_names"] = sorted(done)
        # the live stobjs, made at start (a saved core may hold constants in
        # read-only space): every stobj of the closure by its name, as ACL2's
        # user-stobj-alist holds the live objects
        out.append("(defun |ACL2|::|XL-MAKE-LIVE-STOBJS| () (setq |ACL2|::|*XL-USER-STOBJ-ALIST*| (list %s)))"
                   % " ".join("(cons '%s %s)" % (sym(s["name"]), self.creator_form(s["name"]))
                              for s in self.ir["stobjs"]))
        return "\n".join(out) + "\n", inv

    def packages(self, pkgs):
        """The packages the code names, ACL2's imports first: each made with no
        :use and given exactly the image's imports, so every symbol read is the
        symbol ACL2 has (host/native is read in package ACL2)."""
        used = {"ACL2", "ACL2_INVISIBLE"}
        text = json.dumps(self.ir)
        for pkg in {m.split("::")[0] for m in __import__("re").findall(r'"([A-Z0-9_*+$-]+::)', text)}:
            used.add(pkg)
        used -= {"COMMON-LISP", "KEYWORD"}
        by = {p["name"]: p for p in pkgs}
        order = ["ACL2"] + sorted(p for p in used if p != "ACL2")
        out = [";;; generated by tools/extract/cl.py from the image's packages; do not edit"]
        for p in order + ["ACL2_*1*_" + q for q in order if q in by] + ["ACL2_*1*_COMMON-LISP"]:
            out.append('(unless (find-package "%s") (make-package "%s" :use nil))' % (p, p))
        for p in order:
            if p not in by:
                continue
            for home, name in by[p]["imports"]:
                out.append('(import (list (intern "%s" "%s")) "%s")' % (name.replace('"', '\\"'), home, p))
        return "\n".join(out) + "\n"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("ir")
    p.add_argument("--out", required=True)
    p.add_argument("--inventory", required=True)
    p.add_argument("--packages", help="packages.json (core-export.lisp) -> --packages-out")
    p.add_argument("--packages-out")
    a = p.parse_args()
    ir = json.load(open(a.ir))
    b = CL(ir)
    extra = json.load(open(a.packages)) if a.packages else {"packages": [], "types": {}}
    b.types = extra.get("types", {})
    text_, inv = b.program()
    if a.packages:
        Path(a.packages_out).write_text(b.packages(extra["packages"]), encoding="latin-1")
    with open(a.out, "w", encoding="latin-1") as h:
        h.write(text_)
    json.dump(inv, open(a.inventory, "w"), indent=1)
    print("cl: %d defuns, %d stobj primitives, %d aliases, %d *1* functions; %d host-defined"
          % (inv["defun"], inv["stobj-prim"], inv["alias"], inv["star1"], len(inv["host-defined"])))


if __name__ == "__main__":
    main()
