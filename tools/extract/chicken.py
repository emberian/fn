#!/usr/bin/env python3
"""tools/extract/chicken.py -- backend 1 of the extractor: CHICKEN Scheme 5.

Input: the JSON tools/extract/frontend.lisp writes from the ACL2 world (the
translated, mbe-resolved executable bodies, the stobj field tables, what is
primitive, shimmed, aliased or blocked).  Output: one Scheme file that
includes tools/extract/runtime.scm, plus a JSON ledger of every check the
backend erased and the guard that justified it.

Translation rules (docs: planning/evidence/proto-extract-2026-09-27.md):
  * NIL is '(); a test is (if (eq? x '()) else then), and a primitive
    predicate in test position is the native Scheme predicate;
  * a lambda application is a let (a let* through temporaries when an
    argument produces a stobj, to keep Common Lisp's left-to-right order);
  * mv: a function with k>1 results returns (values ...); an mv-let's
    lambda binds its MV formal through call-with-values and (mv-nth 'i mv)
    reads the i-th temporary;
  * a stobj is a mutable record; each defstobj's primitives are generated;
  * GUARDS AS TYPES: in a guard-verified function, the guard's conjuncts and
    `the' declarations give integer intervals to variables; an arithmetic
    primitive whose arguments and result lie in the fixnum range is emitted
    as the unchecked fx operation, and a stobj array access as the unchecked
    vector operation; each erasure is recorded with the fact that justifies it.
"""
import argparse
import json
import sys

NIL = "COMMON-LISP::NIL"
T = "COMMON-LISP::T"
FIX_LO, FIX_HI = -(1 << 62), (1 << 62) - 1   # CHICKEN 5, 64-bit fixnums
INF = float("inf")


def scm_sym(name):
    return "|" + name.replace("\\", "\\\\").replace("|", "\\|") + "|"


def fname(name):
    return scm_sym("f:" + name)


def short(name):
    return name.split("::", 1)[1] if "::" in name else name


# --- data ------------------------------------------------------------------------
def scm_string(s):
    out = ['"']
    for ch in s:
        k = ord(ch)
        if ch in '"\\':
            out.append("\\" + ch)
        elif 32 <= k <= 126:
            out.append(ch)
        else:
            out.append("\\x%02x" % k)
    out.append('"')
    return "".join(out)


def scm_datum(d):
    """A quotable Scheme external representation of an ACL2 datum."""
    if isinstance(d, int):
        return str(d)
    tag = d[0]
    if tag == "r":
        return "%d/%d" % (d[1], d[2])
    if tag == "x":
        re, im = scm_datum(d[1]), scm_datum(d[2])
        return "%s%s%si" % (re, "" if im.startswith("-") else "+", im)
    if tag == "ch":
        return "#\\x%02x" % d[1]
    if tag == "s":
        return scm_string(d[1])
    if tag == "y":
        return "()" if d[1] == NIL else scm_sym(d[1])
    if tag == "L":
        elems = " ".join(scm_datum(e) for e in d[1])
        tail = d[2]
        if tail == ["y", NIL]:
            return "(" + elems + ")"
        return "(" + elems + " . " + scm_datum(tail) + ")"
    raise ValueError("bad datum %r" % (d,))


def datum_is_nil(d):
    return d == ["y", NIL]


def datum_list(d):
    """The elements of a proper-list datum, or None."""
    if datum_is_nil(d):
        return []
    if isinstance(d, list) and d[0] == "L" and datum_is_nil(d[2]):
        return d[1]
    return None


# --- primitives and shims ----------------------------------------------------------
# name -> (arity, value-context template, test-context template or None)
PRIMS = {
    "COMMON-LISP::CONS": "(cons {0} {1})",
    "COMMON-LISP::CAR": "(a-car {0})",
    "COMMON-LISP::CDR": "(a-cdr {0})",
    "ACL2::BINARY-+": "(+ {0} {1})",
    "ACL2::BINARY-*": "(* {0} {1})",
    "ACL2::UNARY--": "(- {0})",
    "ACL2::UNARY-/": "(/ {0})",
    "COMMON-LISP::CHAR-CODE": "(char->integer {0})",
    "COMMON-LISP::CODE-CHAR": "(integer->char {0})",
    "COMMON-LISP::COERCE": "(a-coerce {0} {1})",
    "COMMON-LISP::DENOMINATOR": "(denominator {0})",
    "COMMON-LISP::NUMERATOR": "(numerator {0})",
    "COMMON-LISP::REALPART": "(real-part {0})",
    "COMMON-LISP::IMAGPART": "(imag-part {0})",
    "COMMON-LISP::COMPLEX": "(a-complex {0} {1})",
    "COMMON-LISP::SYMBOL-NAME": "(a-symbol-name {0})",
    "COMMON-LISP::SYMBOL-PACKAGE-NAME": "(a-symbol-package-name {0})",
    "COMMON-LISP::INTERN-IN-PACKAGE-OF-SYMBOL": "(a-intern-in-package-of-symbol {0} {1})",
    "ACL2::BAD-ATOM<=": "(a-bad-atom<= {0} {1})",
}
PREDS = {
    "COMMON-LISP::CONSP": "(pair? {0})",
    "COMMON-LISP::EQUAL": "(equal? {0} {1})",
    "COMMON-LISP::<": "(< {0} {1})",
    "COMMON-LISP::INTEGERP": "(exact-integer? {0})",
    "COMMON-LISP::RATIONALP": "(a-rationalp {0})",
    "ACL2::ACL2-NUMBERP": "(number? {0})",
    "COMMON-LISP::COMPLEX-RATIONALP": "(a-complex-rationalp {0})",
    "COMMON-LISP::CHARACTERP": "(char? {0})",
    "COMMON-LISP::STRINGP": "(string? {0})",
    "COMMON-LISP::SYMBOLP": "(a-symbolp {0})",
}
# Raw-Lisp built-ins and raw-only functions: runtime.scm implements these.
SHIMS = {
    "COMMON-LISP::ASH": "a-ash",
    "ACL2::BINARY-LOGAND": "bitwise-and",
    "ACL2::BINARY-LOGIOR": "bitwise-ior",
    "ACL2::BINARY-LOGXOR": "bitwise-xor",
    "ACL2::BINARY-LOGEQV": "a-logeqv",
    "COMMON-LISP::LOGNOT": "bitwise-not",
    "COMMON-LISP::LOGORC1": "a-logorc1",
    "COMMON-LISP::FLOOR": "a-floor",
    "COMMON-LISP::MOD": "a-mod",
    "COMMON-LISP::EXPT": "a-expt",
    "ACL2::NONNEGATIVE-INTEGER-QUOTIENT": "a-niq",
    "COMMON-LISP::LENGTH": "a-length",
    "ACL2::LEN": "a-len",
    "ACL2::STRING-APPEND": "string-append",
    "ACL2::CHAR-DOWNCASE-NON-STANDARD": "a-char-downcase-non-standard",
    "ACL2::BOUNDP-GLOBAL": "a-boundp-global",
    "ACL2::F-BOUNDP-GLOBAL": "a-boundp-global",
    "ACL2::GET-GLOBAL": "a-get-global",
    "ACL2::F-GET-GLOBAL": "a-get-global",
    "ACL2::PUT-GLOBAL": "a-put-global",
    "ACL2::F-PUT-GLOBAL": "a-put-global",
    "ACL2::HARD-ERROR": "a-hard-error",
    "ACL2::ILLEGAL": "a-illegal",
    "ACL2::THROW-NONEXEC-ERROR": "a-throw-nonexec-error",
    "ACL2::FN-DURABLE-REALIZE-OCTET": "a-durable-realize-octet",
    "ACL2::FN-DURABLE-REALIZE-OCTETS": "a-durable-realize-octets",
    "ACL2::FN-DURABLE-REALIZE-LZ": "a-durable-realize-lz",
}
# The image's native digest (host/native/digest.lisp, lane digest-native):
# calls of these go to tools/extract/native.scm's libcrypto SHA-256; the
# extracted definitions stay as the fallback and the self-check's reference.
NATIVE = {
    "ACL2::FN-SHA256-STOBJ": "a-native-sha256-list",
    "ACL2::FN-SHA256-OF-STRING": "a-native-sha256-string",
    "ACL2::FN-SHA256-OF-PREFIXED-BUFFER": "a-native-sha256-prefixed-buffer",
}
# Common Lisp and ACL2 built-ins that raw Lisp compiles inline (NOT, EQ,
# ZP ...): the Scheme form for a test position, and for a value position.
# Their ACL2 definitions are still extracted and the per-function
# differential checks each of these against ACL2's own evaluation.
INLINE = {
    "COMMON-LISP::NOT": ("(not {t0})", None),
    "COMMON-LISP::NULL": ("(eq? {0} '())", None),
    "COMMON-LISP::ATOM": ("(not (pair? {0}))", None),
    "COMMON-LISP::ENDP": ("(not (pair? {0}))", None),
    "COMMON-LISP::EQ": ("(eqv? {0} {1})", None),
    "COMMON-LISP::EQL": ("(eqv? {0} {1})", None),
    "COMMON-LISP::=": ("(= {0} {1})", None),
    "ACL2::ZP": ("(a-zp {0})", None),
    "ACL2::ZIP": ("(a-zip {0})", None),
    "ACL2::NATP": ("(a-natp {0})", None),
    "ACL2::POSP": ("(a-posp {0})", None),
    "ACL2::BOOLEANP": ("(a-booleanp {0})", None),
    "ACL2::NFIX": (None, "(a-nfix {0})"),
    "ACL2::IFIX": (None, "(a-ifix {0})"),
    "ACL2::FIX": (None, "(a-fix {0})"),
}

# Why each shim exists (the inventory).
SHIM_CLASS = {
    "ACL2::BOUNDP-GLOBAL": "state", "ACL2::F-BOUNDP-GLOBAL": "state",
    "ACL2::GET-GLOBAL": "state", "ACL2::F-GET-GLOBAL": "state",
    "ACL2::PUT-GLOBAL": "state", "ACL2::F-PUT-GLOBAL": "state",
    "ACL2::HARD-ERROR": "raw-only error", "ACL2::ILLEGAL": "raw-only error",
    "ACL2::THROW-NONEXEC-ERROR": "raw-only error",
    "ACL2::CHAR-DOWNCASE-NON-STANDARD": "host-Lisp character table (constrained in ACL2)",
    "ACL2::FN-DURABLE-REALIZE-OCTET": "file primitive (A-DURABLE-EXTENT)",
    "ACL2::FN-DURABLE-REALIZE-OCTETS": "file primitive (A-DURABLE-EXTENT)",
    "ACL2::FN-DURABLE-REALIZE-LZ": "file primitive and ACL2's decoder (A-DURABLE-LZ)",
}
# fx forms for arithmetic whose arguments and result are fixnums.
FX = {
    "ACL2::BINARY-+": "fx+", "ACL2::BINARY-*": "fx*",
    "ACL2::BINARY-LOGAND": "fxand", "ACL2::BINARY-LOGIOR": "fxior",
    "ACL2::BINARY-LOGXOR": "fxxor",
}


# --- intervals ("guards as types") ----------------------------------------------------
class Iv:
    __slots__ = ("lo", "hi", "why")

    def __init__(self, lo, hi, why):
        self.lo, self.hi, self.why = lo, hi, why

    def fixnum(self):
        return self.lo >= FIX_LO and self.hi <= FIX_HI


def iv_meet(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return Iv(max(a.lo, b.lo), min(a.hi, b.hi), a.why + b.why)


def conjuncts(term):
    """The conjuncts of a translated guard: (if a b 'nil) is (and a b)."""
    if term[0] == "c" and term[1] == "COMMON-LISP::IF" and term[2][2] == ["q", ["y", NIL]]:
        return conjuncts(term[2][0]) + conjuncts(term[2][1])
    return [term]


def qint(t):
    if t[0] == "q" and isinstance(t[1], int):
        return t[1]
    return None


def text(t, depth=0):
    if depth > 6:
        return "..."
    if t[0] == "v":
        return short(t[1]).lower()
    if t[0] == "q":
        d = t[1]
        if isinstance(d, int):
            return str(d)
        return "'" + scm_datum(d)[:40].lower()
    if t[0] == "c":
        return "(" + " ".join([short(t[1]).lower()] + [text(a, depth + 1) for a in t[2]]) + ")"
    return "((lambda ...) ...)"


# Recognizers whose length argument bounds an index by a resident object.
LENGTHISH = ("ACL2::LEN", "COMMON-LISP::LENGTH")


class Backend:
    def __init__(self, ir):
        self.ir = ir
        self.fns = {f["name"]: f for f in ir["functions"]}
        self.stobjs = {s["name"]: s for s in ir["stobjs"]}
        self.consts = {}
        self.const_defs = []
        self.erased = []
        self.prim_info = {}   # stobj primitive name -> (stobj, field, op)
        self.array_lengths = set()
        self.pred_cache = {}
        self.cur_star1 = False
        self.checked_needed = set()
        self.native = True
        self._index_stobj_prims()

    # --- stobjs ------------------------------------------------------------------------
    def _index_stobj_prims(self):
        for s in self.ir["stobjs"]:
            if s["abstract"]:
                continue
            for i, fld in enumerate(s["fields"]):
                ftype = fld["type"]
                kind = "scalar"
                if isinstance(ftype, list) and ftype[0] == "L" and ftype[1][0] == ["y", "COMMON-LISP::ARRAY"]:
                    kind = "array"
                elif isinstance(ftype, list) and ftype[0] == "L" and ftype[1][0] == ["y", "COMMON-LISP::HASH-TABLE"]:
                    kind = "hash"
                fld["_kind"], fld["_index"] = kind, i
                if kind == "hash":
                    base = fld["field"]
                    for op in ("GET", "PUT", "BOUNDP", "REM", "COUNT", "CLEAR", "INIT"):
                        self.prim_info[base + "-" + op] = (s["name"], fld, "hash-" + op.lower())
                else:
                    ops = ("get", "set", "length", "resize", "recog")
                    for op, nm in zip(ops, fld["names"]):
                        if nm:
                            self.prim_info[nm] = (s["name"], fld, kind + "-" + op)
                            if op == "length":
                                self.array_lengths.add(nm)

    def elt_type(self, fld):
        """(array ELT dims) -> ('u8'|'vector'|('stobj', name), fill datum)."""
        ftype = fld["type"]
        elt = ftype[1][1]
        if elt == ["L", [["y", "COMMON-LISP::UNSIGNED-BYTE"], 8], ["y", NIL]]:
            return "u8"
        if isinstance(elt, list) and elt[0] == "y" and elt[1] in self.stobjs:
            return ("stobj", elt[1])
        return "vector"

    def array_dim(self, fld):
        dims = datum_list(fld["type"][1][2]) if fld["type"][1][2][0] == "L" else None
        return dims[0] if dims else 0

    def creator_expr(self, stname):
        s = self.stobjs[stname]
        if s["abstract"]:
            return self.creator_expr(s["foundation"])
        parts = []
        for fld in s["fields"]:
            kind = fld["_kind"]
            if kind == "scalar":
                ftype = fld["type"]
                if isinstance(ftype, list) and ftype[0] == "y" and ftype[1] in self.stobjs:
                    parts.append(self.creator_expr(ftype[1]))
                else:
                    parts.append("'" + scm_datum(fld["init"]))
            elif kind == "hash":
                parts.append("(make-hash-table equal?)")
            else:
                n = self.array_dim(fld)
                et = self.elt_type(fld)
                if et == "u8":
                    parts.append("(make-u8vector %d %s)" % (n, scm_datum(fld["init"])))
                elif isinstance(et, tuple):
                    parts.append("(let ((v (make-vector %d))) (do ((i 0 (fx+ i 1))) ((fx>= i %d) v) (vector-set! v i %s)))"
                                 % (n, n, self.creator_expr(et[1])))
                else:
                    parts.append("(make-vector %d '%s)" % (n, scm_datum(fld["init"])))
        return "(vector " + " ".join(parts) + ")"

    def stobj_prim_def(self, name):
        f = self.fns[name]
        st = f.get("stobj")
        s = self.stobjs[st]
        if name == s["creator"]:
            return "(define (%s) %s)" % (fname(name), self.creator_expr(st))
        if name == s["recognizer"]:
            return "(define (%s x) '|COMMON-LISP::T|)" % fname(name)
        info = self.prim_info.get(name)
        if not info:
            return "(define (%s . args) (error \"stobj primitive not implemented\" '%s))" % (fname(name), scm_sym(name))
        _, fld, op = info
        i = fld["_index"]
        if op == "scalar-get":
            return "(define-inline (%s st) (##sys#slot st %d))" % (fname(name), i)
        if op == "scalar-set":
            return "(define-inline (%s v st) (##sys#setslot st %d v) st)" % (fname(name), i)
        if op in ("array-recog", "scalar-recog"):
            return "(define (%s x) (error \"logic-only recognizer\" '%s))" % (fname(name), scm_sym(name))
        et = self.elt_type(fld) if fld["_kind"] == "array" else None
        if op == "array-get":
            if et == "u8":
                return ("(define-inline (%s i st) (##core#inline \"C_u_i_u8vector_ref\" (##sys#slot st %d) i))"
                        % (fname(name), i))
            return "(define-inline (%s i st) (##sys#slot (##sys#slot st %d) i))" % (fname(name), i)
        if op == "array-set":
            if et == "u8":
                return ("(define-inline (%s i v st) (##core#inline \"C_u_i_u8vector_set\" (##sys#slot st %d) i v) st)"
                        % (fname(name), i))
            return "(define-inline (%s i v st) (##sys#setslot (##sys#slot st %d) i v) st)" % (fname(name), i)
        if op == "array-length":
            if et == "u8":
                return "(define-inline (%s st) (u8vector-length (##sys#slot st %d)))" % (fname(name), i)
            return "(define-inline (%s st) (vector-length (##sys#slot st %d)))" % (fname(name), i)
        if op == "array-resize":
            if et == "u8":
                return ("(define (%s n st) (##sys#setslot st %d (a-resize-u8vector (##sys#slot st %d) n %s)) st)"
                        % (fname(name), i, i, scm_datum(fld["init"])))
            fill = ("(lambda () %s)" % self.creator_expr(et[1])) if isinstance(et, tuple) \
                else "(lambda () '%s)" % scm_datum(fld["init"])
            return ("(define (%s n st) (##sys#setslot st %d (a-resize-vector (##sys#slot st %d) n %s)) st)"
                    % (fname(name), i, i, fill))
        if op == "hash-get":
            return "(define (%s k st) (hash-table-ref/default (##sys#slot st %d) k '()))" % (fname(name), i)
        if op == "hash-put":
            return "(define (%s k v st) (hash-table-set! (##sys#slot st %d) k v) st)" % (fname(name), i)
        if op == "hash-boundp":
            return "(define (%s k st) (a-bool (hash-table-exists? (##sys#slot st %d) k)))" % (fname(name), i)
        if op == "hash-rem":
            return "(define (%s k st) (hash-table-delete! (##sys#slot st %d) k) st)" % (fname(name), i)
        if op == "hash-count":
            return "(define (%s st) (hash-table-size (##sys#slot st %d)))" % (fname(name), i)
        if op == "hash-clear":
            return "(define (%s st) (##sys#setslot st %d (make-hash-table equal?)) st)" % (fname(name), i)
        return "(define (%s . args) (error \"stobj primitive op\" '%s))" % (fname(name), op)

    # --- constants ---------------------------------------------------------------------
    def literal(self, d):
        if isinstance(d, int) or d[0] in ("r", "x", "ch", "s"):
            return scm_datum(d)
        if d[0] == "y":
            return "'()" if d[1] == NIL else "'" + scm_sym(d[1])
        key = json.dumps(d, separators=(",", ":"))
        name = self.consts.get(key)
        if name is None:
            name = "k%d" % len(self.consts)
            self.consts[key] = name
            self.const_defs.append("(define %s '%s)" % (name, scm_datum(d)))
        return name

    # --- value counts ---------------------------------------------------------------------
    def nout(self, fn):
        f = self.fns.get(fn)
        if not f:
            return 1
        if f["kind"] == "alias":
            return self.nout(f["target"])
        return max(1, len(f["stobjs_out"]))

    def nvalues(self, t):
        if t[0] == "c":
            if t[1] == "COMMON-LISP::IF":
                return max(self.nvalues(t[2][1]), self.nvalues(t[2][2]))
            if t[1] in PRIMS or t[1] in PREDS:
                return 1
            return self.nout(t[1])
        if t[0] == "l":
            return self.nvalues(t[2])
        return 1

    def stobj_producing(self, t):
        if t[0] != "c":
            return t[0] == "l"
        f = self.fns.get(t[1])
        if f and any(x for x in f["stobjs_out"]):
            return True
        return any(self.stobj_producing(a) for a in t[2])

    # --- the predicate a guard conjunct states about a variable -----------------------
    def conj_interval(self, c, depth=0):
        """(var, Iv) for a conjunct that bounds an integer variable, else None."""
        why = [text(c)]
        if c[0] != "c":
            return None
        fn, args = c[1], c[2]
        if fn == "ACL2::UNSIGNED-BYTE-P" and qint(args[0]) is not None and args[1][0] == "v":
            return args[1][1], Iv(0, (1 << qint(args[0])) - 1, why)
        if fn == "ACL2::SIGNED-BYTE-P" and qint(args[0]) is not None and args[1][0] == "v":
            n = qint(args[0])
            return args[1][1], Iv(-(1 << (n - 1)), (1 << (n - 1)) - 1, why)
        if fn == "ACL2::NATP" and args[0][0] == "v":
            return args[0][1], Iv(0, INF, why)
        if fn == "ACL2::POSP" and args[0][0] == "v":
            return args[0][1], Iv(1, INF, why)
        if fn == "COMMON-LISP::<":
            a, b = args
            if a[0] == "v" and qint(b) is not None:
                return a[1], Iv(-INF, qint(b) - 1, why)
            if b[0] == "v" and qint(a) is not None:
                return b[1], Iv(qint(a) + 1, INF, why)
            if a[0] == "v" and b[0] == "c" and (b[1] in LENGTHISH or b[1] in self.array_lengths):
                return a[1], Iv(-INF, FIX_HI - 1,
                                [text(c) + " [an index below the length of a resident object is a fixnum]"])
        if fn == "COMMON-LISP::NOT" and args[0][0] == "c" and args[0][1] == "COMMON-LISP::<":
            a, b = args[0][2]
            if a[0] == "v" and qint(b) is not None:
                return a[1], Iv(qint(b), INF, why)
            if b[0] == "v" and qint(a) is not None:
                return b[1], Iv(-INF, qint(a), why)
        # A one-argument recognizer defined in the extracted set: its body's
        # conjuncts about its formal, unfolded (depth-limited).
        f = self.fns.get(fn)
        if (f and f["kind"] == "defun" and f["name"] not in SHIMS and len(f["formals"]) == 1 and len(args) == 1
                and args[0][0] == "v" and depth < 3):
            iv = self.pred_interval(fn, depth + 1)
            if iv is not None:
                return args[0][1], Iv(iv.lo, iv.hi, [text(c) + " = " + "; ".join(iv.why)])
        return None

    def pred_interval(self, fn, depth):
        if fn in self.pred_cache:
            return self.pred_cache[fn]
        self.pred_cache[fn] = None
        f = self.fns[fn]
        formal = f["formals"][0]
        iv = None
        body = f["body"]
        cs = conjuncts(body) if body[0] == "c" else []
        integer = False
        for c in cs:
            if c[0] == "c" and c[1] == "COMMON-LISP::INTEGERP" and c[2][0] == ["v", formal]:
                integer = True
            r = self.conj_interval(c, depth)
            if r and r[0] == formal:
                iv = iv_meet(iv, r[1])
        if iv is not None and not integer and "NATP" not in json.dumps(body) \
                and "BYTE-P" not in json.dumps(body):
            iv = None   # an interval without integerp is not an integer type
        self.pred_cache[fn] = iv
        return iv

    def guard_env(self, f):
        env = {}
        if f.get("class") != "common-lisp-compliant":
            return env
        integer_vars = set()
        for c in conjuncts(f["guard"]):
            if c[0] == "c" and c[1] in ("COMMON-LISP::INTEGERP", "ACL2::NATP", "ACL2::POSP",
                                        "ACL2::UNSIGNED-BYTE-P", "ACL2::SIGNED-BYTE-P"):
                v = c[2][-1]
                if v[0] == "v":
                    integer_vars.add(v[1])
            r = self.conj_interval(c)
            if r:
                var, iv = r
                env[var] = iv_meet(env.get(var), iv)
                fn = c[1]
                if fn in self.fns and self.fns[fn]["kind"] == "defun" and fn not in SHIMS and self.pred_interval(fn, 1) is not None:
                    integer_vars.add(var)
        return {v: iv for v, iv in env.items() if v in integer_vars}

    # --- expressions ---------------------------------------------------------------------
    def interval(self, t, env):
        if t[0] == "q":
            n = qint(t)
            return Iv(n, n, []) if n is not None else None
        if t[0] == "v":
            b = env.get(t[1])
            return b[1] if b and b[0] == "var" else None
        if t[0] == "l":
            return None
        fn, args = t[1], t[2]
        if fn == "ACL2::BINARY-+":
            a, b = self.interval(args[0], env), self.interval(args[1], env)
            if a and b:
                return Iv(a.lo + b.lo, a.hi + b.hi, a.why + b.why)
        if fn == "ACL2::BINARY-*":
            a, b = self.interval(args[0], env), self.interval(args[1], env)
            if a and b and all(abs(x) != INF for x in (a.lo, a.hi, b.lo, b.hi)):
                ps = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
                return Iv(min(ps), max(ps), a.why + b.why)
        if fn == "ACL2::UNARY--":
            a = self.interval(args[0], env)
            if a:
                return Iv(-a.hi, -a.lo, a.why)
        if fn == "ACL2::BINARY-LOGAND":
            a, b = self.interval(args[0], env), self.interval(args[1], env)
            nonneg = [x for x in (a, b) if x and x.lo >= 0]
            if nonneg:
                m = min(nonneg, key=lambda x: x.hi)
                return Iv(0, m.hi, m.why)
        if fn in ("ACL2::BINARY-LOGIOR", "ACL2::BINARY-LOGXOR"):
            a, b = self.interval(args[0], env), self.interval(args[1], env)
            if a and b and a.lo >= 0 and b.lo >= 0 and a.hi != INF and b.hi != INF:
                bits = max(int(a.hi).bit_length(), int(b.hi).bit_length())
                return Iv(0, (1 << bits) - 1, a.why + b.why)
        if fn == "COMMON-LISP::CHAR-CODE":
            return Iv(0, 255, ["char-code is below 256 (ACL2 characters)"])
        if fn == "COMMON-LISP::ASH":
            a, c = self.interval(args[0], env), qint(args[1])
            if a and c is not None and a.lo >= 0 and a.hi != INF:
                return Iv(0, (int(a.hi) << c) if c >= 0 else (int(a.hi) >> -c), a.why)
        if fn in self.array_lengths or fn in LENGTHISH:
            return Iv(0, FIX_HI, ["a resident object's length is a fixnum"])
        info = self.prim_info.get(fn)
        if info and info[2] == "array-get" and self.elt_type(info[1]) == "u8":
            return Iv(0, 255, ["an (unsigned-byte 8) array element"])
        return None

    def the_pattern(self, t):
        """((lambda (var) (the-check G 'TYPE var)) EXPR) -> (EXPR, G)."""
        if (t[0] == "l" and len(t[1]) == 1 and t[2][0] == "c" and t[2][1] == "ACL2::THE-CHECK"
                and t[2][2][2] == ["v", t[1][0]]):
            return t[3][0], t[2][2][0], t[1][0]
        return None

    def bool_of(self, s):
        return "(a-bool %s)" % s

    def emit_test(self, t, env):
        if t[0] == "q":
            return "#f" if datum_is_nil(t[1]) else "#t"
        if t[0] == "c":
            fn, args = t[1], t[2]
            if fn == "COMMON-LISP::IF":
                return "(if %s %s %s)" % (self.emit_test(args[0], env), self.emit_test(args[1], env),
                                          self.emit_test(args[2], self.else_env(args[0], env)))
            if fn in PREDS:
                return self.emit_pred(fn, args, env)
            if fn in INLINE and INLINE[fn][0]:
                return self.emit_inline_test(fn, args, env)
        return "(not (eq? %s '()))" % self.emit(t, env, 1)

    def emit_inline_test(self, fn, args, env):
        tmpl = INLINE[fn][0]
        if "{t0}" in tmpl:
            return tmpl.format(t0=self.emit_test(args[0], env))
        fact = self.eq_fact(["c", fn, args]) if fn in (
            "COMMON-LISP::EQ", "COMMON-LISP::EQL") else None
        if fact is not None and env.get(("neq",) + fact):
            return "#f"
        return tmpl.format(*[self.emit(a, env, 1) for a in args])

    @staticmethod
    def eq_fact(t):
        """(var, datum-key) when T is (equal var 'atom) or (equal 'atom var)."""
        if t[0] == "c" and t[1] in ("COMMON-LISP::EQUAL", "COMMON-LISP::EQ", "COMMON-LISP::EQL"):
            a, b = t[2]
            if a[0] == "q":
                a, b = b, a
            if a[0] == "v" and b[0] == "q":
                return (a[1], json.dumps(b[1]))
        return None

    def else_env(self, test, env):
        # In the else branch of (if (equal v 'c) ...), the same test is false.
        # ACL2's `case' repeats a key's test (fn-inj-month-days tests 2 twice);
        # folding the repeat keeps CHICKEN's switch free of duplicate labels.
        fact = self.eq_fact(test)
        if fact is None:
            return env
        e = dict(env)
        e[("neq",) + fact] = True
        return e

    def emit_pred(self, fn, args, env):
        fact = self.eq_fact(["c", fn, args])
        if fact is not None and env.get(("neq",) + fact):
            return "#f"
        xs = [self.emit(a, env, 1) for a in args]
        if fn == "COMMON-LISP::<":
            a, b = self.interval(args[0], env), self.interval(args[1], env)
            if a and b and a.fixnum() and b.fixnum() and self.cur_verified:
                self.erase("<", "fx<", args, [a, b])
                return "(fx< %s %s)" % (xs[0], xs[1])
        if fn == "COMMON-LISP::EQUAL":
            # Scheme equal? agrees with ACL2 equal on conses, numbers,
            # characters, strings and symbols; eqv? suffices on atoms.
            for a in args:
                if a[0] == "q" and (isinstance(a[1], int) or a[1][0] in ("y", "ch")):
                    return "(eqv? %s %s)" % (xs[0], xs[1])
        return PREDS[fn].format(*xs)

    def erase(self, op, to, args, ivs):
        self.erased.append({
            "function": self.cur,
            "operation": "(%s %s)" % (op.lower(), " ".join(text(a) for a in args)),
            "emitted": to,
            "erased": "generic-arithmetic dispatch and overflow promotion",
            "justification": sorted(set(w for iv in ivs for w in iv.why)) or ["literal"],
        })

    def emit(self, t, env, want):
        tag = t[0]
        if tag == "v":
            b = env.get(t[1])
            if b and b[0] == "tuple":
                s = "(list %s)" % " ".join(b[1])
            else:
                s = scm_sym(t[1])
            return s if want == 1 else "(apply values %s)" % s
        if tag == "q":
            if want == 1:
                return self.literal(t[1])
            elems = datum_list(t[1])
            if elems is not None and len(elems) == want:
                return "(values %s)" % " ".join(self.literal(e) for e in elems)
            return "(apply values %s)" % self.literal(t[1])
        if tag == "l":
            return self.emit_lambda(t, env, want)
        fn, args = t[1], t[2]
        if fn == "COMMON-LISP::IF":
            return "(if %s %s %s)" % (self.emit_test(args[0], env), self.emit(args[1], env, want),
                                      self.emit(args[2], self.else_env(args[0], env), want))
        if want > 1 and fn == "COMMON-LISP::CONS":
            elems, cur = [], t
            while cur[0] == "c" and cur[1] == "COMMON-LISP::CONS" and len(elems) < want:
                elems.append(cur[2][0])
                cur = cur[2][1]
            if len(elems) == want and cur[0] == "q" and datum_is_nil(cur[1]):
                return "(values %s)" % " ".join(self.emit(e, env, 1) for e in elems)
        if fn == "ACL2::RETURN-LAST":
            key = args[0][1] if args[0][0] == "q" else None
            if key == ["y", "COMMON-LISP::PROGN"]:
                return "(begin %s %s)" % (self.emit(args[1], env, 1), self.emit(args[2], env, want))
            return self.emit(args[2], env, want)
        if fn == "ACL2::MV-NTH" and qint(args[0]) is not None:
            i = qint(args[0])
            src = args[1]
            if src[0] == "v" and env.get(src[1], ("", None))[0] == "tuple":
                s = env[src[1]][1][i]
                return s if want == 1 else "(apply values %s)" % s
            n = self.nvalues(src)
            if n > 1:
                s = "(call-with-values (lambda () %s) (lambda vs (list-ref vs %d)))" % (self.emit(src, env, n), i)
                return s if want == 1 else "(apply values %s)" % s
        s = self.emit_call(fn, args, env)
        n = self.nvalues(t)
        if want == n:
            return s
        if want == 1:
            return "(call-with-values (lambda () %s) list)" % s
        if n == 1:
            return "(apply values %s)" % s
        raise ValueError("value count mismatch in %s: %s wants %d, has %d" % (self.cur, fn, want, n))

    def emit_call(self, fn, args, env):
        if self.cur_star1 and (fn in PREDS or fn in INLINE or fn in PRIMS):
            self.star1_call(fn, fn, self.fns.get(fn))
        if fn in PREDS:
            return self.bool_of(self.emit_pred(fn, args, env))
        if fn in INLINE:
            test, value = INLINE[fn]
            if value:
                return value.format(*[self.emit(a, env, 1) for a in args])
            return self.bool_of(self.emit_inline_test(fn, args, env))
        if fn in FX and self.cur_verified:
            ivs = [self.interval(a, env) for a in args]
            res = self.interval(["c", fn, args], env)
            if all(iv and iv.fixnum() for iv in ivs) and res and res.fixnum():
                self.erase(short(fn), FX[fn], args, ivs + [res])
                return "(%s %s)" % (FX[fn], " ".join(self.emit(a, env, 1) for a in args))
        if fn == "ACL2::THE-CHECK":
            return self.emit(args[2], env, 1)
        xs = [self.emit(a, env, 1) for a in args]
        order = any(self.stobj_producing(a) for a in args) and len(args) > 1
        if fn in PRIMS:
            call = PRIMS[fn].format(*xs) if not order else None
            if call:
                return call
        f = self.fns.get(fn)
        target = fn
        while f and f["kind"] == "alias":
            target = f["target"]
            f = self.fns.get(target)
        if self.cur_star1:
            self.star1_call(fn, target, f)
        if fn in SHIMS or target in SHIMS:
            head = SHIMS.get(fn) or SHIMS[target]
        elif self.native and target in NATIVE and self.cur not in NATIVE:
            head = NATIVE[target]
        elif fn in PRIMS:
            head = None
        elif self.cur_star1 and fn in self.checked_needed:
            head = scm_sym("c:" + fn)
        else:
            head = fname(target)
            info = self.prim_info.get(target)
            if info and info[2] in ("array-get", "array-set") and self.cur_verified:
                self.erased.append({
                    "function": self.cur,
                    "operation": "(%s %s)" % (short(target).lower(), " ".join(text(a) for a in args)),
                    "emitted": "unchecked vector access",
                    "erased": "array bounds and element-type checks",
                    "justification": ["the guard of %s (a natp index below the array's length%s) is a guard "
                                      "obligation of %s, discharged by its guard verification"
                                      % (short(target).lower(),
                                         ", an (unsigned-byte 8) value" if info[2] == "array-set"
                                         and self.elt_type(info[1]) == "u8" else "",
                                         short(self.cur).lower())],
                })
        if not order:
            return "(%s %s)" % (head, " ".join(xs)) if head else PRIMS[fn].format(*xs)
        temps = ["%%a%d" % self.gensym() for _ in xs]
        binds = " ".join("(%s %s)" % (tv, x) for tv, x in zip(temps, xs))
        inner = "(%s %s)" % (head, " ".join(temps)) if head else PRIMS[fn].format(*temps)
        return "(let* (%s) %s)" % (binds, inner)

    def gensym(self):
        self.counter += 1
        return self.counter

    def emit_lambda(self, t, env, want):
        formals, body, actuals = t[1], t[2], t[3]
        the = self.the_pattern(t)
        if the is not None:
            expr, g, var = the
            return self.emit(expr, env, want)
        new_env = {k: v for k, v in env.items()
                   if not (isinstance(k, tuple) and k[1] in formals)}
        plain, tuples = [], []
        for v, a in zip(formals, actuals):
            n = self.nvalues(a)
            if n > 1:
                names = ["%%t%d" % self.gensym() for _ in range(n)]
                tuples.append((v, names, self.emit(a, env, n)))
                new_env[v] = ("tuple", names)
            else:
                iv = self.interval(a, env)
                the2 = self.the_pattern(a) if a[0] == "l" else None
                if the2 is not None:
                    r = self.conj_interval(the2[1])
                    if r:
                        iv = iv_meet(iv, Iv(r[1].lo, r[1].hi, ["(the %s) declared" % text(the2[1])]))
                plain.append((v, self.emit(a, env, 1)))
                new_env[v] = ("var", iv)
        inner = self.emit(body, new_env, want)
        ordered = any(self.stobj_producing(a) for a in actuals) and len(actuals) > 1
        if plain:
            if ordered:
                temps = [("%%l%d" % self.gensym(), v, x) for v, x in plain]
                inner = "(let* (%s) (let (%s) %s))" % (
                    " ".join("(%s %s)" % (tv, x) for tv, v, x in temps),
                    " ".join("(%s %s)" % (scm_sym(v), tv) for tv, v, x in temps), inner)
            else:
                inner = "(let (%s) %s)" % (" ".join("(%s %s)" % (scm_sym(v), x) for v, x in plain), inner)
        for v, names, expr in reversed(tuples):
            inner = "(call-with-values (lambda () %s) (lambda (%s) %s))" % (expr, " ".join(names), inner)
        return inner

    # --- functions ------------------------------------------------------------------------
    def emit_defun(self, f):
        self.cur = f["name"]
        self.counter = 0
        self.cur_verified = f.get("class") == "common-lisp-compliant"
        self.cur_star1 = f.get("class") == "program" and f.get("invariant_risk", False)
        genv = self.guard_env(f)
        env = {v: ("var", genv.get(v)) for v in f["formals"]}
        want = self.nout(f["name"])
        body = self.emit(f["body"], env, want)
        return "(define (%s %s)\n  %s)" % (fname(f["name"]), " ".join(scm_sym(v) for v in f["formals"]), body)

    # --- *1* bodies (invariant risk) ------------------------------------------------------------
    # A :program function with ACL2's `invariant-risk' property (it may reach a
    # stobj updater) runs, under the image's check-invariant-risk t, its *1*
    # body (interface-raw.lisp oneify, **1*-as-raw* t): each call in it to a
    # function G checks G's guard before G runs raw, except a call to another
    # invariant-risk :program function, whose own body is a *1* body in turn.
    # The backend emits exactly those checks, as |c:G| (G's guard, then
    # |f:G|).  A primitive with a guard (car, <, ...) called from such a body
    # would need its *1* check as well: none is reached today, and the
    # backend refuses to build one rather than leave it unchecked.
    STAR1_UNCHECKED_OK = {"COMMON-LISP::CONS", "COMMON-LISP::CONSP", "COMMON-LISP::EQUAL",
                          "COMMON-LISP::INTEGERP", "COMMON-LISP::RATIONALP", "ACL2::ACL2-NUMBERP",
                          "COMMON-LISP::COMPLEX-RATIONALP", "COMMON-LISP::CHARACTERP",
                          "COMMON-LISP::STRINGP", "COMMON-LISP::SYMBOLP", "COMMON-LISP::NOT",
                          "COMMON-LISP::NULL", "COMMON-LISP::ATOM", "COMMON-LISP::EQL",
                          "ACL2::NATP", "ACL2::POSP", "ACL2::BOOLEANP", "ACL2::NFIX", "ACL2::IFIX",
                          "ACL2::FIX", "COMMON-LISP::IF"}

    def live_guard(self, f):
        formals = f["formals"]
        stobjs_in = f["stobjs_in"] or [None] * len(formals)
        stobj_formals = {v for v, st in zip(formals, stobjs_in) if st}
        return self.drop_live_recognizers(f["guard"], stobj_formals, self.stobj_recognizers())

    def star1_call(self, fn, target, f):
        if fn in self.STAR1_UNCHECKED_OK:
            return
        if fn in PRIMS or fn in PREDS or fn in INLINE:
            raise ValueError("%s: a *1* body (invariant risk) calls the guarded primitive %s; "
                             "its *1* guard check is not implemented" % (self.cur, fn))
        # The guard checked is the CALLED function's: an abstract stobj's
        # export has its own guard (its :logic guard, stobj conjuncts aside),
        # not its :exec function's (which also states the concrete invariant).
        called = self.fns.get(fn)
        if target in SHIMS or not f or f["kind"] != "defun" or not called or "guard" not in called:
            return
        if f.get("class") == "program" and f.get("invariant_risk", False):
            return
        if self.live_guard(called) != ["q", ["y", T]]:
            self.checked_needed.add(fn)

    def checked_def(self, name):
        f = self.fns[name]
        target = name
        while self.fns[target]["kind"] == "alias":
            target = self.fns[target]["target"]
        formals = f["formals"]
        saved = (self.cur, self.cur_verified, self.cur_star1, self.counter)
        self.cur, self.cur_verified, self.cur_star1, self.counter = name, False, False, 0
        env = {v: ("var", None) for v in formals}
        test = self.emit_test(self.live_guard(f), env)
        self.cur, self.cur_verified, self.cur_star1, self.counter = saved
        args = " ".join(scm_sym(v) for v in formals)
        return ("(define (%s %s)\n  (if %s (%s %s) (a-guard-violation %s (list %s))))"
                % (scm_sym("c:" + name), args, test, fname(target), args, scm_string(short(name)), args))

    # --- the boundary (e1) ------------------------------------------------------------------
    # THE RULE.  A boundary function is one the host driver calls (a root of
    # the extraction; host/native/io.lisp calls it through fnn-call).  Its
    # procedure |b:F| does what fnn-call and F's *1* counterpart do under
    # guard-checking t, in their order: (1) the arity and the KIND conjuncts
    # of F's guard (fnn-entry-guard; the front end computes the checks exactly
    # as fnn-entry-guard-spec does), refused as a host-entry-guard fault with
    # fnn-entry-guard's own message; (2) F's WHOLE guard, refused as a guard
    # violation of F (the fault fnn-call raises when the *1* function throws);
    # (3) the raw procedure |f:F|.  A stobj recognizer applied to its own
    # stobj formal is true of the live stobj and is not evaluated (the *1*
    # code never evaluates it on a live stobj either).  Every call INSIDE
    # the program is to |f:G|, unchecked: G's guard is a guard obligation of
    # its caller, discharged by the caller's guard verification.
    def stobj_recognizers(self):
        rec = {"ACL2::STATE-P", "ACL2::STATE-P1"}
        for st in self.ir["stobjs"]:
            rec.add(st["recognizer"])
        for f in self.ir["functions"]:
            if f["kind"] == "alias" and f.get("target") and f["name"].endswith("-P"):
                rec.add(f["name"])
        return rec

    def drop_live_recognizers(self, t, stobj_formals, recs):
        if t[0] == "c":
            if (t[1] in recs and len(t[2]) == 1 and t[2][0][0] == "v"
                    and t[2][0][1] in stobj_formals):
                return ["q", ["y", T]]
            return ["c", t[1], [self.drop_live_recognizers(a, stobj_formals, recs) for a in t[2]]]
        if t[0] == "l":
            return ["l", t[1], self.drop_live_recognizers(t[2], stobj_formals, recs),
                    [self.drop_live_recognizers(a, stobj_formals, recs) for a in t[3]]]
        return t

    def boundary_def(self, b, recs):
        name = b["name"]
        f = self.fns[name]
        target = name
        while self.fns.get(target, {}).get("kind") == "alias":
            target = self.fns[target]["target"]
        formals = f["formals"]
        stobjs_in = f["stobjs_in"] or [None] * len(formals)
        stobj_formals = {v for v, st in zip(formals, stobjs_in) if st}
        self.cur, self.cur_verified, self.counter = name, False, 0
        env = {v: ("var", None) for v in formals}
        lname = scm_string(short(name).lower())
        body = []
        for pos, formal, recog, kind in b["checks"]:
            test = self.emit_test(["c", recog, [["v", formal]]], env)
            body.append("(unless %s (a-entry-kind-fault %s %d %s %s %s %s))"
                        % (test, lname, pos + 1, scm_string(short(formal).lower()), scm_string(kind),
                           scm_string(short(recog).lower()), scm_sym(formal)))
        guard = self.drop_live_recognizers(b["guard"], stobj_formals, recs)
        if guard != ["q", ["y", T]]:
            body.append("(unless %s (a-guard-violation %s (list %s)))"  # the entry's own guard
                        % (self.emit_test(guard, env), scm_string(short(name)),
                           " ".join(scm_sym(v) for v in formals)))
        call = "(%s %s)" % (fname(target), " ".join(scm_sym(v) for v in formals)) \
            if target not in SHIMS else "(%s %s)" % (SHIMS[target], " ".join(scm_sym(v) for v in formals))
        return ("(define (%s . args)\n  (set! a-current-entry %s)\n  (a-entry-arity %s %d args)\n"
                "  (apply (lambda (%s)\n    %s\n    (a-entry-call %s (lambda () %s))) args))"
                % (scm_sym("b:" + name), lname, lname, len(formals), " ".join(scm_sym(v) for v in formals),
                   "\n    ".join(body) if body else "#t", lname, call))

    def program(self):
        out = [";;; generated by tools/extract/chicken.py from %s roots: %s"
               % (len(self.ir["functions"]), " ".join(self.ir["roots"]))]
        out.append("(declare (block) (fixnum-arithmetic-off))" if False else "")
        defs = []
        prims_out = []
        inventory = {"defun": 0, "stobj-prim": 0, "prim": 0, "alias": 0, "shim": [], "blocker": []}
        for f in self.ir["functions"]:
            k, n = f["kind"], f["name"]
            if n in SHIMS or n in INLINE:
                inventory["shim"].append({"name": n, "why": SHIM_CLASS.get(
                    n, "raw-Lisp built-in compiled inline" if n in INLINE
                    else "raw-Lisp built-in (Common Lisp's function)"), "was": k})
                continue
            if k == "defun":
                defs.append(self.emit_defun(f))
                inventory["defun"] += 1
            elif k == "stobj-prim":
                # first: define-inline must precede its uses
                prims_out.append(self.stobj_prim_def(n))
                inventory["stobj-prim"] += 1
            elif k == "prim":
                inventory["prim"] += 1
            elif k == "alias":
                inventory["alias"] += 1
            elif k == "shim":
                inventory["shim"].append({"name": n, "why": SHIM_CLASS.get(n, "raw-only"), "was": k})
            elif k == "blocker":
                inventory["blocker"].append({"name": n, "reason": f["reason"]})
                defs.append("(define (%s . args) (error \"extractor blocker\" '%s %s))"
                            % (fname(n), scm_sym(n), scm_string(f["reason"])))
        # aliases whose target is a creator/recognizer need a name too: callers use the target.
        recs = self.stobj_recognizers()
        boundary = [self.boundary_def(b, recs) for b in self.ir.get("boundary", [])]
        checked = [self.checked_def(n) for n in sorted(self.checked_needed)]
        inventory["star1_checked"] = sorted(self.checked_needed)
        inventory["star1_bodies"] = [f["name"] for f in self.ir["functions"]
                                     if f["kind"] == "defun" and f.get("class") == "program"
                                     and f.get("invariant_risk", False)]
        inventory["boundary"] = [b["name"] for b in self.ir.get("boundary", [])]
        out.extend(self.const_defs)
        out.extend(prims_out)
        out.extend(defs)
        out.extend(checked)
        out.extend(boundary)
        return "\n".join(out) + "\n", inventory


def main():
    p = argparse.ArgumentParser()
    p.add_argument("ir")
    p.add_argument("--out", required=True)
    p.add_argument("--erased", required=True)
    p.add_argument("--inventory", required=True)
    p.add_argument("--table", help="also write a name -> procedure table (fcheck-main.scm)")
    p.add_argument("--no-native", action="store_true",
                   help="the ACL2 SHA-256 everywhere (no native.scm; fcheck-main.scm's build)")
    a = p.parse_args()
    ir = json.load(open(a.ir))
    b = Backend(ir)
    b.native = not a.no_native
    text_, inv = b.program()
    with open(a.out, "w") as h:
        h.write(text_)
    if a.table:
        with open(a.table, "w") as h:
            h.write("(define extracted-functions (make-hash-table string=?))\n")
            for f in ir["functions"]:
                if f["kind"] != "defun":
                    continue
                if f["name"] in SHIMS or f["name"] in INLINE:
                    # the shim, as a procedure, so the differential checks it
                    b.cur, b.cur_verified, b.counter = f["name"], False, 0
                    env = {v: ("var", None) for v in f["formals"]}
                    call = b.emit_call(f["name"], [["v", v] for v in f["formals"]], env)
                    proc = "(lambda (%s) %s)" % (" ".join(scm_sym(v) for v in f["formals"]), call)
                else:
                    proc = fname(f["name"])
                h.write("(hash-table-set! extracted-functions %s %s)\n" % (scm_string(f["name"]), proc))
    with open(a.erased, "w") as h:
        json.dump(b.erased, h, indent=1)
    with open(a.inventory, "w") as h:
        json.dump(inv, h, indent=1)
    print("functions %d; defuns %d; stobj primitives %d; aliases %d; shims %d; blockers %d; erased checks %d"
          % (len(ir["functions"]), inv["defun"], inv["stobj-prim"], inv["alias"], len(inv["shim"]),
             len(inv["blocker"]), len(b.erased)))


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    main()
