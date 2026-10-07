#!/usr/bin/env python3
"""Drain hand-written loop twins into `def-loop' forms (books/def-loop.lisp).

A hand twin is four things in a book: a tail-recursive `NAME-loop' defun, the
wrapper `NAME' whose `(mbe :logic <recursion> :exec (NAME-loop ... nil))' is
the structural recursion, a bridge theorem `NAME-loop-is-*' and the two
`verify-guards'.  `def-loop' emits all of it from one form.  This tool reads
the WRAPPER's :logic recursion (the loop is never trusted: the generated
bridge is proved over the generated loop), recognises its shape, and rewrites
the four things into one `def-loop' form.

    tools/def_loop_drain.py --check BOOK...       report only, writes nothing
    tools/def_loop_drain.py --apply BOOK...       rewrite the books in place
    tools/def_loop_drain.py --residual [--out F]  every refused loop in books/

Shapes taken: :map (with :let :stop :keep :keep-order :while :tail :stobjs),
:sum, :concat, :take.  Everything else is refused with a named reason, and
the refusal list is the tree's fold / step / non-generator inventory:

    fold          the exec seeds an accumulator that is not nil / 0, or the
                  loop threads more than the list (a state, a started flag)
    rev-input     the exec reverses its input first (a fold from the right)
    step          the recursion steps by other than (cdr XS) (cddr, nthcdr...)
    two-list      the recursion steps two lists together
    mv            the logic returns multiple values
    pair-result   the recursion's result is destructured (split, partition)
    exec-differs  the exec loop's terms differ from the logic's (fix, ag-car):
                  the loop is what makes the guards provable
    late-guard    a function the body calls has its verify-guards later in the
                  same book, and def-loop verifies guards at its own position
    concat-multi  an append of several pieces per element (assoc changes)
    no-wrapper    NAME-loop with no wrapper NAME, or no mbe
    no-shape      none of the above recognises the logic
    loop-referenced  NAME-loop is named outside the twin it would delete

The tool reads s-expressions with positions (comments and strings kept): a
regex over parentheses is wrong on `#\\(' and strings.  Comments inside the
wrapper are hoisted above the generated form, never dropped.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

ROOT = Path(os.environ.get("DEF_LOOP_DRAIN_ROOT") or Path(__file__).resolve().parent.parent)

# --------------------------------------------------------------------------
# reader and printer: tools/lisp_rewrite.py (the one shared reader)

from lisp_rewrite import Atom, Str, Pre, Lst, ReadError, flat, emit, parse, write  # noqa: E402


# the tree's hand-written def-loop forms wrap at about 100 columns (84 matched 28 of 64
# landed conversions byte for byte, 100 matches 33)
WIDTH = 100


def read_all(text: str):
    """Top-level data of TEXT and the comments between them as (start, text)."""
    p = parse(text)
    return p.forms, p.comments


def pretty(n, indent=0, width=WIDTH) -> str:
    return emit(n, indent=indent, width=width, layout="aligned", drop_comments=True)


# --------------------------------------------------------------------------
# helpers over trees


def S(x):  # build an atom
    return Atom(x)


def L(*items):
    return Lst(list(items))


def is_call(n, name=None):
    return (isinstance(n, Lst) and n.items and isinstance(n.items[0], Atom)
            and not isinstance(n.items[0], Str)
            and (name is None or n.items[0].low == name))


def head(n):
    return n.items[0].low if is_call(n) else None


def eq(a, b):
    return flat_low(a) == flat_low(b)


def flat_low(n):
    return flat(n).lower() if not isinstance(n, Atom) else n.text.lower()


def contains(n, pred):
    if pred(n):
        return True
    if isinstance(n, Pre):
        return contains(n.node, pred)
    if isinstance(n, Lst):
        return any(contains(i, pred) for i in n.items)
    return False


def mentions(n, sym):
    sym = sym.lower()
    return contains(n, lambda x: isinstance(x, Atom) and not isinstance(x, Str)
                    and x.low == sym)


def subst(n, pred, repl):
    if pred(n):
        return repl
    if isinstance(n, Pre):
        return Pre(n.prefix, subst(n.node, pred, repl))
    if isinstance(n, Lst):
        return Lst([subst(i, pred, repl) for i in n.items])
    return n


def fn_names(n, out):
    """Every symbol in function position under N (quoted data excluded)."""
    if isinstance(n, Pre):
        if n.prefix not in ("'", "#'"):
            fn_names(n.node, out)
        elif n.prefix == "#'" and isinstance(n.node, Atom):
            out.add(n.node.low)
        return
    if isinstance(n, Lst):
        if is_call(n):
            if n.items[0].low == "quote":
                return
            out.add(n.items[0].low)
        for i in n.items[1:] if is_call(n) else n.items:
            fn_names(i, out)


class Refuse(Exception):
    def __init__(self, reason, detail=""):
        super().__init__(reason)
        self.reason = reason
        self.detail = detail


def inline_rec_lets(n, name):
    """(let ((r (NAME ...))) BODY) -> BODY with r replaced by the call: the
    recursion's result named, which the matcher reads at its use sites."""
    if isinstance(n, Pre):
        return Pre(n.prefix, inline_rec_lets(n.node, name))
    if not isinstance(n, Lst):
        return n
    items = [inline_rec_lets(i, name) for i in n.items]
    if (is_call(n, "let") or is_call(n, "let*")) and len(items) == 3 \
            and isinstance(items[1], Lst) and len(items[1].items) == 1:
        b = items[1].items[0]
        if isinstance(b, Lst) and len(b.items) == 2 and isinstance(b.items[0], Atom) \
                and is_call(b.items[1], name):
            var = b.items[0].low
            return subst(items[2], lambda x: isinstance(x, Atom) and not isinstance(x, Str)
                         and x.low == var, b.items[1])
    return Lst(items)


def cond_to_if(n):
    """Rewrite every `cond' under N as nested `if'."""
    if isinstance(n, Pre):
        return Pre(n.prefix, cond_to_if(n.node))
    if not isinstance(n, Lst):
        return n
    items = [cond_to_if(i) for i in n.items]
    if is_call(n, "cond"):
        clauses = items[1:]
        out = None
        for cl in reversed(clauses):
            if not isinstance(cl, Lst) or len(cl.items) != 2:
                raise Refuse("no-shape", "cond clause with other than 2 parts")
            test, val = cl.items
            if out is None:
                if isinstance(test, Atom) and test.low == "t":
                    out = val
                else:
                    out = L(S("if"), test, val, S("nil"))
            else:
                out = L(S("if"), test, val, out)
        return out
    return Lst(items)


# --------------------------------------------------------------------------
# a book


@dataclass
class Form:
    node: object
    start: int
    end: int
    name: str | None
    kind: str | None


def book_forms(text):
    data, comments = read_all(text)
    forms = []
    for n in data:
        kind = name = None
        if isinstance(n, Lst) and is_call(n) and len(n.items) > 1:
            kind = n.items[0].low
            second = n.items[1]
            if isinstance(second, Atom):
                name = second.low
            elif kind == "local" and isinstance(second, Lst) and is_call(second) \
                    and len(second.items) > 1 and isinstance(second.items[1], Atom):
                kind = "local-" + second.items[0].low
                name = second.items[1].low
        forms.append(Form(n, n.start, n.end, name, kind))
    return forms, comments


def xargs_of(defun: Lst):
    """The :keyword -> node dict of the defun's (declare (xargs ...))s."""
    out = {}
    for it in defun.items[3:]:
        if is_call(it, "declare"):
            for d in it.items[1:]:
                if is_call(d, "xargs"):
                    ks = d.items[1:]
                    for i in range(0, len(ks) - 1, 2):
                        if isinstance(ks[i], Atom):
                            out[ks[i].low] = ks[i + 1]
    return out


def body_of(defun: Lst):
    """The defun's body (last item that is not a declare, string or comment)."""
    return defun.items[-1]


# --------------------------------------------------------------------------
# matching


@dataclass
class Spec:
    shape: str
    name: str
    formals: Lst
    xs: str
    elt: str = "e"
    count: str | None = None
    lets: Lst | None = None
    stop: object = None
    stopval: object = None
    keep: object = None
    skip_first: bool = False
    while_: object = None
    tail: object = None
    body: object = None
    stobjs: list = field(default_factory=list)
    guard: object = None
    row_term: object = None  # :fold
    st: str | None = None
    fail: object = None
    guard_hints: object = None
    done: object = None      # :step
    emit: object = None
    skip: object = None
    next: object = None      # one term, or a list of terms (several :over formals)
    skip_next: object = None
    svars: list = field(default_factory=list)
    measure: object = None
    combine: object = None   # :foldr
    init: object = None
    rev: str | None = None
    loop_guard: object = None


def formals_of(defun):
    f = defun.items[2]
    if not isinstance(f, Lst):
        raise Refuse("no-shape", "formals")
    return f


def atoms_of(n, out):
    if isinstance(n, Pre):
        atoms_of(n.node, out)
    elif isinstance(n, Lst):
        for i in n.items:
            atoms_of(i, out)
    elif isinstance(n, Atom) and not isinstance(n, Str):
        out.add(n.low)
    return out


def pick_elt(xs, formals, used=()):
    taken = {i.low for i in formals.items if isinstance(i, Atom)} | set(used)
    for c in (xs[0], "e", "x", "y", "z", "w", "u", "v"):
        c = c.lower()
        if c not in ("t", "nil") and c not in taken:
            return c
    raise Refuse("no-shape", "no free element name")


def is_consp_of(c, xs):
    return is_call(c, "consp") and len(c.items) == 2 and flat_low(c.items[1]) == xs


def is_atom_of(c, xs):
    if is_call(c, "atom") and len(c.items) == 2 and flat_low(c.items[1]) == xs:
        return True
    return (is_call(c, "not") and len(c.items) == 2
            and is_consp_of(c.items[1], xs))


def negate(c):
    if is_call(c, "atom") and len(c.items) == 2:
        return L(S("consp"), c.items[1])
    if is_call(c, "not") and len(c.items) == 2:
        return c.items[1]
    return L(S("not"), c)


def and_of(parts):
    return parts[0] if len(parts) == 1 else Lst([S("and")] + parts)


def split_test(c, xs):
    """(polarity, while_term or None): `C' as 'consp XS and W' (True) or its
    negation (False), else None."""
    if is_consp_of(c, xs):
        return True, None
    if is_atom_of(c, xs):
        return False, None
    if is_call(c, "and") and len(c.items) > 2 and is_consp_of(c.items[1], xs):
        return True, and_of(c.items[2:])
    if is_call(c, "or") and len(c.items) > 2 and is_atom_of(c.items[1], xs):
        return False, and_of([negate(i) for i in c.items[2:]])
    return None


def rec_call(n, name, formals, xs):
    """Is N a call (NAME a...) stepping only XS by (cdr XS)?  Reason or None."""
    if not (is_call(n, name) and len(n.items) == len(formals.items) + 1):
        return False
    for f, a in zip(formals.items, n.items[1:]):
        if f.low == xs:
            if not (is_call(a, "cdr") and flat_low(a.items[1]) == xs):
                return False
        elif not (isinstance(a, Atom) and a.low == f.low):
            return False
    return True


def any_rec(n, name):
    return contains(n, lambda x: is_call(x, name))


def classify_nonshape(name, formals, logic, loop_body, exec_call):
    """A named reason for a wrapper that no shape matched."""
    low = flat_low(logic)
    if "mv-let" in low or "(mv " in low:
        return Refuse("mv")
    if exec_call is not None:
        args = exec_call.items[1:]
        if any(is_call(a, "fn-ag-rev-onto") or is_call(a, "reverse") for a in args):
            return Refuse("rev-input")
        if args and not (isinstance(args[-1], Atom) and args[-1].low in ("nil", "0")):
            return Refuse("fold", "seeded accumulator")
    for c in [i for i in walk_calls(logic, name)]:
        steps = [a for a in c.items[1:] if is_call(a, "cdr") or is_call(a, "cddr")
                 or is_call(a, "nthcdr") or is_call(a, "cadr")]
        cd = [a for a in c.items[1:] if is_call(a, "cddr") or is_call(a, "nthcdr")
              or (is_call(a, "cdr") and is_call(a.items[1], "cdr"))]
        if cd:
            return Refuse("step")
        if len([a for a in steps if is_call(a, "cdr")]) >= 2:
            return Refuse("two-list")
    if contains(logic, lambda x: is_call(x, name) and False):
        pass
    if loop_body is not None:
        lf = {i.low for i in loop_body.items[2].items} if isinstance(loop_body.items[2], Lst) else set()
        wf = {i.low for i in formals.items}
        if len(lf - wf) > 1:
            return Refuse("fold", "loop threads more than one extra")
    if re.search(r"\(let\*?\s+\(\(\w[\w-]*\s+\(" + re.escape(name.lower()), low) or \
            re.search(r"\(let\*?\s+\(\(\w[\w-]* \(" + re.escape(name.lower()), low):
        return Refuse("pair-result", "recursion result is bound and inspected")
    return Refuse("no-shape")


def walk_calls(n, name):
    if isinstance(n, Pre):
        yield from walk_calls(n.node, name)
    elif isinstance(n, Lst):
        if is_call(n, name):
            yield n
        for i in n.items:
            yield from walk_calls(i, name)


def match_inner(inner, spec_name, formals, xs, spec):
    """Peel lets / stop / keep around the cons; fill SPEC.  Raises Refuse."""
    n = inner
    lets = []
    while True:
        if is_call(n, "let") or is_call(n, "let*"):
            if len(n.items) != 3 or not isinstance(n.items[1], Lst):
                raise Refuse("no-shape", "let form")
            lets.extend(n.items[1].items)
            n = n.items[2]
            continue
        break
    if lets:
        spec.lets = Lst(lets)
    if is_call(n, "if") and len(n.items) == 4:
        c, a, b = n.items[1:]
        ra, rb = any_rec(a, spec_name), any_rec(b, spec_name)
        if (not ra) and rb:
            # stop: C returns A, else go on
            spec.stop, spec.stopval = c, a
            return match_inner(b, spec_name, formals, xs, spec)
        if (not rb) and ra:
            spec.stop, spec.stopval = L(S("not"), c), b
            return match_inner(a, spec_name, formals, xs, spec)
        if is_call(a, "cons") and rec_call(b, spec_name, formals, xs) and len(a.items) == 3 \
                and rec_call(a.items[2], spec_name, formals, xs):
            spec.keep, spec.body = c, a.items[1]
            return
        if is_call(b, "cons") and rec_call(a, spec_name, formals, xs) and len(b.items) == 3 \
                and rec_call(b.items[2], spec_name, formals, xs):
            spec.keep, spec.body, spec.skip_first = c, b.items[1], True
            return
        raise Refuse("no-shape", "if inside the step")
    if is_call(n, "cons") and len(n.items) == 3 and rec_call(n.items[2], spec_name, formals, xs):
        spec.body = n.items[1]
        return
    raise Refuse("no-shape", "step is not (cons BODY (NAME ... (cdr XS) ...))")


def shape_of(name, formals, logic, wrapper):
    """The Spec of LOGIC (the :logic recursion of NAME), or a Refuse."""
    logic = cond_to_if(inline_rec_lets(logic, name))
    if not (is_call(logic, "if") and len(logic.items) == 4):
        raise Refuse("no-shape", "logic is not an if")
    fl = [f.low for f in formals.items]
    c, a, b = logic.items[1:]
    # find the xs formal: the one a leading consp/atom test names
    xs = None
    for f in fl:
        if split_test(c, f) is not None:
            xs = f
            break
    # :take tests (zp N) as well as the list
    count = None
    if xs is None and is_call(c, "or"):
        for f in fl:
            if any(is_atom_of(i, f) for i in c.items[1:]):
                xs = f
    if xs is None:
        raise Refuse("no-shape", "no leading (consp XS) test")
    spec = Spec("map", name, formals, xs)
    # take: (or (zp N) (atom XS))
    if is_call(c, "or") and any(is_call(i, "zp") for i in c.items[1:]):
        zps = [i for i in c.items[1:] if is_call(i, "zp")]
        rest = [i for i in c.items[1:] if not is_call(i, "zp")]
        if len(zps) == 1 and len(rest) == 1 and is_atom_of(rest[0], xs):
            count = flat(zps[0].items[1])
            if not is_call(b, "cons") or len(b.items) != 3:
                raise Refuse("no-shape", "take step")
            rec = b.items[2]
            ok = is_call(rec, name) and len(rec.items) == len(fl) + 1
            for f, arg in zip(fl, rec.items[1:] if ok else []):
                if f == xs:
                    ok = ok and is_call(arg, "cdr") and flat_low(arg.items[1]) == xs
                elif f == count.lower():
                    ok = ok and (is_call(arg, "1-") or is_call(arg, "-")) and \
                        flat_low(arg.items[1]) == f
                else:
                    ok = ok and isinstance(arg, Atom) and arg.low == f
            if not ok:
                raise Refuse("no-shape", "take recursion")
            spec.shape, spec.count = "take", count
            spec.body = b.items[1]
            spec.tail = None if (isinstance(a, Atom) and a.low == "nil") else a
            spec.while_ = L(S("consp"), S(xs))
            return finish(spec, name, formals, wrapper, fl)
        raise Refuse("no-shape", "take test")
    pol_while = split_test(c, xs)
    pol, wh = pol_while
    inner, tail = (a, b) if pol else (b, a)
    spec.while_ = wh
    spec.tail = None if (isinstance(tail, Atom) and tail.low == "nil") else tail
    # sum
    if is_call(inner, "+") and len(inner.items) >= 3 and rec_call(inner.items[-1], name, formals, xs) \
            and isinstance(tail, Atom) and tail.text == "0" and wh is None \
            and not any(any_rec(i, name) for i in inner.items[1:-1]):
        terms = inner.items[1:-1]
        spec.shape, spec.body, spec.tail = "sum", (terms[0] if len(terms) == 1 else Lst([S("+")] + terms)), None
        return finish(spec, name, formals, wrapper, fl)
    if is_call(inner, "append"):
        if len(inner.items) != 3 or not rec_call(inner.items[2], name, formals, xs):
            raise Refuse("concat-multi")
        if wh is not None or spec.tail is not None:
            raise Refuse("no-shape", "concat with while/tail")
        spec.shape, spec.body = "concat", inner.items[1]
        return finish(spec, name, formals, wrapper, fl)
    for c2 in walk_calls(inner, name):
        for arg, f in zip(c2.items[1:], fl):
            if f != xs and not (isinstance(arg, Atom) and arg.low == f):
                if is_call(arg, "cdr") or is_call(arg, "cddr") or is_call(arg, "nthcdr"):
                    raise Refuse("two-list" if is_call(arg, "cdr") else "step")
                raise Refuse("fold", f"parameter {f} changes in the recursion")
            if f == xs and not (is_call(arg, "cdr") and flat_low(arg.items[1]) == xs):
                raise Refuse("step", "other than (cdr XS)")
    match_inner(inner, name, formals, xs, spec)
    return finish(spec, name, formals, wrapper, fl)



def rev_call_of(a, xs):
    """The reversal function when A is `(REV XS nil)', else None."""
    if isinstance(a, Lst) and is_call(a) and len(a.items) == 3 and flat_low(a.items[1]) == xs \
            and flat_low(a.items[2]) == "nil" and a.items[0].low in ("fn-ag-rev-onto", "revappend", "reverse"):
        return a.items[0].low
    return None


def foldr_spec(name, formals, logic, exe, lf, wrapper):
    """:foldr -- the exec runs the loop over the REVERSED list: logic is
    (if (consp XS) COMBINE[(car XS), (NAME .. (cdr XS) ..)] INIT)."""
    fl = [f.low for f in formals.items]
    loop = name + "-loop"
    lfl0 = [f.low for f in formals_of(lf.node).items]
    if not is_call(exe, loop):
        raise Refuse("no-shape", "exec is not the loop")
    if len(lfl0) == 2 and len(exe.items) == 3:       # loop (REV ACC): the other formals stay out of it
        args = list(exe.items[1:])
        nrev = None
        for cand in fl:
            if rev_call_of(args[0], cand):
                nrev = cand
        args = [S(f) if f != nrev else args[0] for f in fl] + [args[1]]
        if nrev is None:
            raise Refuse("no-shape", "exec does not reverse a formal")
        extra_formals_ok = True
    elif len(exe.items) - 1 == len(fl) + 1:
        args = exe.items[1:]
    else:
        raise Refuse("multi-acc", "exec threads more than one accumulator")
    xs = rev = None
    for f, a in zip(fl, args):
        r = None
        for cand in fl:
            r = rev_call_of(a, cand)
            if r:
                xs = cand
                break
        if r:
            rev = r
            break
    if xs is None:
        raise Refuse("no-shape", "exec does not reverse a formal")
    for f, a in zip(fl, args):
        if f != xs and flat_low(a) != f:
            raise Refuse("no-shape", "exec changes a formal other than the reversed list")
    init = args[-1]
    logic = cond_to_if(inline_rec_lets(logic, name))
    if not (is_call(logic, "if") and len(logic.items) == 4):
        raise Refuse("no-shape", "logic is not an if")
    sp = split_test(logic.items[1], xs)
    if sp is None or sp[1] is not None:
        raise Refuse("no-shape", "foldr test is not a plain (consp XS)")
    comb, base = (logic.items[2], logic.items[3]) if sp[0] else (logic.items[3], logic.items[2])
    if flat_low(base) != flat_low(init):
        raise Refuse("exec-differs", "init differs from the logic's base")
    acc = "acc"
    used = atoms_of(logic, set()) | set(fl)
    if acc in used:
        raise Refuse("no-shape", "the name acc is in use")
    calls = list(walk_calls(comb, name))
    if not calls:
        raise Refuse("no-shape", "no recursive call")
    for c in calls:
        if not rec_call(c, name, formals, xs):
            raise Refuse("step", "recursion is not (cdr XS)")
    comb = subst(comb, lambda n: is_call(n, name), S(acc))
    spec = Spec("foldr", name, formals, xs)
    spec.elt = pick_elt(xs, formals, used)
    carx = lambda n: is_call(n, "car") and len(n.items) == 2 and flat_low(n.items[1]) == xs
    spec.combine = subst(comb, carx, S(spec.elt))
    spec.init = init
    spec.rev = None if rev == "revappend" else rev
    if mentions(spec.combine, xs):
        raise Refuse("exec-differs", f"combine mentions {xs} other than (car {xs})")
    # the hand loop must compute the same combine over its own list formal
    lfl = [f.low for f in formals_of(lf.node).items]
    lxs = lfl[fl.index(xs)] if len(lfl) == len(fl) + 1 else lfl[0]
    lbody = body_of(lf.node)
    lacc = lfl[-1]
    if is_call(lbody, "if") and len(lbody.items) == 4:
        sp2 = split_test(lbody.items[1], lxs)
        step = lbody.items[2] if sp2 and sp2[0] else lbody.items[3]
        if is_call(step, loop):
            new = step.items[-1]
            carl = lambda n: is_call(n, "car") and len(n.items) == 2 and flat_low(n.items[1]) == lxs
            new = subst(new, carl, S(spec.elt))
            if lacc != acc:
                new = subst(new, lambda n: isinstance(n, Atom) and n.low == lacc, S(acc))
            if flat_low(new) != flat_low(spec.combine):
                raise Refuse("exec-differs", flat_low(new)[:60])
    xa = xargs_of(wrapper)
    g = xa.get(":guard")
    if g is not None and not (isinstance(g, Atom) and g.low == "t"):
        spec.guard = g
    lg = xargs_of(lf.node).get(":guard")
    if lg is not None and not (isinstance(lg, Atom) and lg.low == "t"):
        if lacc != acc:
            lg = subst(lg, lambda n: isinstance(n, Atom) and n.low == lacc, S(acc))
        if lxs and mentions(lg, lxs):
            raise Refuse("no-shape", "loop guard mentions the list")
        spec.loop_guard = lg
    return spec



class Opt:
    """One `:key value' option: joined onto a line when its flat text fits, else
    on its own line, wrapped by the printer at its indentation."""

    def __init__(self, key, node, suffix=""):
        self.key, self.node, self.suffix = key, node, suffix

    def flat(self):
        return f"{self.key} {pretty(self.node, 10 ** 6)}{self.suffix}"

    def wrapped(self):
        return f"{self.key} {pretty(self.node, 3 + len(self.key))}{self.suffix}"


def packed(chunks, lines, width=WIDTH):
    """Greedy-pack option CHUNKS (Opt or str) onto LINES (the last line grows while it fits)."""
    lines = list(lines)
    for c in chunks:
        f = c.flat() if isinstance(c, Opt) else c
        if "\n" not in lines[-1] and "\n" not in f and len(lines[-1]) + 1 + len(f) <= width:
            lines[-1] += " " + f
        elif isinstance(c, Opt) and len("  " + f) > width:
            lines.append("  " + c.wrapped())
        else:
            lines.append("  " + f)
    return lines


def rec_args(call, name, fl):
    """{formal: arg} of a call of NAME, or None."""
    if not (is_call(call, name) and len(call.items) == len(fl) + 1):
        return None
    return dict(zip(fl, call.items[1:]))



CDRISH = ("cdr", "cddr", "cdddr", "cddddr", "fn-ag-cdr")


def cdrish_of(term, var):
    """Is TERM a cdr/cddr/... (or nested cdr/fn-ag-cdr) chain over VAR?"""
    while isinstance(term, Lst) and is_call(term) and len(term.items) == 2 and term.items[0].low in CDRISH:
        term = term.items[1]
    return isinstance(term, Atom) and term.low == var and not isinstance(term, Str) \
        and flat_low(term) == var and term is not None and True


def order_svars(svars, nexts_by_var, measure_given):
    """The first state var drives the default measure (acl2-count): put a list var that
    advances by a cdr chain first; refuse a state with none unless the wrapper
    carries a :measure."""
    def lead(v):
        t = nexts_by_var[v]
        return isinstance(t, Lst) and is_call(t) and len(t.items) == 2 and t.items[0].low in CDRISH \
            and cdrish_of(t, v) and flat_low(t) != v
    good = [v for v in svars if lead(v)]
    if not good and not measure_given:
        raise Refuse("step-measure", "no state var advances by a cdr chain and the wrapper has no :measure")
    return good + [v for v in svars if v not in good] if good else list(svars)


def step_spec(name, formals, logic, exe, lf, wrapper):
    """:step -- one state (the formals the recursion changes), a done test, an
    emit (or skip) test, and arbitrary advances.  Nothing is bound around the
    recursion result; the loop is the logic's terms threaded."""
    fl = [f.low for f in formals.items]
    loop = name + "-loop"
    if not (is_call(exe, loop) and len(exe.items) == len(fl) + 2
            and [flat_low(a) for a in exe.items[1:-1]] == fl and flat_low(exe.items[-1]) == "nil"):
        raise Refuse("no-shape", "exec is not (LOOP formals nil)")
    xa = xargs_of(wrapper)
    if ":hints" in xa:
        raise Refuse("step-hints", "the wrapper's termination carries :hints")
    logic = cond_to_if(logic)
    if "mv-let" in flat_low(logic) or "(mv " in flat_low(logic):
        raise Refuse("mv")
    if not (is_call(logic, "if") and len(logic.items) == 4):
        raise Refuse("no-shape", "logic is not an if")
    c, a, b = logic.items[1:]
    ra, rb = any_rec(a, name), any_rec(b, name)
    if ra == rb:
        raise Refuse("no-shape", "step: both or neither branch recurse")
    if rb:
        done, tail, rest = c, a, b
    else:
        neg = L(S("atom"), c.items[1]) if (is_call(c, "consp") and len(c.items) == 2) else negate(c)
        done, tail, rest = neg, b, a
    lets = []
    while is_call(rest, "let") or is_call(rest, "let*"):
        if len(rest.items) != 3 or not isinstance(rest.items[1], Lst):
            raise Refuse("no-shape", "let form")
        lets.extend(rest.items[1].items)
        rest = rest.items[2]
    if any(any_rec(bd, name) for bd in lets):
        raise Refuse("pair-result", "recursion result is bound")
    emit = skip = None
    if is_call(rest, "cons") and len(rest.items) == 3:
        body, rec_e, rec_s = rest.items[1], rest.items[2], None
    elif is_call(rest, "if") and len(rest.items) == 4:
        t, x, y = rest.items[1:]
        if is_call(x, "cons") and len(x.items) == 3 and any_rec(x.items[2], name) and any_rec(y, name) \
                and not any_rec(x.items[1], name):
            emit, body, rec_e, rec_s = t, x.items[1], x.items[2], y
        elif is_call(y, "cons") and len(y.items) == 3 and any_rec(y.items[2], name) and any_rec(x, name) \
                and not any_rec(y.items[1], name):
            skip, body, rec_e, rec_s = t, y.items[1], y.items[2], x
        else:
            raise Refuse("no-shape", "step: not (if E (cons F REC) REC) in either order")
    else:
        raise Refuse("no-shape", "step: not a cons of the recursion")
    ea = rec_args(rec_e, name, fl)
    sa = rec_args(rec_s, name, fl) if rec_s is not None else None
    if ea is None or (rec_s is not None and sa is None):
        raise Refuse("no-shape", "step: recursion is not a direct call")
    if any(any_rec(i, name) for i in list(ea.values()) + (list(sa.values()) if sa else [])) or any_rec(body, name):
        raise Refuse("no-shape", "nested recursion")
    svars = [f for f in fl if flat_low(ea[f]) != f or (sa is not None and flat_low(sa[f]) != f)]
    if not svars:
        raise Refuse("no-shape", "no formal advances")
    svars = order_svars(svars, ea, ":measure" in xa)
    spec = Spec("step", name, formals, svars[0])
    spec.svars = svars
    nxt = [ea[f] for f in svars]
    snx = [sa[f] for f in svars] if sa is not None else None
    spec.next = nxt[0] if len(svars) == 1 else nxt
    spec.skip_next = (snx[0] if len(svars) == 1 else snx) if snx is not None else None
    spec.done, spec.body = done, body
    spec.emit, spec.skip = emit, skip
    spec.tail = None if (isinstance(tail, Atom) and tail.low == "nil") else tail
    spec.lets = Lst(lets) if lets else None
    s1 = svars[0]
    carx = lambda n: is_call(n, "car") and len(n.items) == 2 and flat_low(n.items[1]) == s1
    parts_all = [done, body, emit, skip, tail] + nxt + (snx or []) + lets
    uses_car = any(p is not None and contains(p, carx) for p in parts_all)
    if uses_car:
        used = set()
        for p in parts_all:
            if p is not None:
                atoms_of(p, used)
        spec.elt = pick_elt(s1, formals, used)
        sub = lambda n: n if n is None else subst(n, carx, S(spec.elt))
        spec.done, spec.body, spec.emit, spec.skip, spec.tail = (sub(spec.done), sub(spec.body), sub(spec.emit),
                                                                  sub(spec.skip), sub(spec.tail))
        spec.next = [sub(i) for i in spec.next] if isinstance(spec.next, list) else sub(spec.next)
        if isinstance(spec.skip_next, list):
            spec.skip_next = [sub(i) for i in spec.skip_next]
        elif spec.skip_next is not None:
            spec.skip_next = sub(spec.skip_next)
        if spec.lets is not None:
            spec.lets = sub(spec.lets)
    else:
        spec.elt = None
    # the hand loop computes the same terms (a loop with fix / ag-car is what makes its guards provable)
    loop_flat = flat_low(lf.node)
    for part in [body] + nxt + (snx or []) + ([] if tail is None else [tail]):
        if flat_low(part) not in loop_flat:
            raise Refuse("exec-differs", flat_low(part)[:60])
    if flat_low(done) not in loop_flat and flat_low(negate(done)) not in loop_flat \
            and not (is_call(done, "atom") and flat_low(L(S("consp"), done.items[1])) in loop_flat):
        raise Refuse("exec-differs", "done test " + flat_low(done)[:50])
    g = xa.get(":guard")
    if g is not None and not (isinstance(g, Atom) and g.low == "t"):
        spec.guard = g
    m = xa.get(":measure")
    if m is not None:
        spec.measure = m
    st = xa.get(":stobjs")
    if st is not None:
        raise Refuse("step-stobjs", "def-loop :step does not thread :stobjs")
    return spec


def render_step(spec: Spec, hoisted) -> str:
    def val(node):
        return pretty(node, 0)
    over = "" if spec.svars == [spec.formals.items[0].low] else (
        f" :over {spec.svars[0]}" if len(spec.svars) == 1 else f" :over ({' '.join(spec.svars)})")
    first = f"  :shape :step{over}"
    chunks = [Opt(":done", spec.done, f" :elt {spec.elt}" if spec.elt else "")]
    if spec.skip is not None:
        chunks.append(Opt(":skip", spec.skip))
    elif spec.emit is not None:
        chunks.append(Opt(":emit", spec.emit))
    if spec.lets is not None:
        chunks.append(Opt(":let", spec.lets))
    chunks.append(Opt(":body", spec.body))

    def terms(v):
        return v if not isinstance(v, list) else Lst(list(v))
    chunks.append(Opt(":next", terms(spec.next)))
    if spec.skip_next is not None:
        chunks.append(Opt(":skip-next", terms(spec.skip_next)))
    if spec.tail is not None:
        chunks.append(Opt(":tail", spec.tail))
    if spec.measure is not None:
        chunks.append(Opt(":measure", spec.measure))
    if spec.guard is not None:
        chunks.append(Opt(":guard", spec.guard))
    if spec.guard_hints is not None:
        chunks.append(Opt(":guard-hints", spec.guard_hints))
    lines = packed(chunks, [f"(def-loop {spec.name} {flat(spec.formals)}", first])
    lines[-1] += ")"
    return "".join(c.rstrip() + "\n" for c in hoisted) + "\n".join(lines)



def fold_spec(name, formals, logic, exe, lf, wrapper):
    """:fold -- a state (a stobj or any value) threaded through each element;
    the rows are consed, and FAIL at any step is the result.  The logic is
    exactly def-loop's template:
      (if DONE (mv nil ST)
        [LETS] (mv-let (ROW ST) ROWTERM
          (if (eq ROW FAIL) (mv FAIL ST)
            (mv-let (REST ST) (NAME ..NEXT.. ST)
              (if (eq REST FAIL) (mv FAIL ST) (mv (cons ROW REST) ST))))))"""
    fl = [f.low for f in formals.items]
    loop = name + "-loop"
    if not is_call(exe, loop):
        raise Refuse("no-shape", "exec is not the loop")
    eargs = [flat_low(a) for a in exe.items[1:]]
    nils = [i for i, a in enumerate(eargs) if a == "nil"]
    if len(eargs) != len(fl) + 1 or not any(eargs[:i] + eargs[i + 1:] == fl for i in nils):
        raise Refuse("no-shape", "exec is not (LOOP formals with nil for the accumulator)")
    xa = xargs_of(wrapper)
    if ":hints" in xa:
        raise Refuse("step-hints", "the wrapper's termination carries :hints")
    logic = cond_to_if(logic)
    if not (is_call(logic, "if") and len(logic.items) == 4):
        raise Refuse("no-shape", "logic is not an if")
    c, a, b = logic.items[1:]

    def mv_nil(n):
        return is_call(n, "mv") and len(n.items) == 3 and flat_low(n.items[1]) == "nil" \
            and isinstance(n.items[2], Atom)
    if mv_nil(a) and not mv_nil(b):
        done, rest, st = c, b, a.items[2].low
    elif mv_nil(b) and not mv_nil(a):
        done, rest, st = (L(S("atom"), c.items[1]) if is_call(c, "consp") and len(c.items) == 2 else negate(c)), a, b.items[2].low
    else:
        raise Refuse("no-shape", "fold: no (mv nil ST) base")
    if st not in fl:
        raise Refuse("no-shape", "fold: the state is not a formal")
    lets = []
    while is_call(rest, "let") or is_call(rest, "let*"):
        if len(rest.items) != 3 or not isinstance(rest.items[1], Lst):
            raise Refuse("no-shape", "let form")
        lets.extend(rest.items[1].items)
        rest = rest.items[2]

    def mvlet(n):
        if is_call(n, "mv-let") and len(n.items) == 4 and isinstance(n.items[1], Lst) \
                and len(n.items[1].items) == 2 and flat_low(n.items[1].items[1]) == st:
            return n.items[1].items[0].low, n.items[2], n.items[3]
        raise Refuse("no-shape", "fold: not (mv-let (V ST) ..)")
    row, rowterm, body = mvlet(rest)

    def failtest(n, v):
        if is_call(n, "if") and len(n.items) == 4:
            t = n.items[1]
            if (is_call(t, "eq") or is_call(t, "equal")) and len(t.items) == 3 and flat_low(t.items[1]) == v:
                f = t.items[2]
                m = n.items[2]
                if is_call(m, "mv") and len(m.items) == 3 and flat_low(m.items[1]) == flat_low(f) \
                        and flat_low(m.items[2]) == st:
                    return f, n.items[3]
        raise Refuse("no-shape", "fold: not (if (eq V FAIL) (mv FAIL ST) ..)")
    fail, body2 = failtest(body, row)
    rst, rec, body3 = mvlet(body2)
    f2, last = failtest(body3, rst)
    if flat_low(f2) != flat_low(fail) or flat_low(last) != flat_low(L(S("mv"), L(S("cons"), S(row), S(rst)), S(st))):
        raise Refuse("no-shape", "fold: the result is not (mv (cons ROW REST) ST)")
    ra = rec_args(rec, name, fl)
    if ra is None or flat_low(ra[st]) != st or any_rec(rowterm, name):
        raise Refuse("no-shape", "fold: the recursion is not a direct call")
    svars = [f for f in fl if f != st and flat_low(ra[f]) != f]
    if not svars:
        raise Refuse("no-shape", "no formal advances")
    svars = order_svars(svars, ra, ":measure" in xa)
    spec = Spec("fold", name, formals, svars[0])
    spec.svars = svars
    nxt = [ra[f] for f in svars]
    s1 = svars[0]
    carx = lambda n: is_call(n, "car") and len(n.items) == 2 and flat_low(n.items[1]) == s1
    parts_all = [done, rowterm] + nxt + lets
    used = set()
    for q in parts_all:
        atoms_of(q, used)
    uses_car = any(contains(q, carx) for q in parts_all)
    spec.elt = pick_elt(s1, formals, used) if uses_car else None
    sub = (lambda n: subst(n, carx, S(spec.elt))) if uses_car else (lambda n: n)
    spec.done, spec.row_term = sub(done), sub(rowterm)
    nxt = [sub(i) for i in nxt]
    spec.next = nxt[0] if len(svars) == 1 else nxt
    spec.lets = sub(Lst(lets)) if lets else None
    spec.st = st
    spec.fail = None if flat_low(fail) == ":bad" else fail
    loop_flat = flat_low(lf.node)
    for part in [rowterm] + [ra[f] for f in svars]:
        if flat_low(part) not in loop_flat:
            raise Refuse("exec-differs", flat_low(part)[:60])
    if flat_low(done) not in loop_flat and flat_low(negate(done)) not in loop_flat \
            and not (is_call(done, "atom") and flat_low(L(S("consp"), done.items[1])) in loop_flat):
        raise Refuse("exec-differs", "done test " + flat_low(done)[:50])
    g = xa.get(":guard")
    if g is not None and not (isinstance(g, Atom) and g.low == "t"):
        spec.guard = g
    m = xa.get(":measure")
    if m is not None:
        spec.measure = m
    return spec


def render_fold(spec: Spec, hoisted) -> str:
    val = lambda n: pretty(n, 0)
    over = spec.svars[0] if len(spec.svars) == 1 else "(" + " ".join(spec.svars) + ")"
    first = f"  :shape :fold :over {over} :st {spec.st}"
    chunks = [Opt(":done", spec.done, f" :elt {spec.elt}" if spec.elt else "")]
    if spec.lets is not None:
        chunks.append(Opt(":let", spec.lets))
    chunks.append(Opt(":row", spec.row_term))
    chunks.append(Opt(":next", Lst(list(spec.next)) if isinstance(spec.next, list) else spec.next))
    if spec.fail is not None:
        chunks.append(Opt(":fail", spec.fail))
    if spec.measure is not None:
        chunks.append(Opt(":measure", spec.measure))
    if spec.guard is not None:
        chunks.append(Opt(":guard", spec.guard))
    if spec.guard_hints is not None:
        chunks.append(Opt(":guard-hints", spec.guard_hints))
    lines = packed(chunks, [f"(def-loop {spec.name} {flat(spec.formals)}", first])
    lines[-1] += ")"
    return "".join(c.rstrip() + "\n" for c in hoisted) + "\n".join(lines)


def finish(spec, name, formals, wrapper, fl):
    xs = spec.xs
    used = set()
    for attr in ("body", "keep", "stop", "stopval", "while_", "tail", "lets"):
        v = getattr(spec, attr)
        if v is not None:
            atoms_of(v, used)
    spec.elt = pick_elt(xs, formals, used)
    car_of_xs = lambda n: is_call(n, "car") and len(n.items) == 2 and flat_low(n.items[1]) == xs
    sub = lambda n: n if n is None else subst(n, car_of_xs, S(spec.elt))
    for attr in ("body", "keep", "stop", "stopval", "while_", "tail"):
        setattr(spec, attr, sub(getattr(spec, attr)))
    if spec.lets is not None:
        spec.lets = sub(spec.lets)
    # body / keep / lets may mention XS only through ELT
    for attr in ("body", "keep", "lets"):
        v = getattr(spec, attr)
        if v is not None and mentions(v, xs):
            raise Refuse("no-shape", f"{attr} mentions the list other than (car {xs})")
    if spec.shape == "take" and spec.count and mentions(spec.body, spec.count):
        raise Refuse("no-shape", "take body uses the count")
    xa = xargs_of(wrapper)
    g = xa.get(":guard")
    if g is not None and not (isinstance(g, Atom) and g.low == "t"):
        spec.guard = g
    st = xa.get(":stobjs")
    if st is not None:
        spec.stobjs = [i.text for i in st.items] if isinstance(st, Lst) else [st.text]
    return spec


def render_foldr(spec: Spec, hoisted) -> str:
    parts = [f"(def-loop {spec.name} {flat(spec.formals)}",
             f"  :shape :foldr :over {spec.xs} :elt {spec.elt}"]

    def opt(key, node):
        parts.append(f"  {key} {pretty(node, 3 + len(key))}")

    opt(":combine", spec.combine)
    init_txt = pretty(spec.init, 9 + len(parts[-1]))
    if "\n" not in parts[-1] and "\n" not in init_txt and len(parts[-1]) + 7 + len(init_txt) <= WIDTH:
        parts[-1] += f" :init {init_txt}"
    else:
        opt(":init", spec.init)
    if spec.rev:
        parts.append(f"  :rev {spec.rev}")
    if spec.guard is not None:
        opt(":guard", spec.guard)
    if spec.loop_guard is not None:
        if spec.guard is not None and "\n" not in parts[-1]:
            parts[-1] += f" :loop-guard {pretty(spec.loop_guard, 3 + len(parts[-1]))}"
        else:
            opt(":loop-guard", spec.loop_guard)
    if spec.guard_hints is not None:
        opt(":guard-hints", spec.guard_hints)
    parts[-1] += ")"
    return "".join(c.rstrip() + "\n" for c in hoisted) + "\n".join(parts)


def render(spec: Spec, hoisted) -> str:
    if spec.shape == "foldr":
        return render_foldr(spec, hoisted)
    if spec.shape == "step":
        return render_step(spec, hoisted)
    if spec.shape == "fold":
        return render_fold(spec, hoisted)
    parts = [f"(def-loop {spec.name} {flat(spec.formals)}"]
    first = f"  :shape :{spec.shape} "
    if spec.shape == "take":
        first += f":count {spec.count} "
    first += f":over {spec.xs} :elt {spec.elt}"
    if spec.stobjs:
        first += " :stobjs " + (spec.stobjs[0] if len(spec.stobjs) == 1
                                else "(" + " ".join(spec.stobjs) + ")")
    parts.append(first)

    def opt(key, node):
        txt = pretty(node, 3 + len(key))
        parts.append(f"  {key} {txt}")

    if spec.guard is not None:
        opt(":guard", spec.guard)
    if spec.lets is not None:
        opt(":let", spec.lets)
    if spec.stop is not None:
        opt(":stop", spec.stop)
        opt(":stop-value", spec.stopval)
    if spec.keep is not None:
        opt(":keep", spec.keep)
        if spec.skip_first:
            if "\n" in parts[-1]:  # a wrapped :keep leaves the option on its own line
                parts.append("  :keep-order :skip-first")
            else:
                parts[-1] += " :keep-order :skip-first"
    if spec.while_ is not None and not (spec.shape == "take" and flat_low(spec.while_) == f"(consp {spec.xs})" and False):
        opt(":while", spec.while_)
    if spec.tail is not None:
        opt(":tail", spec.tail)
        if spec.stop is not None and "\n" not in parts[-1] and "\n" not in parts[-2] \
                and len(parts[-2]) + len(parts[-1].strip()) + 1 <= WIDTH:
            tail_line = parts.pop().strip()
            parts[-1] += " " + tail_line
    if isinstance(spec.body, Atom) and spec.body.low == "nil":
        parts.append("  :body 'nil")  # def-loop reads a bare NIL :body as absent
    else:
        opt(":body", spec.body)
    parts[-1] += ")"
    head_comments = "".join(c.rstrip() + "\n" for c in hoisted)
    return head_comments + "\n".join(parts)


# --------------------------------------------------------------------------
# a book's twins


def loop_defuns(forms):
    return [f for f in forms if f.kind == "defun" and f.name and f.name.endswith("-loop")]


def container_members(f, twins):
    """The twins a bridge container carries, or None when F is not purely a
    container: `(encapsulate () ...)' / `(progn ...)' whose every child is a
    (local) defthm named NAME-loop-is-*/NAME-loop-of-* or a verify-guards of
    NAME / NAME-loop for a twin NAME."""
    n = f.node
    if f.kind == "encapsulate":
        kids = n.items[3:] if len(n.items) > 2 else []
    elif f.kind == "progn":
        kids = n.items[1:]
    else:
        return None
    mem = set()
    for k in kids:
        if is_call(k, "local") and len(k.items) == 2:
            k = k.items[1]
        if not (isinstance(k, Lst) and is_call(k) and len(k.items) > 1 and isinstance(k.items[1], Atom)):
            return None
        nm = k.items[1].low
        if is_call(k, "verify-guards"):
            base = nm[:-5] if nm.endswith("-loop") else nm
        elif is_call(k, "defthm") or is_call(k, "defthmd"):
            m = re.match(r"(.*)-loop-(?:is|of)-", nm)
            base = m.group(1) if m else None
        else:
            return None
        if base not in twins:
            return None
        mem.add(base)
    return mem or None


def analyse(text: str, book: str, other_text: dict | None = None):
    """(conversions, residual): conversions are dicts with the spec, the
    forms to delete and the replacement; residual is [(name, reason, detail)]."""
    forms, comments = book_forms(text)
    by_name = {}
    for f in forms:
        if f.kind == "defun":
            by_name[f.name] = f
    # position of every verify-guards NAME
    vg_pos = {}
    for f in forms:
        if f.kind == "verify-guards":
            vg_pos.setdefault(f.name, f.start)
    eager = 1
    for f in forms:
        if f.kind == "set-verify-guards-eagerness" and is_call(f.node) and len(f.node.items) == 2:
            eager = int(f.node.items[1].text)

    def unverified(f):
        xa = xargs_of(f.node)
        vg = xa.get(":verify-guards")
        if vg is not None:
            return vg.low == "nil"
        if eager == 0:
            return True
        if eager >= 2:
            return False
        return ":guard" not in xa and ":stobjs" not in xa
    noguards = {n for n, f in by_name.items() if unverified(f)}
    conv, resid = [], []
    twin_names = {lf.name[:-5] for lf in loop_defuns(forms)}
    containers = {}
    for lf in loop_defuns(forms):
        name = lf.name[:-5]
        w = by_name.get(name)
        if w is None:
            resid.append((name, "no-wrapper", "")); continue
        try:
            wnode = w.node
            body = body_of(wnode)
            mbe = None
            for sub in [body] + [i for i in wnode.items[3:] if is_call(i, "mbe")]:
                if is_call(sub, "mbe"):
                    mbe = sub
            if mbe is None:
                raise Refuse("no-wrapper", "no mbe in the wrapper")
            kv = {mbe.items[i].low: mbe.items[i + 1] for i in range(1, len(mbe.items) - 1, 2)
                  if isinstance(mbe.items[i], Atom)}
            logic, exe = kv.get(":logic"), kv.get(":exec")
            if logic is None or exe is None:
                raise Refuse("no-wrapper", "mbe without :logic/:exec")
            exec_call = exe if is_call(exe, name + "-loop") else None
            formals = formals_of(wnode)
            rev_exec = exec_call is not None and any(
                rev_call_of(a, f.low) for a in exec_call.items[1:] for f in formals.items)
            if rev_exec:
                spec = foldr_spec(name, formals, logic, exe, lf, wnode)
            else:
                try:
                    if exec_call is None:
                        raise Refuse("no-shape")
                    args = exec_call.items[1:]
                    fl = [f.low for f in formals.items]
                    if [flat_low(a) for a in args[:len(fl)]] != fl or len(args) != len(fl) + 1 \
                            or flat_low(args[-1]) not in ("nil", "0"):
                        raise Refuse("no-shape")
                    spec = shape_of(name, formals, logic, wnode)
                except Refuse as r:
                    spec = None
                    if "mv-let" in flat_low(logic):
                        try:
                            spec = fold_spec(name, formals, logic, exe, lf, wnode)
                        except Refuse as r2:
                            if r2.reason in ("step-hints", "exec-differs"):
                                raise r2
                    if spec is None and r.reason in ("no-shape", "step", "two-list", "fold"):
                        try:
                            spec = step_spec(name, formals, logic, exe, lf, wnode)
                        except Refuse as r2:
                            if r2.reason in ("step-hints", "step-stobjs", "exec-differs", "pair-result"):
                                raise r2
                    if spec is None:
                        if r.reason in ("no-shape",):
                            raise classify_nonshape(name, formals, logic, lf.node, exec_call)
                        raise
                # the exec loop must compute the same terms as the logic: a loop that
                # differs (fix, fn-ag-car) is there to make the guards provable, and
                # the generated loop would use the logic's terms
                if spec.shape != "step":
                    xs_ = spec.xs
                    carx = lambda n: is_call(n, "car") and len(n.items) == 2 and flat_low(n.items[1]) == xs_
                    loop_flat = flat_low(subst(lf.node, carx, S(spec.elt)))
                    for part in (spec.body, spec.keep, spec.stop, spec.stopval, spec.tail,
                                 None if spec.shape == "take" else spec.while_):
                        if part is not None and flat_low(part) not in loop_flat:
                            raise Refuse("exec-differs", flat_low(part)[:60])
                    if spec.lets is not None:
                        for b in spec.lets.items:
                            if flat_low(b.items[1]) not in loop_flat:
                                raise Refuse("exec-differs", flat_low(b.items[1])[:60])
            # late guard: callee verified after the wrapper
            names = set()
            for part in (spec.body, spec.keep, spec.stop, spec.stopval, spec.lets, spec.tail, spec.while_,
                         spec.combine, spec.init, spec.done, spec.emit, spec.skip):
                if part is not None:
                    fn_names(part, names)
            for part in ([spec.next, spec.skip_next] if spec.shape == "step" else []):
                for t in (part if isinstance(part, list) else [part]):
                    if t is not None:
                        fn_names(t, names)
            for callee in names:
                if callee in noguards and vg_pos.get(callee, -1) > w.start:
                    raise Refuse("late-guard", callee)
            # the deletable forms
            kill = [lf]
            for f in forms:
                if f.name and (f.name.startswith(name + "-loop-is-") or f.name.startswith(name + "-loop-of-")) \
                        and f.kind in ("defthm", "local-defthm", "defthmd"):
                    kill.append(f)
                if f.kind == "verify-guards" and f.name in (name, name + "-loop"):
                    kill.append(f)
            killset = {id(k) for k in kill}
            if spec.shape in ("foldr", "step", "fold"):
                for k in kill:
                    if k.kind == "verify-guards" and k.name in (name, name + "-loop") and is_call(k.node) \
                            and spec.guard_hints is None:
                        ks = k.node.items[2:]
                        for i in range(0, len(ks) - 1, 2):
                            if isinstance(ks[i], Atom) and ks[i].low == ":hints":
                                if not contains(ks[i + 1], lambda x: isinstance(x, Atom) and x.low.startswith(name + "-loop")):
                                    spec.guard_hints = ks[i + 1]
            # references to the loop elsewhere
            for f in forms:
                if id(f) in killset or f is w:
                    continue
                if mentions(f.node, name + "-loop") or contains(
                        f.node, lambda x: isinstance(x, Atom) and x.low.startswith(
                            (name + "-loop-is", name + "-loop-of"))):
                    if f.kind == "fn-payload-kind":
                        continue  # a kind registration of the loop's name: def-loop emits the same name
                    if container_members(f, twin_names) is None:
                        raise Refuse("loop-referenced", f.name or "")
                    containers.setdefault(id(f), f)
            for other, otext in (other_text or {}).items():
                if re.search(re.escape(name) + r"-loop", otext, re.I):
                    raise Refuse("loop-referenced", other)
            inner_comments = [c for c in wnode.comments]
            doc = [i for i in wnode.items[3:] if isinstance(i, Str)]
            hoisted = []
            for d in doc:
                hoisted += ["; " + ln.strip() for ln in d.text.strip('"').splitlines() if ln.strip()]
            hoisted += [c for c in inner_comments]
            conv.append(dict(name=name, spec=spec, wrapper=w, kill=kill,
                             text=render(spec, hoisted)))
        except Refuse as r:
            resid.append((name, r.reason, r.detail))
    # a shared (encapsulate () (local bridge)... (verify-guards ..)...) goes only
    # when every twin it carries converts; one that stays keeps the others out
    changed = True
    while changed:
        changed = False
        have = {c["name"] for c in conv}
        for f in containers.values():
            mem = container_members(f, twin_names)
            bad = [m for m in mem if m in twin_names and m not in have] if mem else []
            if bad:
                for c in [c for c in conv if c["name"] in mem]:
                    conv.remove(c)
                    resid.append((c["name"], "loop-referenced", f"shared bridge encapsulate with {bad[0]}"))
                    changed = True
        if changed:
            continue
    for f in containers.values():
        mem = container_members(f, twin_names)
        owners = [c for c in conv if c["name"] in mem]
        if owners and not any(f in c["kill"] for c in conv):
            owners[0]["kill"].append(f)
    return conv, resid


def apply_text(text: str, conv) -> str:
    edits = []
    for c in conv:
        w = c["wrapper"]
        edits.append((w.start, w.end, c["text"]))
        for k in c["kill"]:
            # a deleted form takes its trailing blank line with it
            m = re.match(r"[ \t]*\n(\s*\n)?", text[k.end:])
            edits.append((k.start, k.end + (m.end() if m else 0), ""))
    if conv and '(include-book "def-loop")' not in text:
        m = re.search(r'^\(include-book "[^"]+"[^\n]*\)\n', text, re.M)
        if not m:
            raise Refuse("no-shape", "no include-book to anchor def-loop")
        edits.append((m.end(), m.end(), '(include-book "def-loop")\n'))
    return write(text, edits)


# --------------------------------------------------------------------------
# statement diff (exported theorems)


def exported(text):
    forms, _ = book_forms(text)
    out = {}
    for f in forms:
        if f.kind in ("defthm", "defthmd") or (f.kind or "").startswith("defthm-"):
            items = f.node.items
            stmt = []
            i = 2
            while i < len(items):
                if isinstance(items[i], Atom) and items[i].text.startswith(":") and \
                        items[i].low in (":hints", ":rule-classes", ":otf-flg", ":instructions"):
                    break
                stmt.append(flat_low(items[i]))
                i += 1
            out[f.name] = (f.kind, tuple(stmt))
        elif f.kind == "def-loop":
            out[f.name] = ("defun", "def-loop")
        elif f.kind in ("defun", "defund", "defmacro", "defconst"):
            out[f.name] = (f.kind, flat_low(f.node))
    return out


def stmt_diff(old_text, new_text):
    o, n = exported(old_text), exported(new_text)
    removed = [k for k in o if k not in n and not ("-loop-is-" in k or (o[k][0] == "defun" and k.endswith("-loop")))]
    removed += [k for k in o if k in n and o[k][0] == "defun" and n[k] == ("defun", "def-loop") and False]
    added = [k for k in n if k not in o]
    changed = [k for k in o if k in n and o[k] != n[k] and o[k][0].startswith("defthm")]
    return removed, added, changed


def git_show(ref, path):
    try:
        return subprocess.check_output(["git", "show", f"{ref}:{path}"], cwd=ROOT,
                                       stderr=subprocess.DEVNULL).decode()
    except subprocess.CalledProcessError:
        return None


def loop_count(text):
    forms, _ = book_forms(text)
    return len(loop_defuns(forms))


# --------------------------------------------------------------------------
# tree scan and CLI

EXCLUDE = re.compile(
    r"^(catalog-.*|served-catalog-view|msgid-linear.*|msgid-pages.*|msgid-tag-exec|msgid-index.*|"
    r"pagestore.*|store-checkpoint.*|checkpoint.*|owner-checkpoint-.*|payload-arena.*|payload-extent.*|"
    r"history-paged|history-columns.*|history-records|def-representation.*|assumptions.*|"
    r"peer-catchup-spool.*|article-stream-owner|wire-grammar|wire-family-.*|blake3.*|decoded-payload-.*|"
    r"definterface|def-carried.*|store-files|protocol-table|image-world.*|def-buffer|octets-stobj|"
    r"deflate-inflate|web-request|receive-octet-buffer|native-control-buffer|bp-node-rotation-buffer|"
    r"store-log-buffer|def-loop)$")


def tree_text_for_refs(skip):
    """Text of every other book, test and host file that may name a loop."""
    out = {}
    for pat in ("books/*.lisp", "tests/acl2/*.lisp", "host/**/*.lisp"):
        for p in ROOT.glob(pat):
            if p != skip:
                out[str(p.relative_to(ROOT))] = None
    return out


def check_book(book: str, ref="origin/dev", tree_refs=None, write=False, skip=()):
    path = ROOT / "books" / f"{book}.lisp"
    text = path.read_text()
    others = {}
    if tree_refs is not None:
        for rel in tree_refs:
            if rel == f"books/{book}.lisp":
                continue
            others[rel] = tree_refs[rel]
    conv, resid = analyse(text, book, others)
    for c in [c for c in conv if c["name"] in skip]:
        conv.remove(c)
        resid.append((c["name"], "skipped", "by --skip"))
    new = apply_text(text, conv) if conv else text
    old = git_show(ref, f"books/{book}.lisp") or text
    removed, added, changed = stmt_diff(old, new)
    report = dict(book=book, converted=[c["name"] for c in conv], residual=resid,
                  loops_before=loop_count(text), loops_after=loop_count(new),
                  removed=removed, added=added, changed_theorems=changed)
    if write and conv:
        path.write_text(new)
    return report, conv


# -----------------------------------------------------------------------------
# planning/proof-events.json cites theorems by name.  A conversion deletes the
# hand bridges (NAME-loop-is-rev-onto ...) those rows cite, and ledger.py
# --write then fails "no such theorem".  The property now lives in the
# def-loop library bridge for the shape; re-point each dangling citation there.

EVENTS = "planning/proof-events.json"
LOOPISH = re.compile(r"-loop-(?:is|of)-[a-z-]+$|-loop-natp$")


def library_bridge(form: str) -> str | None:
    """The books/def-loop.lisp theorem that carries a def-loop form's bridge."""
    shape = re.search(r":shape\s+:(\w+)", form)
    shape = shape.group(1) if shape else "map"
    base = re.search(r"\s:base\s", form) is not None
    if shape == "map":
        if base:
            return "fn-dl-map-base-loop-is-revappend"
        if re.search(r":keep-order\s+:skip-first", form):
            return "fn-dl-map-skip-loop-is-revappend"
        if re.search(r":acc-fix\b", form):
            return "fn-dl-map-fixed-loop-is-revappend"
        return "fn-dl-map-loop-is-revappend"
    if shape == "take":
        return "fn-dl-take-base-loop-is-revappend" if base else "fn-dl-take-loop-is-revappend"
    return {"sum": "fn-dl-sum-loop-is-plus", "concat": "fn-dl-concat-loop-is-revappend",
            "into": "fn-dl-into-loop-is-append", "step": "fn-dl-step-loop-is-revappend",
            "fold": "fn-dl-fold-loop-is-revappend", "foldr": "fn-dl-foldr-loop-is-foldr"}.get(shape)


def tree_defs():
    """(set of defthm names, {def-loop name: form text}) over books/ and tests/acl2/."""
    thms, forms = set(), {}
    for pat in ("books/*.lisp", "tests/acl2/*.lisp"):
        for p in ROOT.glob(pat):
            t = p.read_text(errors="replace")
            thms.update(re.findall(r"\(defthmd?\s+([^\s()]+)", t, re.I))
            for m in re.finditer(r"\(def-loop\s+([^\s()]+)", t, re.I):
                end = t.find("\n(", m.start())
                forms[m.group(1).lower()] = t[m.start():end if end > 0 else len(t)]
    return {x.lower() for x in thms}, forms


def repoint_events(write: bool):
    """Dangling theorem events in the curated map -> (renames, unresolved)."""
    path = ROOT / EVENTS
    if not path.exists():
        return [], []
    data = json.loads(path.read_text())
    thms, forms = tree_defs()
    renames, unresolved = [], []
    for t in data.get("targets", []):
        out, seen = [], set()
        for ev in t.get("events", []):
            name = ev.get("name", "")
            if (ev.get("kind", "theorem") == "theorem" and name.lower() not in thms
                    and LOOPISH.search(name)):
                fn = LOOPISH.sub("", name).lower()
                lib = library_bridge(forms[fn]) if fn in forms and fn != name.lower() else None
                if lib is None or lib not in thms:
                    unresolved.append((t["id"], name))
                else:
                    renames.append((t["id"], name, lib))
                    ev = dict(ev, name=lib)
            if ev["name"] in seen:
                continue
            seen.add(ev["name"])
            out.append(ev)
        t["events"] = out
    if write and renames:
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    return renames, unresolved


def load_refs():
    refs = {}
    for pat in ("books/*.lisp", "tests/acl2/*.lisp", "host/**/*.lisp"):
        for p in ROOT.glob(pat):
            refs[str(p.relative_to(ROOT))] = p.read_text(errors="replace")
    # only files that name a *-loop-ish symbol matter; keep the dict small
    return {k: v for k, v in refs.items() if "-loop" in v}


def print_report(r):
    print(f"{r['book']}: converted {len(r['converted'])} "
          f"(loop defuns {r['loops_before']} -> {r['loops_after']})")
    for n in r["converted"]:
        print(f"  + {n}")
    for n, why, d in r["residual"]:
        print(f"  - {n}: {why}{(' ' + d) if d else ''}")
    print(f"  exported diff: unexpected removals {r['removed']}, "
          f"added {r['added']}, changed theorems {r['changed_theorems']}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("books", nargs="*")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--residual", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--ref", default="origin/dev")
    ap.add_argument("--exclude-file", help="books/NAME.lisp per line: busy books, tagged excluded")
    ap.add_argument("--ledger", action="store_true",
                    help="only the proof-events.json citations (with --apply: re-point them)")
    ap.add_argument("--skip", action="append", default=[], help="a twin NAME to leave unconverted (repeatable)")
    ap.add_argument("--plan", action="store_true", help="list books with take-now twins")
    a = ap.parse_args(argv)
    refs = load_refs()
    busy = set()
    if a.exclude_file:
        busy = {Path(l.strip()).stem for l in Path(a.exclude_file).read_text().splitlines() if l.strip()}
    if a.residual or a.plan:
        rows = []
        for p in sorted((ROOT / "books").glob("*.lisp")):
            b = p.stem
            tag = "excluded" if (EXCLUDE.match(b) or b in busy) else ""
            if a.plan and tag:
                continue
            try:
                rep, _ = check_book(b, a.ref, refs)
            except (ReadError, Refuse) as e:
                rows.append((b, "(unreadable)", "read-error", str(e)))
                continue
            for n, why, d in rep["residual"]:
                rows.append((b, n, why, (d + " " + tag).strip()))
            for n in rep["converted"]:
                rows.append((b, n, "TAKE-NOW", tag))
        if a.plan:
            from collections import Counter
            c = Counter(b for b, n, why, d in rows if why == "TAKE-NOW")
            for b, k in sorted(c.items(), key=lambda kv: (-kv[1], kv[0])):
                print(k, b)
            return 0
        text = render_residual(rows)
        if a.out:
            Path(a.out).write_text(text)
        else:
            print(text)
        return 0
    if not a.books and not a.ledger:
        ap.error("name books, or --residual")
    rc = 0
    for b in a.books:
        b = b.removeprefix("books/").removesuffix(".lisp")
        rep, _ = check_book(b, a.ref, refs, write=a.apply, skip=set(a.skip))
        print_report(rep)
    renames, unresolved = repoint_events(a.apply)
    if a.apply or a.ledger or unresolved:
        for ident, name, lib in renames:
            print(f"  ledger {ident}: {name} -> {lib}" + ("" if a.apply else " (would re-point)"))
    for ident, name in unresolved:
        print(f"  DANGLING {EVENTS} {ident}: {name}: no theorem and no def-loop library bridge")
    if unresolved or (a.ledger and renames and not a.apply):
        rc = 1
    return rc


def render_residual(rows):
    from collections import Counter, defaultdict
    by = defaultdict(list)
    for b, n, why, d in rows:
        by[why].append((b, n, d))
    lines = ["# Generator drain residual (computed by tools/def_loop_drain.py --residual)", "",
             "Every `*-loop` defun in books/ (excluding other deputies' books) with the reason",
             "`def_loop_drain.py` did not convert it.  TAKE-NOW rows are twins the tool can still",
             "convert.  Regenerate, never hand-edit.", "", "## Counts", "", "| class | count |", "|---|---|"]
    for why, items in sorted(by.items(), key=lambda kv: -len(kv[1])):
        lines.append(f"| {why} | {len(items)} |")
    for why, items in sorted(by.items(), key=lambda kv: -len(kv[1])):
        lines += ["", f"## {why} ({len(items)})", ""]
        for b, n, d in sorted(items):
            lines.append(f"- {b}: {n}{(' (' + d + ')') if d else ''}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
