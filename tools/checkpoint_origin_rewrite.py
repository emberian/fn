#!/usr/bin/env python3
"""Bounded checkpoint physical-origin migration using shared Lisp rewrites.

Helpers preserve untouched bytes, reject unexpected signatures/argument slots,
and never replace a numeric literal without an exact call/position match.
"""
import lisp_rewrite as lr
from origin_context_rewrite import thread


def low(node):
    return node.text.lower() if isinstance(node, lr.Atom) else None


def source(text, node):
    return text[node.start:node.end]


def add_read_child(text, name, arity, child):
    """Insert readonly CHILD before the existing final argument everywhere."""
    text, count = thread(text, name, arity, arity - 1, child)
    parsed = lr.parse(text)
    edits = []
    for m in lr.match('(defun ?name ?params ?*body)', parsed.forms, name=name):
        decl = m.node.items[3]
        xargs = next(x for x in decl.items if isinstance(x, lr.Lst) and low(x.items[0]) == 'xargs')
        xs = xargs.items
        stobjs = xs[next(i for i,x in enumerate(xs) if low(x)==':stobjs')+1]
        guard = xs[next(i for i,x in enumerate(xs) if low(x)==':guard')+1]
        if not isinstance(stobjs, lr.Lst):
            raise ValueError('migration requires explicit stobj list')
        edits.append((stobjs.items[-1].start, stobjs.items[-1].start, child+' '))
        if isinstance(guard, lr.Lst) and low(guard.items[0]) == 'and':
            edits.append((guard.end-1, guard.end-1, f' ({child}-wfp {child})'))
        else:
            raise ValueError('migration requires explicit conjunctive guard')
    for m in lr.match('(?*xs)', parsed.forms):
        xs=m.node.items
        if len(xs)<3 or not (low(xs[0]) or '').endswith('-preserves') or low(xs[1]) != name:
            continue
        args=xs[2]
        edits.append((args.items[-1].start,args.items[-1].start,child+' '))
        hyps=next((xs[i+1] for i,x in enumerate(xs[:-1]) if low(x)==':hyps'),None)
        if hyps is not None:
            edits.append((hyps.end-1,hyps.end-1,f' ({child}p {child}) ({child}-wfp {child})'))
        else:
            carriers=next((xs[i+1] for i,x in enumerate(xs[:-1]) if low(x)==':carriers'),None)
            tables=[low(c.items[0]) for c in carriers.items] if carriers else [(low(xs[0]) or '').removesuffix('-preserves')]
            hs=' '.join(f'({t}p {t}) ({t}-wfp {t})' for t in tables+[child])
            edits.append((m.end-1,m.end-1,f'\n :hyps ({hs})'))
    for m in lr.match('(?*xs)',parsed.forms,head='defcost'):
        xs=m.node.items
        ci=next((i for i,x in enumerate(xs[:-1]) if low(x)==':child' and low(xs[i+1])==name),None)
        if ci is None:continue
        tables=next(xs[i+1] for i,x in enumerate(xs[:-1]) if low(x)==':tables')
        edits.append((tables.items[-1].start,tables.items[-1].start,child.replace('fn2-','fn2-core-',1)+' '))
    return lr.write(text,edits),count+len(edits)


def call_args(text, head, replacements, scope=None, expected_count=None):
    """REPLACEMENTS maps zero-based argument index to (old text,new text)."""
    parsed=lr.parse(text);edits=[];count=0
    scopes=lr.match('(defun ?name ?*body)',parsed.forms,name=scope) if scope else None
    for m in lr.match('(?*xs)',parsed.forms,head=head):
        if scopes is not None and not any(s.start<=m.start and m.end<=s.end for s in scopes):continue
        for i,(old,new) in replacements.items():
            arg=m.node.items[i+1]
            actual=source(text,arg)
            if actual != old:raise ValueError(f'{head} arg{i}: expected {old!r}, got {actual!r}')
            edits.append((arg.start,arg.end,new))
        count+=1
    if expected_count is not None and count!=expected_count:raise ValueError(f'{head}: expected {expected_count} calls, found {count}')
    return lr.write(text,edits),count
