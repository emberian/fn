#!/usr/bin/env python3
"""Thread declared origin arguments through source definitions and their calls.

One bounded migration using the shared Lisp reader. Definitions and calls keep
all existing source bytes; fixtures exercise both forms and reject bad arities.
"""
import lisp_rewrite as lr

def thread(text, name, arity, before, arguments='lineage domain incarnation'):
    parsed = lr.parse(text)
    edits=[]
    theory=[(m.start,m.end) for head in ('disable','enable','e/d') for m in lr.match('(?*xs)',parsed.forms,head=head)]
    for m in lr.match('(?*xs)', parsed.forms, head=name):
        if any(a<=m.start and m.end<=b for a,b in theory): continue
        xs=m.node.items
        if len(xs)-1 != arity:
            raise ValueError(f'{name}: expected {arity} arguments')
        at=xs[before+1].start
        edits.append((at,at,arguments+' '))
    for m in lr.match('(defun ?name ?params ?*body)',parsed.forms, name=name):
        params=m.node.items[2]
        if len(params.items)!=arity: raise ValueError(f'{name}: definition arity')
        at=params.items[before].start
        edits.append((at,at,arguments+' '))
    return lr.write(text,edits),len(edits)

def control():
    s='; retained\n(defun f (a b) (f a b))\n(g f)'
    out,n=thread(s,'f',2,1)
    assert out=='; retained\n(defun f (a lineage domain incarnation b) (f a lineage domain incarnation b))\n(g f)'
    assert n==2
    try: thread('(f a)','f',2,1)
    except ValueError: pass
    else: raise AssertionError('wrong arity accepted')

if __name__=='__main__':
    control(); print('origin context rewrite fixtures PASS')
