#!/usr/bin/env python3
"""One structural class: account the declared Xref work in every ready exit."""
from pathlib import Path
import lisp_rewrite as lr

def transform(text, inverse=False):
    p=lr.parse(text)
    arms=lr.match('(:ready :on-refusal ?*body)',p.forms)
    if len(arms)!=1: raise ValueError('expected one ready arm')
    arm=arms[0]
    old,new=('24576','*fn2-txn-ready-bytes*')
    if inverse: old,new=new,old
    sites=lr.match(old,[arm.node])
    if len(sites)!=13: raise ValueError(f'expected thirteen ready exits, got {len(sites)}')
    return lr.write(text,[(m.start,m.end,new) for m in sites])

if __name__=='__main__':
    path=Path(__file__).resolve().parents[1]/'books/txn.lisp'
    path.write_text(transform(path.read_text()))
