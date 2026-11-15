#!/usr/bin/env python3
"""Align named arm bodies to declared enum order without changing any body."""
from pathlib import Path
import argparse
import lisp_rewrite as lr
def arms_of(node):
    return next(node.items[i+1] for i,x in enumerate(node.items) if getattr(x,'low',None)==':arms')
def align(declaration,implementation,kind):
    decl=lr.match(f'(defmachine {kind} ?*body)',lr.parse(declaration).forms,deep=False)
    impl=lr.match(f'(defmachine-arms {kind} ?*body)',lr.parse(implementation).forms,deep=False)
    if len(decl)!=1 or len(impl)!=1:raise ValueError('expected one declared/implemented machine')
    node=decl[0].node
    states=next(node.items[i+1] for i,x in enumerate(node.items) if getattr(x,'low',None)==':states')
    wanted=[x.low for x in states.items];arms=arms_of(impl[0].node)
    actual=[x.items[0].low for x in arms.items]
    if len(set(actual))!=len(actual) or set(actual)!=set(wanted):raise ValueError('arm coverage differs; never invent/drop a body')
    segments={};end=arms.start+1
    for n in arms.items:
        segments[n.items[0].low]=implementation[end:n.end];end=n.end
    replacement='('+''.join(segments[x] for x in wanted)+implementation[end:arms.end-1]+')'
    return lr.write(implementation,[(arms.start,arms.end,replacement)])
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('declaration',type=Path);p.add_argument('implementation',type=Path);p.add_argument('kind');a=p.parse_args()
    a.implementation.write_text(align(a.declaration.read_text(),a.implementation.read_text(),a.kind))
