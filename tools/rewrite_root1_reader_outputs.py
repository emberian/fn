#!/usr/bin/env python3
"""Extend the actual root1 callback projections for the shared physical reader.
Uses the shared structural reader; no Lisp evaluation or blanket child returns.
"""
from pathlib import Path
from lisp_rewrite import parse, match, Lst, Atom, Pre, write
CHILDREN=('fn2-run-loads','fn2-run-load-ops','fn2-checkpoint-summary','fn2-checkpoint-summary-sources','fn2-checkpoint-summary-leases')
ADDITIONS={
 'fn2-checkpoint-root1-begin':('fn2-run-loads',),
 'fn2-checkpoint-root1-work':('fn2-run-loads','fn2-checkpoint-summary','fn2-checkpoint-summary-leases'),
 'fn2-checkpoint-root1-closure':('fn2-run-loads','fn2-run-cursors','fn2-checkpoint-summary','fn2-checkpoint-summary-leases'),
 'fn2-checkpoint-root1-read':('fn2-run-loads','fn2-run-load-ops'),
 'fn2-checkpoint-root1-step':('fn2-run-loads','fn2-checkpoint-summary','fn2-checkpoint-summary-leases')}
def quoted_list(node):
    # The shared structural reader preserves quote as a prefix node.
    if isinstance(node,Pre): node=node.node
    if not isinstance(node,Lst): raise ValueError('projection is not a quoted list')
    return node

def transform(text):
    p=parse(text); edits=[]
    found=match('(defconst *fn2-checkpoint-root1-children* ?value)',p.forms,deep=False)
    rows=match('(defconst *fn2-checkpoint-root1-outputs* ?value)',p.forms,deep=False)
    if len(found)!=1 or len(rows)!=1: raise ValueError('actual children/output declaration missing')
    children=quoted_list(found[0].node.items[2]); present={n.low for n in children.items if isinstance(n,Atom)}
    missing=[n for n in CHILDREN if n not in present]
    if missing: edits.append((children.end-1,children.end-1,' '+' '.join(missing)))
    outputs=quoted_list(rows[0].node.items[2]); seen=set()
    for row in outputs.items:
        if not isinstance(row,Lst) or not row.items or not isinstance(row.items[0],Atom):raise ValueError('invalid output row')
        name=row.items[0].low
        if name not in ADDITIONS:continue
        seen.add(name); existing={n.low for n in row.items if isinstance(n,Atom)}
        add=[n for n in ADDITIONS[name] if n not in existing]
        if len(row.items)-1+len(add)+(3 if name.endswith('-read') else 1)>32: raise ValueError('ACL2 MV limit exceeded')
        if add:edits.append((row.end-1,row.end-1,' '+' '.join(add)))
    if seen!=set(ADDITIONS):raise ValueError('mutating callback projection missing')
    return write(text,edits),len(edits)
if __name__=='__main__':
    import argparse
    a=argparse.ArgumentParser();a.add_argument('path',type=Path);a.add_argument('--write',action='store_true');o=a.parse_args()
    out,n=transform(o.path.read_text())
    if o.write:o.path.write_text(out)
    print(f'{o.path}: {n} projection edits')
