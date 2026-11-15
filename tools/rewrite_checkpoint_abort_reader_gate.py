#!/usr/bin/env python3
"""Thread readonly source-reader detachment through the actual abort family."""
from pathlib import Path
import argparse
from lisp_rewrite import parse,write,Lst,Atom,Pre
NAMES={'fn2-checkpoint-master-preconstructionp','fn2-checkpoint-master-abort-snapshot-ready-children','fn2-checkpoint-master-abort-step-children','fn2-checkpoint-master-abort-complete-children','fn2-checkpoint-master-abort-empty-ready-children'}
CHILDREN=('fn2-run-loads','fn2-run-cursors','fn2-checkpoint-summary-leases')
GATE='(fn2-checkpoint-source-reader-detachedp '+' '.join(CHILDREN)+')'
def head(n):return n.items[0].low if isinstance(n,Lst) and n.items and isinstance(n.items[0],Atom) else ''
def walk(n):
 yield n
 if isinstance(n,Lst):
  for x in n.items:yield from walk(x)
 elif isinstance(n,Pre):yield from walk(n.node)
def has(n,name):return any(isinstance(x,Atom) and x.low==name for x in n.items) if isinstance(n,Lst) else False
def transform(text):
 p=parse(text);edits=[]
 def append(n,s):edits.append((n.end-1,n.end-1,' '+s))
 for form in p.forms:
  for n in walk(form):
   h=head(n)
   if h=='defun' and len(n.items)>3 and isinstance(n.items[1],Atom) and n.items[1].low in NAMES:
    name=n.items[1].low;args=n.items[2]
    if not has(args,CHILDREN[0]):append(args,' '.join(CHILDREN))
    for x in walk(n.items[3]):
     if head(x)=='xargs':
      xs=x.items
      for i,a in enumerate(xs[:-1]):
       if not isinstance(a,Atom):continue
       if a.low==':stobjs' and not has(xs[i+1],CHILDREN[0]):append(xs[i+1],' '.join(CHILDREN))
       if a.low==':guard' and not any(head(y)=='fn2-run-loads-wfp' for y in walk(xs[i+1])):append(xs[i+1],' '.join('('+c+'-wfp '+c+')' for c in CHILDREN))
    if name in ('fn2-checkpoint-master-preconstructionp','fn2-checkpoint-master-abort-empty-ready-children') and not any(head(y)=='fn2-checkpoint-source-reader-detachedp' for y in walk(n)):
     body=n.items[-1];gate=body if head(body)=='and' else body.items[1]
     append(gate,GATE)
   elif h in NAMES and not has(n,CHILDREN[0]):append(n,' '.join(CHILDREN))
   elif h=='fn2-checkpoint-root1-preserves' and len(n.items)>2 and isinstance(n.items[1],Atom) and n.items[1].low in NAMES:
    if not has(n.items[2],CHILDREN[0]):append(n.items[2],' '.join(CHILDREN))
    for i,a in enumerate(n.items[:-1]):
     if isinstance(a,Atom) and a.low==':hyps' and not any(head(y)=='fn2-run-loads-wfp' for y in walk(n.items[i+1])):append(n.items[i+1],' '.join('('+c+'-wfp '+c+')' for c in CHILDREN))
   elif h=='defcost' and any(isinstance(a,Atom) and a.low in NAMES for a in n.items):
    for i,a in enumerate(n.items[:-1]):
     if isinstance(a,Atom) and a.low==':tables' and not has(n.items[i+1],'fn2-core-run-loads'):append(n.items[i+1],' '.join('fn2-core-'+c[4:] for c in CHILDREN))
 return write(text,edits),len(edits)
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('path',type=Path);a.add_argument('--write',action='store_true');o=a.parse_args();out,n=transform(o.path.read_text())
 if o.write:o.path.write_text(out)
 print(f'{o.path}: {n} abort reader gate edits')
