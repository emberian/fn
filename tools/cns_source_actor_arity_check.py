#!/usr/bin/env python3
"""Advisory actual emitted-function and core-face arity audit; no Lisp eval."""
from pathlib import Path
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def head(n):
 return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def walk(n):
 yield n
 if isinstance(n,lr.Lst):
  for x in n.items:yield from walk(x)
 elif isinstance(n,lr.Pre):yield from walk(n.node)
def forms(path):return lr.parse(ROOT/path).forms
def definitions(path):
 return [n for f in forms(path) for n in walk(f) if head(n)=='defun' and isinstance(n.items[1],lr.Atom) and isinstance(n.items[2],lr.Lst)]
paths=list((ROOT/'books').glob('cns-source-*.lisp'))+[ROOT/'books/cns.lisp']
D={};nodes={}
for path in paths:
 for n in definitions(path.relative_to(ROOT)):
  name=n.items[1].low
  if name.startswith(('fn2-cns-source-','fn2-cns-stream-source-')):
   D[name]=len(n.items[2].items);nodes[name]=n
pairs=[n for f in forms('books/cns-source-core.lisp') for n in walk(f)
       if head(n)=='defconst' and n.items[1].low=='*fn2-cns-source-core-faces*']
assert len(pairs)==1
value=pairs[0].items[2];assert isinstance(value,lr.Pre) and isinstance(value.node,lr.Lst)
aliases={}
for pair in value.node.items:
 assert isinstance(pair,lr.Lst) and len(pair.items)==3 and pair.items[1].low=='.'
 alias,child=pair.items[0].low,pair.items[2].low;n=nodes[child]
 stobjs=[]
 for declaration in n.items[3:]:
  if head(declaration)!='declare':continue
  for x in declaration.items[1:]:
   if head(x)=='xargs':
    for i,a in enumerate(x.items):
     if isinstance(a,lr.Atom) and a.low==':stobjs':
      v=x.items[i+1];stobjs=[z.low for z in v.items] if isinstance(v,lr.Lst) else [v.low]
 assert stobjs and all(s in [a.low for a in n.items[2].items] for s in stobjs)
 aliases[alias]=D[child]-len(stobjs)+1
assert len(aliases)==9
D.update(aliases)
errors=[];calls=0
for name,n in nodes.items():
 if not (name in ('fn2-cns-source-contextp','fn2-cns-source-boundp') or name.startswith('fn2-cns-stream-source-')):continue
 for body in n.items[3:]:
  for call in walk(body):
   if head(call) in D:
    calls+=1
    if len(call.items)-1!=D[head(call)]:errors.append((name,head(call),len(call.items)-1,D[head(call)]))
# Actual DSL operations omit the single implicit core argument.
dsl=0
for f in forms('books/cns.lisp'):
 for n in walk(f):
  call=n.items[2] if head(n)==':do' and len(n.items)>2 else n.items[1] if head(n)==':issue' and len(n.items)>1 else None
  if call is not None and head(call) in D:
   dsl+=1;expected=D[head(call)]-1
   if len(call.items)-1!=expected:errors.append(('DSL',head(call),len(call.items)-1,expected))
assert calls>=20 and dsl>=10
print(f'{len(aliases)} actual lower-derived core faces / {calls} direct source calls / {dsl} DSL source calls; findings: {errors}')
assert not errors
