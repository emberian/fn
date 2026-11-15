"""Source-only known-arity check of actual READ function bodies and core wrappers.

Skips quoted data, theorem hints and binders; this is not macroexpansion, ACL2
admission or a complete-world check. Shared definitions may have multiple
source arities; a call must match an actual source definition.
"""
from pathlib import Path
import sys
sys.path.insert(0,'tools');import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym
known={}; targets=[]
for p in Path('books').glob('*.lisp'):
 for f in lr.parse(p.read_text()).forms:
  for n in nodes(f):
   if isinstance(n,lr.Lst) and len(n.items)>3 and sym(n.items[0])=='defun' and sym(n.items[1]).startswith('fn2-') and isinstance(n.items[2],lr.Lst):
    known.setdefault(sym(n.items[1]),set()).add(len(n.items[2].items))
    if p.name=='machines-c-read.lisp':targets.append(n)
errors=[];checked=0
def visit(n):
 global checked
 if isinstance(n,lr.Pre):return
 if not isinstance(n,lr.Lst) or not n.items:return
 h=sym(n.items[0]);a=n.items
 if h in {'quote','declare'}:return
 if h in {'let','let*','b*'}:
  for b in a[1].items:
   if isinstance(b,lr.Lst) and len(b.items)==2:
    lhs=b.items[0]
    if isinstance(lhs,lr.Lst) and lhs.items and sym(lhs.items[0]) in {'when','unless'}:
     for x in lhs.items[1:]:visit(x)
    visit(b.items[1])
  for x in a[2:]:visit(x)
  return
 if h=='mv-let':
  for x in a[2:]:visit(x)
  return
 if h=='stobj-let':
  for b in a[1].items:
   for x in b.items[1:]:visit(x)
  for x in a[3:]:visit(x)
  return
 if h in {'cond','case','case-match'}:
  start=1 if h=='cond' else 2
  if start==2:visit(a[1])
  for c in a[start:]:
   if isinstance(c,lr.Lst):
    for x in c.items[(0 if h=='cond' else 1):]:visit(x)
  return
 if h in known:
  checked+=1
  if len(a)-1 not in known[h]:errors.append((h,len(a)-1,sorted(known[h])))
 for x in a[1:]:visit(x)
for n in targets:
 for b in n.items[3:]:visit(b)
print('Actual executable known-arity calls:',checked,'errors:',errors)
assert not errors
