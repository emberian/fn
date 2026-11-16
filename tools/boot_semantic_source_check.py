"""Executable-context source arities; no evaluation, proof or complete world."""
from pathlib import Path
import lisp_rewrite as lr

def sym(n):return getattr(n,'low','')
def nodes(n):
 yield n
 if isinstance(n,lr.Lst):
  for a in n.items:yield from nodes(a)
 elif isinstance(n,lr.Pre):yield from nodes(n.node)
known={};targets=[]
books=('checkpoint-restore-semantic-source','checkpoint-restore-semantic','checkpoint-restore-semantic-work',
       'checkpoint-restore-reach-core','checkpoint-restore-semantic-reach','checkpoint-summary-catalog','boot-semantic-consumer')
for path in Path('books').glob('*.lisp'):
 for f in lr.parse(path.read_text()).forms:
  for n in nodes(f):
   if isinstance(n,lr.Lst) and len(n.items)>3 and sym(n.items[0])=='defun' and sym(n.items[1]).startswith('fn2-') and isinstance(n.items[2],lr.Lst):
    known.setdefault(sym(n.items[1]),set()).add(len(n.items[2].items))
    if path.stem in books:targets.append(n)
errors=[];checked=0;mvchecked=0
mv={'fn2-checkpoint-restore-semantic-begin':2,'fn2-checkpoint-summary-begin':2,'fn2-pool-reset':2,'fn2-pool-copy-range':2,
    'fn2-checkpoint-restore-semantic-page':8,'fn2-checkpoint-restore-reach-claim':2,'fn2-checkpoint-restore-semantic-entry':2,
    'fn2-checkpoint-restore-semantic-track':3,'fn2-checkpoint-restore-semantic-enqueue':4,'fn2-checkpoint-restore-map-consume':5,
    'fn2-checkpoint-summary-load-hash':2}
def visit(n):
 global checked,mvchecked
 if isinstance(n,lr.Pre) or not isinstance(n,lr.Lst) or not n.items:return
 h=sym(n.items[0]);a=n.items
 if h in {'quote','declare'}:return
 if h in {'let','let*','b*'}:
  for b in a[1].items:
   if isinstance(b,lr.Lst) and len(b.items)==2:
    lhs,call=b.items
    if isinstance(lhs,lr.Lst) and lhs.items:
     if sym(lhs.items[0]) in {'when','unless'}:
      for x in lhs.items[1:]:visit(x)
     if sym(lhs.items[0])=='mv' and isinstance(call,lr.Lst) and call.items and sym(call.items[0]) in mv:
      mvchecked+=1
      if len(lhs.items)-1!=mv[sym(call.items[0])]:errors.append(('MV',sym(call.items[0]),len(lhs.items)-1,mv[sym(call.items[0])]))
    visit(call)
  for x in a[2:]:visit(x)
  return
 if h=='mv-let':
  for x in a[2:]:visit(x)
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
 if h=='mv' and len(a)-1>32:errors.append(('MVlimit',len(a)-1))
 for x in a[1:]:visit(x)
for n in targets:
 for body in n.items[3:]:visit(body)
print('Semantic source calls',checked,'known MV',mvchecked,'errors',errors)
assert not errors
