#!/usr/bin/env python3
"""Thread only the three mutated park carriers plus readonly pool through CLOSE."""
from pathlib import Path
import argparse
import lisp_rewrite as lr
ADDED=('fn2-run-loads','fn2-checkpoint-summary','fn2-checkpoint-summary-leases')
TARGETS={'fn2-succ-source-close':ADDED+('fn2-pool',),'fn2-succ-resolve-observed':ADDED,'fn2-succ-release-observed':ADDED+('fn2-pool',)}
CORE={'fn2-directory-source-core-definition','fn2-identity-decide'}
PUBLIC={'fn2-successor-resolve','fn2-successor-release','fn2-group-lookup','fn2-principal-lookup','fn2-identity-decide'}
def head(n):return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def atom(n):return n.low if isinstance(n,lr.Atom) else ''
def has(n,name):return isinstance(n,lr.Lst) and any(atom(x)==name for x in n.items)
def transform(text):
 p=lr.parse(text);edits=[]
 def add(n,names):
  missing=[x for x in names if not has(n,x)]
  if missing:edits.append((n.end-1,n.end-1,' '+' '.join(missing)))
 def binding_add(n):
  names={atom(x.items[0]) for x in n.items if isinstance(x,lr.Lst) and x.items}
  new=[x for x in ADDED+('fn2-pool',) if x not in names]
  if new:edits.append((n.end-1,n.end-1,' '+ ' '.join('('+x+' (fn2-core-'+x[4:]+' fn2-core))' for x in new)))
 def visit(n,scope='',binder=False):
  if isinstance(n,lr.Pre):visit(n.node,scope,binder);return
  if not isinstance(n,lr.Lst):return
  h=head(n)
  if h in ('defun','defmacro') and len(n.items)>2:
   name=atom(n.items[1]);nested=name if name in TARGETS or name in CORE else (scope if not name else '')
   if name in TARGETS:add(n.items[2],TARGETS[name])
   for x in n.items[3:]:visit(x,nested)
   return
  if h=='fn2-idc-fn-shape' and len(n.items)>4 and atom(n.items[1]) in TARGETS:
   name=atom(n.items[1]);add(n.items[2],TARGETS[name]);add(n.items[3],ADDED);add(n.items[4],ADDED+('fn2-pool',));return
  if h=='fn2-succ-wrap' and len(n.items)>5 and atom(n.items[1]) in PUBLIC:
   binding_add(n.items[3]);add(n.items[4],ADDED)
   for x in n.items[5:]:visit(x,'core')
   return
  if h=='defcost' and len(n.items)>1 and atom(n.items[1]) in PUBLIC:
   for i,x in enumerate(n.items[:-1]):
    if atom(x)==':tables':add(n.items[i+1],tuple('fn2-core-'+x[4:] for x in ADDED+('fn2-pool',)))
   return
  if scope in TARGETS and h=='xargs':
   for i,x in enumerate(n.items[:-1]):
    if atom(x)==':stobjs':add(n.items[i+1],TARGETS[scope])
  if scope in CORE and h=='stobj-let':binding_add(n.items[1]);add(n.items[2],ADDED)
  if h in TARGETS:add(n,TARGETS[h]);return
  if h=='b*' and len(n.items)>1 and isinstance(n.items[1],lr.Lst):
   for b in n.items[1].items:
    if isinstance(b,lr.Lst) and len(b.items)==2:
     if head(b.items[0])=='mv' and head(b.items[1]) in TARGETS:add(b.items[0],ADDED)
     visit(b.items[0],scope,True);visit(b.items[1],scope)
   for x in n.items[2:]:visit(x,scope)
   return
  if scope in set(TARGETS)|CORE|{'core'} and not binder and h=='mv' and has(n,'fn2-succ-txns') and has(n,'fn2-c-source-control') and has(n,'fn2-c-source-readers'):add(n,ADDED)
  for x in n.items:visit(x,scope,binder)
 for f in p.forms:visit(f)
 return lr.write(text,edits),len(edits)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('paths',type=Path,nargs='+');ap.add_argument('--write',action='store_true');o=ap.parse_args()
 for p in o.paths:
  out,n=transform(p.read_text())
  if o.write:p.write_text(out)
  print(f'{p}: {n} exact park-carrier edits')
