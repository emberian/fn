#!/usr/bin/env python3
"""Conservative literal return-status closure of actual SOURCE definitions.

Follow returned core faces to their declared actual child functions. Conditions
are not assumed true/false: both return branches contribute. Unresolved status
variables/functions fail closed. This is source analysis, not an ACL2 theorem.
"""
from pathlib import Path
import lisp_rewrite as lr
import cns_source_status_routes as r
FILES=('books/cns-source-core.lisp','books/cns-source-raw.lisp','books/cns-source-manifest.lisp')
def definitions(texts):
 result={};aliases={}
 for text in texts:
  p=lr.parse(text)
  for form in p.forms:
   for n in r.walk(form):
    if r.head(n)=='defun' and isinstance(n.items[1],lr.Atom):result[n.items[1].low]=n.items[-1]
   if r.head(form)=='defconst' and r.sym(form.items[1])=='*fn2-cns-source-core-faces*':
    pairs=form.items[2].node
    for pair in pairs.items:aliases[r.sym(pair.items[0])]=r.sym(pair.items[2])
 return result,aliases

def status_closure(texts,subject='fn2-cns-stream-source-step'):
 functions,aliases=definitions(texts);active=set();seen={}
 def value(n):
  if isinstance(n,lr.Atom) and n.low.startswith(':'):return {n.low}
  h=r.head(n)
  if h=='if':return value(n.items[2])|value(n.items[3])
  if h in ('case','cond'):
   start=2 if h=='case' else 1
   return set().union(*(value(c.items[-1]) for c in n.items[start:]))
  raise ValueError('unresolved returned status '+str(n))
 def expression(n):
  h=r.head(n)
  if h=='mv':return value(n.items[1])
  if h=='b*':
   states=expression(n.items[-1])
   for binding in n.items[1].items:
    if isinstance(binding,lr.Lst) and binding.items and r.head(binding.items[0]) in ('unless','when'):
     states |= expression(binding.items[-1])
   return states
  if h in ('let','let*','mv-let','stobj-let'):return expression(n.items[-1])
  if h=='if':return expression(n.items[2])|expression(n.items[3])
  if h in ('cond','case'):
   start=1 if h=='cond' else 2
   return set().union(*(expression(c.items[-1]) for c in n.items[start:]))
  if h in aliases or h in functions:return function(h)
  raise ValueError('unresolved returned function '+h)
 def function(name):
  name=aliases.get(name,name)
  if name in seen:return seen[name]
  if name in active:raise ValueError('recursive returned status '+name)
  if name not in functions:raise ValueError('missing actual return definition '+name)
  active.add(name);states=expression(functions[name]);active.remove(name);seen[name]=states
  return states
 answer=function(subject)
 return answer,seen
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 answer,seen=status_closure([(root/p).read_text() for p in FILES])
 print('actual SOURCEstep return closure: '+', '.join(sorted(answer)))
 for name,states in sorted(seen.items()):print(name+': '+', '.join(sorted(states)))
