"""Literal DEFUN guard free-variable preflight, including quoted generated DEFUNs.

No Lisp evaluation or macro expansion. Function positions, quoted data and
self-evaluating literals are not variables. Star names are not assumed to be
constants. LET/LET*/MV-LET scope is handled; unknown
binding constructs refuse instead of being reported safe.
"""
import re
from pathlib import Path
import lisp_rewrite as lr

def atom(n):return n.low if isinstance(n,lr.Atom) else None

def variables(n,bound):
 if isinstance(n,(lr.Str,)):return set()
 if isinstance(n,lr.Pre):
  if n.prefix in ("'","#'"):return set()
  raise ValueError('unresolved guard reader prefix')
 if isinstance(n,lr.Atom):
  s=n.low
  if s in ('t','nil') or s.startswith((':','#')) or re.fullmatch(r'[+-]?[0-9]+(?:/[0-9]+)?',s):return set()
  return set() if s in bound else {s}
 if not isinstance(n,lr.Lst) or not n.items:return set()
 h=atom(n.items[0]);args=n.items[1:]
 if h is None:raise ValueError('unresolved guard function position')
 if h in ('quote','function'):return set()
 if h in ('let','let*'):
  names=set(bound);free=set()
  for binding in args[0].items:
   if isinstance(binding,lr.Atom):names.add(binding.low);continue
   name=atom(binding.items[0]);free|=variables(binding.items[1],names if h=='let*' else bound);names.add(name)
  for body in args[1:]:free|=variables(body,names)
  return free
 if h=='mv-let':
  names=bound|{atom(x) for x in args[0].items};free=variables(args[1],bound)
  for body in args[2:]:free|=variables(body,names)
  return free
 if h in ('b*','lambda','flet','labels'):raise ValueError('unresolved guard binding '+h)
 free=set()
 for x in args:free|=variables(x,bound)
 return free

def definitions(n):
 if isinstance(n,lr.Pre):yield from definitions(n.node)
 elif isinstance(n,lr.Lst):
  if n.items and atom(n.items[0])=='defun':yield n;return
  for x in n.items:yield from definitions(x)

def findings(text):
 out=[];seen=0
 for form in lr.parse(text).forms:
  for d in definitions(form):
   seen+=1;name=atom(d.items[1]);bound={atom(x) for x in d.items[2].items}
   for dec in d.items[3:]:
    if not isinstance(dec,lr.Lst) or not dec.items or atom(dec.items[0])!='declare':continue
    for x in dec.items[1:]:
     if not isinstance(x,lr.Lst) or not x.items or atom(x.items[0])!='xargs':continue
     for i,v in enumerate(x.items[:-1]):
      if atom(v)==':guard':
       free=variables(x.items[i+1],bound)
       if free:out.append((name,sorted(free)))
 return seen,out
if __name__=='__main__':
 import sys
 bad=False
 for f in sys.argv[1:]:
  count,out=findings(Path(f).read_text());print(f,count,'literal definitions;',out);bad|=bool(out)
 raise SystemExit(int(bad))
