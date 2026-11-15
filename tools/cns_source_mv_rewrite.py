#!/usr/bin/env python3
"""Bind the actual CNS source setter before returning its stobj in MV."""
from pathlib import Path
import lisp_rewrite as lr

def head(n):
 return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def rewrite(text):
 parsed=lr.parse(text); edits=[]
 def walk(n):
  if not isinstance(n,lr.Lst): return
  targets=[(i,x) for i,x in enumerate(n.items) if head(x)=='fn2-cns-sources-set-phase'] if head(n)=='mv' else []
  if targets:
   if len(targets)!=1: raise ValueError('ambiguous CNS stobj MV')
   i,x=targets[0]
   if len(x.items)!=4 or not isinstance(x.items[-1],lr.Atom) or x.items[-1].low!='fn2-cns-sources':
    raise ValueError('unrecognized CNS setter ABI')
   setter=text[x.start:x.end]
   args=[text[a.start:a.end] if j!=i else 'fn2-cns-sources' for j,a in enumerate(n.items)]
   replacement='(let ((fn2-cns-sources '+setter+'))\n        ('+' '.join(args)+'))'
   edits.append((n.start,n.end,replacement));return
  for x in n.items: walk(x)
 for f in parsed.forms:walk(f)
 return lr.write(text,edits),len(edits)
if __name__=='__main__':
 import sys
 p=Path(sys.argv[1]);out,count=rewrite(p.read_text());p.write_text(out);print(count,'actual MV returns rewritten')
