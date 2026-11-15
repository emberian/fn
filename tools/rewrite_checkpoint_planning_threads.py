#!/usr/bin/env python3
"""Thread actual planning carriers through the three root1 page constructors.
Uses lisp_rewrite spans; never regenerates a whole commented book.
"""
from pathlib import Path
from tools.lisp_rewrite import parse,write,Lst,Atom,Pre
import sys
TARGETS={'fn2-checkpoint-metadata-page-for-build','fn2-checkpoint-metadata-page','fn2-checkpoint-metadata-manifest-page'}
EXTRA='fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order'
def head(n):return n.items[0].low if isinstance(n,Lst) and n.items and isinstance(n.items[0],Atom) else ''
def walk(n):
 yield n
 if isinstance(n,Lst):
  for x in n.items:yield from walk(x)
 elif isinstance(n,Pre):yield from walk(n.node)
def hascall(n):return any(head(x) in TARGETS for x in walk(n))
def rewrite(text):
 tree=parse(text);edits=[];done=set()
 def append(n,s=EXTRA):
  if n.end not in done:edits.append((n.end-1,n.end-1,' '+s));done.add(n.end)
 for top in tree.forms:
  if head(top)=='defun' and top.items[1].low in TARGETS:
   append(top.items[2])
   binders={id(n.items[0]) for n in walk(top) if isinstance(n,Lst) and len(n.items)==2 and head(n.items[0])=='mv'}
   for n in walk(top):
    if head(n)=='mv' and id(n) not in binders:append(n)
    if isinstance(n,Lst):
     for i,x in enumerate(n.items[:-1]):
      if isinstance(x,Atom) and x.low==':stobjs':append(n.items[i+1])
      if isinstance(x,Atom) and x.low==':guard':append(n.items[i+1], ' '.join('('+a+'-wfp '+a+')' for a in EXTRA.split()))
  for n in walk(top):
   if head(n) in TARGETS:append(n)
   if head(n)=='mv-let' and len(n.items)>=4 and hascall(n.items[2]):append(n.items[1])
   if isinstance(n,Lst) and len(n.items)==2 and head(n.items[0])=='mv' and hascall(n.items[1]):append(n.items[0])
 return write(text,edits)
def selftest():
 src='(defun fn2-checkpoint-metadata-page (x) (declare (xargs :stobjs (s) :guard (and p))) (mv :ok s))'
 out=rewrite(src)
 assert out.count(EXTRA)==3 and '(and p (fn2-checkpoint-planning-wfp' in out
 src='; keep\n(b* (((mv c s) (if p (fn2-checkpoint-metadata-page x) (fn2-checkpoint-metadata-manifest-page y)))) (mv c s))'
 out=rewrite(src);assert out.startswith('; keep\n') and out.count(EXTRA)==3
 src='(defun fn2-checkpoint-metadata-page (x) (declare (xargs :stobjs (s) :guard (and p))) (b* (((mv c s) (ordinary s))) (mv c s)))'
 assert '(mv c s) (ordinary s)' in rewrite(src)
 src='(mv-let (c s) (fn2-checkpoint-metadata-page x) (mv c s))'
 assert rewrite(src).count(EXTRA)==2
 assert rewrite('(other (mv x y))')=='(other (mv x y))'
if __name__=='__main__':
 selftest()
 if '--selftest' in sys.argv:print('5 planning-thread rewrite controls passed')
 else:
  for f in sys.argv[1:]:
   p=Path(f);p.write_text(rewrite(p.read_text()))
