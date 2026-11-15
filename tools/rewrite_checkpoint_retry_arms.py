#!/usr/bin/env python3
"""Connect exact refusal recording to actual master arms using shared spans."""
from pathlib import Path
import sys
from tools.lisp_rewrite import parse,write,Lst,Atom

def h(n):return n.items[0].low if isinstance(n,Lst) and n.items and isinstance(n.items[0],Atom) else ''
def walk(n):
 yield n
 if isinstance(n,Lst):
  for c in n.items:yield from walk(c)
def rewrite(src):
 ed=[];seen=[]
 for t in parse(src).forms:
  for arm in walk(t):
   name=h(arm)
   if name in (':reserve',':directory',':descriptor-begin',':root1-begin'):
    first=next((n for n in arm.items if h(n)==':do'),None)
    if first:
     reason={'reserve':'pool','directory':'directory'}.get(name[1:],'physical')
     ed.append((first.start,first.start,f'(:set (refusal-reason *fn2-checkpoint-retry-{reason}*))\n   '));seen.append(name)
   if name in (':abort-empty',':abort-complete'):
    first=next((n for n in arm.items if h(n)==':set'),None)
    if first:ed.append((first.start,first.start,'(:do (code) (fn2-checkpoint-master-retry-record-op))\n   '));seen.append(name)
   if isinstance(arm,Lst) and arm.items and isinstance(arm.items[0],Lst):
    cases=arm.items[0]
    if [x.low for x in cases.items if isinstance(x,Atom)]==[':no-space',':exhausted',':directory-no-space']:
     tail=src[cases.end:arm.end-1]
     replacement='((:no-space :exhausted) (:set (refusal-reason *fn2-checkpoint-retry-physical*))'+tail+')\n     ((:directory-no-space) (:set (refusal-reason *fn2-checkpoint-retry-directory*))'+tail+')'
     ed.append((arm.start,arm.end,replacement));seen.append('split')
 return write(src,ed),seen

def selftest():
 s='; preserve\n(:reserve :on-refusal ((:next :abort-empty)) (:do (code) (try)))'
 o,c=rewrite(s);assert o.startswith('; preserve\n') and '*fn2-checkpoint-retry-pool*' in o and c==[':reserve']
 s='((:no-space :exhausted :directory-no-space) (:next :cancel-ledger) (:charge :bytes 4096))'
 o,c=rewrite(s);assert o.count(':bytes 4096')==2 and ':directory-no-space' in o and c==['split']
 s='(:abort-complete (:do (code) (complete)) (:set (token 0)))'
 o,c=rewrite(s);assert o.index('(complete)')<o.index('retry-record-op')<o.index('(token 0)')
 assert rewrite('(unrelated x y)')[0]=='(unrelated x y)'
if __name__=='__main__':
 selftest()
 if '--selftest' in sys.argv:print('4 retry-arm rewrite controls passed')
 else:
  p=Path(sys.argv[1]);s=p.read_text();o,c=rewrite(s)
  assert sorted(c)==sorted([':reserve',':directory',':descriptor-begin',':root1-begin',':abort-empty',':abort-complete','split','split','split']),c
  p.write_text(o)
