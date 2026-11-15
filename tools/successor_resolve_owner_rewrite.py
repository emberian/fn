#!/usr/bin/env python3
"""Compose the raw/cleanup resolver class with its actual physical owner ABI."""
import lisp_rewrite as lr
NAMES={'fn2-succ-resolve','fn2-succ-resolve-raw'}
def add(args,source):
 values=[getattr(x,'low',None) for x in args.items]
 if values[:6]==['tx','budget','b0','qk','qs','qg']:return None
 if values[:3]!=['tx','budget','b0'] or values[3]!='fn2-succ-txns':raise ValueError('resolver formal ABI drift')
 return args.items[3].start,args.items[3].start,'qk qs qg '
def transform(source):
 edits=[];defs=[]
 for m in lr.match('(defun ?name ?args ?*body)',lr.parse(source).forms,deep=False):
  if m.captures['name'].low not in NAMES:continue
  defs.append(m.node);e=add(m.captures['args'],source)
  if e:edits.append(e)
 if len(defs)!=2:raise ValueError('expected both raw and public resolver')
 for m in lr.match('(fn2-idc-fn-shape ?name ?args ?*body)',lr.parse(source).forms,deep=False):
  if m.captures['name'].low in NAMES:
   e=add(m.captures['args'],source)
   if e:edits.append(e)
 for fn in defs:
  for name in ['fn2-succ-resolve-raw','fn2-succ-resolve-step']:
   for m in lr.match('('+name+' ?*args)',[fn.items[-1]]):
    actual=m.node.items[1:];prefix=[getattr(x,'low',None) for x in actual[:6]]
    if prefix==['tx','budget','b0','qk','qs','qg']:continue
    if prefix[:3]!=['tx','budget','b0'] or prefix[3]!='fn2-succ-txns':raise ValueError('resolver call ABI drift')
    edits.append((actual[3].start,actual[3].start,'qk qs qg '))
 return lr.write(source,edits),len(edits)
if __name__=='__main__':
 from pathlib import Path
 p=Path(__file__).resolve().parents[1]/'books/machines-c-successor.lisp'
 after,count=transform(p.read_text());p.write_text(after);print(count)
