#!/usr/bin/env python3
"""Bind actual C read operations, arm charges and kind quanta to codec bounds.

Source transformation only. Uses the shared structural reader and preserves
non-reader operations (including physical sector IO) byte for byte.
"""
from __future__ import annotations
from pathlib import Path
import argparse
from lisp_rewrite import parse, write, Lst, Atom, Pre, Str
STEP='*fn2-c-read-step-bytes*'
CALLBACK='*fn2-c-read-callback-bytes*'
STEP_OPS={'fn2-read-lookup','fn2-read-next','fn2-read-seek-step','fn2-read-scan-next','fn2-read-identity',
 'fn2-group-lookup','fn2-principal-lookup','fn2-identity-decide','fn2-successor-resolve',
 'fn2-authority-allows','fn2-txn-group-of','fn2-auth-find-outcome','fn2-auth-find-head','fn2-auth-find-current','fn2-auth-find-grant'}
CALLBACK_OPS={'fn2-sealer-step','fn2-checkpoint-root1-step-op','fn2-checkpoint-root1-consume-op','fn2-cns-lookup-cursor','fn2-cns-item-next','fn2-cns-put-item','fn2-cns-put-article','fn2-cns-decode-port'}
OPS=STEP_OPS|CALLBACK_OPS
KINDS={'fn2-cursor':16384,'fn2-txn':26624,'fn2-auth':32768,'fn2-cns':32768,'fn2-sealer':4096,'fn2-checkpoint-master':16384}
def atom(n,s):return isinstance(n,Atom) and not isinstance(n,Pre) and n.low==s

def nodes(n):
 if isinstance(n,Lst):
  yield n
  for x in n.items:yield from nodes(x)
 elif isinstance(n,Pre):
  # Declarations/macros are the design of record; their static templates
  # are transformed too. No Lisp is evaluated.
  yield from nodes(n.node)

def option(n,key):
 for i,x in enumerate(n.items[:-1]):
  if atom(x,key):return n.items[i+1]
 return None

def operation_present(n):
 return any(isinstance(x,Lst) and x.items and isinstance(x.items[0],Atom) and x.items[0].low in OPS for x in nodes(n))

def transform(text):
 parsed=parse(text);edits={};counts={'costs':0,'charges':0,'budgets':0,'docs':0}
 def replace(n,value,category,allowed=None):
  old=text[n.start:n.end]
  if old==value:return
  if allowed is not None and old not in allowed:raise ValueError(f'unexpected {category} value {old}')
  key=(n.start,n.end)
  if key in edits and edits[key]!=value:raise ValueError('conflicting structural edit')
  edits[key]=value;counts[category]+=1
 for top in parsed.forms:
  for n in nodes(top):
   if not n.items or not isinstance(n.items[0],Atom):continue
   head=n.items[0].low
   if head=='defcost' and len(n.items)>1 and isinstance(n.items[1],Atom) and n.items[1].low in OPS:
    name=n.items[1].low;b=option(n,':bytes')
    if b is None:raise ValueError(f'{name} has no byte cost')
    value=CALLBACK if name in CALLBACK_OPS else STEP
    replace(b,value,'costs',{'4096','2048','8192',value})
    doc=option(n,':doc')
    if isinstance(doc,Str):
     old=text[doc.start:doc.end]
     new=old.replace('one run step of at most 4,096 pool reads','one run step under the generated codec work bound')
     new=new.replace('each of at most eight sources advanced by at most the budget\'s pool reads','at most one actual source advanced under the generated codec work bound')
     new=new.replace('(at most 250-octet compares over 9 probes)', '(under the declared overlay probe and key bounds)')
     if new!=old:replace(doc,new,'docs')
   if head in ('defmachine','fn2-c-actor-loader-kind') and len(n.items)>1 and isinstance(n.items[1],Atom) and n.items[1].low in KINDS:
    old=KINDS[n.items[1].low];budget=option(n,':budget')
    if not isinstance(budget,Lst):raise ValueError('kind budget is not a plist')
    b=option(budget,':bytes')
    if b is None:raise ValueError('kind has no byte quantum')
    # Preserve the old non-reader envelope and admit as many codec work
    # calls as that envelope formerly admitted at the smallest legacy reader cost (2048).
    calls=old//2048+1
    value=f'(+ {old} (* {calls} {CALLBACK}))'
    replace(b,value,'budgets',{str(old),value})
   if head in ('defmachine-arms','fn2-c-actor-loader-arms'):
    for key in (':arms',':subarms'):
     clauses=option(n,key)
     if not isinstance(clauses,Lst):continue
     for clause in clauses.items:
      if not isinstance(clause,Lst) or not operation_present(clause):continue
      for charge in nodes(clause):
       if not charge.items or not atom(charge.items[0],':charge'):continue
       b=option(charge,':bytes')
       if b is None:continue
       original=text[b.start:b.end]
       if original in (CALLBACK,STEP):continue
       # Exact old expression is retained, including symbolic work terms;
       # add the conservative C source charge for this reader-bearing arm.
       if original.startswith(f'(+ {CALLBACK} '):continue
       replace(b,f'(+ {CALLBACK} {original})','charges')
 return write(text,[(a,b,v) for (a,b),v in edits.items()]),counts

def main():
 p=argparse.ArgumentParser();p.add_argument('files',nargs='+',type=Path);p.add_argument('--write',action='store_true');a=p.parse_args()
 for path in a.files:
  result,counts=transform(path.read_text());print(path,counts)
  if a.write:path.write_text(result)
if __name__=='__main__':main()
