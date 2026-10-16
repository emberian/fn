#!/usr/bin/env python3
"""Widen only pin-value substitutions in selected theorem hints."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'tools'))
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[2]
VALUE='(cons (fn-ocfg-config oc) (fn-ocfg-conn-profile oc id))'
TARGETS={
 'books/config-owner-live-read.lisp':['fn-ocl-read-preserves-historical-relation-repinned'],
 'books/owner-host-relation.lisp':['fn-ohr-read-step-preserves-ocl-relation-repinned'],
 'books/config-owner-advance-invariants.lisp':['fn-ocl-advanced-preserves-all-connection-histories','fn-ocl-advanced-preserves-connection-and-pin-clauses']}
def transform(text,names):
 parsed=lr.parse(text);edits=[]
 for name in names:
  n=lr.match(None,parsed.forms,head='defthm',name=name)[0].node
  idx=next(i for i,x in enumerate(n.items) if isinstance(x,lr.Atom) and x.low==':hints')
  hints=n.items[idx+1]
  for m in lr.match('(cfg (fn-ocfg-config oc))',[hints]):
   arg=m.node.items[1];edits.append((arg.start,arg.end,VALUE))
  for m in lr.match('(fn-ocfg-pin-set id (fn-ocfg-config oc) ?pins)',[hints]):
   arg=m.node.items[2];edits.append((arg.start,arg.end,VALUE))
  for inst in ['fn-ocl-pin-set-preserves-connection-coverage','fn-ocl-pin-set-preserves-pin-domain']:
   for m in lr.match(None,[hints],head=':instance',name=inst):
    if not any(isinstance(x,lr.Lst) and x.items and isinstance(x.items[0],lr.Atom) and x.items[0].low=='cfg' for x in m.node.items[2:]):
     edits.append((m.end-1,m.end-1,'\n                            (cfg '+VALUE+')'))
 return lr.write(text,edits),len(edits)
def fixtures():
 src='(defthm x (equal (fn-ocfg-pin-set id (fn-ocfg-config oc) pins) x) :hints (("Goal" :use ((:instance t (cfg (fn-ocfg-config oc)))))))'
 got,n=transform(src,['x']);assert n==1 and got==src.replace('(cfg (fn-ocfg-config oc))','(cfg '+VALUE+')')
 src='(defthm x t :hints (("Goal" :use ((:instance t (pins (fn-ocfg-pin-set id (fn-ocfg-config oc) pins)))))))'
 got,n=transform(src,['x']);assert n==1 and got==src.replace('(fn-ocfg-config oc)',VALUE)
 src='(defthm x t :hints (("Goal" :use ((:instance fn-ocl-pin-set-preserves-pin-domain (pins pins))))))'
 got,n=transform(src,['x']);assert n==1 and '(cfg '+VALUE+')' in got
 assert transform(got,['x'])==(got,0)
if __name__=='__main__':
 fixtures()
 for path,names in TARGETS.items():
  p=ROOT/path;new,count=transform(p.read_text(),names)
  if count:p.write_text(new)
  print(path,count,'hint edits')
