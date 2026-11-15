#!/usr/bin/env python3
"""Scope the authentic summary recursion recipe to directory/archive helpers.

Supplier: d394d6f91:tools/checkpoint_summary_recursion_rewrite.py, unchanged.
Two archive helpers first normalize commutative successor spelling and the
natural-index base to that exact class; no guarded behavior changes.
"""
from pathlib import Path
import lisp_rewrite as lr
from checkpoint_summary_recursion_rewrite import rewrite
TARGETS={
 'books/checkpoint-directory-consume.lisp':{'fn2-directory-rebase-transfer-bytes':520,'fn2-directory-rebase-seal-p':8,'fn2-directory-rebase-base-seal':8},
 'books/event-archive-control.lisp':{'fn2-event-archive-copy-digest':8},
 'books/event-archive-manifest.lisp':{'fn2-event-archive-load-digest':8},
}
def normalize(source,targets):
 edits=[]
 for name,bound in targets.items():
  fn=lr.match('(defun '+name+' ?*body)',lr.parse(source).forms,deep=False)[0].node
  oldbase=lr.match('(>= i '+str(bound)+')',[fn.items[-1]])
  if len(oldbase)>1:raise ValueError('ambiguous archive base')
  if oldbase:
   n=oldbase[0].node;edits.append((n.start,n.end,'(>= (nfix i) '+str(bound)+')'))
  formals=[x.low for x in fn.items[2].items];index=formals.index('i')
  selfcalls=lr.match('('+name+' ?*args)',[fn.items[-1]])
  if len(selfcalls)!=1:raise ValueError('recursive class drift')
  actual=selfcalls[0].node.items[index+1]
  if lr.match('(+ i 1)',[actual],deep=False):edits.append((actual.start,actual.end,'(+ 1 i)'))
 return lr.write(source,edits)
def transform(source,targets):return rewrite(normalize(source,targets),targets)
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 for path,targets in TARGETS.items():
  p=root/path;changed,count=transform(p.read_text(),targets);p.write_text(changed);print(path,count)
