#!/usr/bin/env python3
"""Check scalar callback arities from source; never evaluates the ACL2 reader.

Generated root1 faces use their actual operation declaration and shared four
scalar READ signature. This is a narrow integration check, not admission.
"""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk,declaration
files=['checkpoint-teardown','checkpoint-master-control','checkpoint-master-rearm','checkpoint-writer','checkpoint-writer-ops','checkpoint-build','checkpoint-plan','checkpoint-map-build','checkpoint-page-worker','checkpoint-metadata-driver','checkpoint-metadata-resources','checkpoint-working-reserve','checkpoint-metadata-release','checkpoint-working-release','event-build-kind','event-build','event-producer','c-snapshot','checkpoint-allocation-coordinator','checkpoint-installation-coordinator','retirement','retirement-coordinator','checkpoint-lifecycle','event-rearm','checkpoint-master-abort']
files += ['checkpoint-bank-obligations-state','checkpoint-teardown-transfer','checkpoint-summary-authority-live','checkpoint-summary-live-close','checkpoint-directory-rebase','checkpoint-directory-consume','event-catalog-live','checkpoint-cbase-live-acquire','c-source-observer-adapters','checkpoint-live-adoption','checkpoint-live-adoption-rearm','checkpoint-teardown-sweep','checkpoint-teardown-cold-transfer','checkpoint-bank-transfer']
raw={};cost={}
for name in files:
 for source in forms((ROOT/'books'/(name+'.lisp')).read_text()):
  for x in walk(read_sexp(source)):
   if len(x)>2 and x[0]=='defun' and isinstance(x[1],str) and isinstance(x[2],list):raw[x[1]]=[a for a in x[2] if isinstance(a,str) and not a.startswith(('fn2-',''',@'''))]
   if len(x)>2 and x[0] in ('fn2-checkpoint-root1-operation','fn2-live-adoption-operation','fn2-live-adoption-post-operation'):raw[x[1]]=x[2]
   if len(x)>2 and x[0]=='fn2-live-adoption-post-cost':cost[x[1]]=x[2]
   if len(x)>2 and x[0]=='fn2-csnapshot-op':raw[x[1]]=x[2]
   if len(x)>1 and x[0]=='defcost' and isinstance(x[1],str):cost[x[1]]=x[x.index(':child')+1] if ':child'in x else x[1]
raw['fn2-checkpoint-root1-read']=['budget','kind','owner','gen']
# Root1 cost faces emitted by its existing operation macro.
for n in list(raw):
 if n.startswith(('fn2-checkpoint-root1-','fn2-checkpoint-live-adoption-')):cost.setdefault(n+'-op',n)
form=declaration((ROOT/'books/checkpoint-master-arms.lisp').read_text())
for x in walk(form):
 if x and x[0] in (':do',':issue'):
  call=x[2] if x[0]==':do' else x[1]
  name=call[0];target=cost.get(name,name)
  if target not in raw:raise Exception(('missing actual callback',name,target))
  assert len(call)-1==len(raw[target]),(name,len(call)-1,raw[target])
print('master scalar call arities agree with actual source callbacks')
