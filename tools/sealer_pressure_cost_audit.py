"""Advisory source categories for864 pending/wake. No runtime decision/emission.
Generated access formulas are source-template contracts, not executed faces.
Unknown callees/forms fail; no MASTER sequential/controller closure is claimed.
"""
from pathlib import Path
from lisp_source import forms,read_sexp
D={}
for path in ('machines-c-sealer-events','sealer-checkpoint-request','sealer-physical-loader','run-physical-region'):
 for raw in forms(Path('books/'+path+'.lisp').read_text()):
  f=read_sexp(raw)
  candidates=[f]
  if isinstance(f,list) and f[:1]==['defmacro'] and f[2]==[] and f[-1][0]=='quote' and f[-1][1][0]=='progn':candidates=f[-1][1][1:]
  for d in candidates:
   if isinstance(d,list) and d[:1]==['defun']:D[d[1]]=d
# Native metadata reads include the actual core-child GET when present.
ID=2;INDEX=ID+2;FIELD_CODE=ID+INDEX+INDEX+2;FIELD=FIELD_CODE+INDEX+INDEX+2;SNAPSHOT=FIELD_CODE+INDEX
KNOWN={'fn2-machine-kind-base':2,'fn2-machine-idp':ID,'fn2-sealer-snapshot-read-code':SNAPSHOT,'fn2-machine-kind':INDEX,'fn2-machine-slot':INDEX,'fn2-machine-generation':FIELD,'fn2-machine-generation-read-code':FIELD_CODE,'fn2-machine-phase':FIELD,'fn2-machine-stopped':FIELD}
LEAVES=set(['fn2-seals-rows', 'fn2-seals-phase', 'fn2-seals-held', 'fn2-seals-source-receipt', 'fn2-seals-copy-live', 'fn2-seals-prefix-hash-live', 'fn2-seals-prefix-page-live', 'fn2-seals-cbase', 'fn2-checkpoint-summary-rows', 'fn2-checkpoint-summary-phase', 'fn2-checkpoint-summary-tag', 'fn2-checkpoint-summary-generation', 'fn2-checkpoint-summary-candidate', 'fn2-checkpoint-summary-owner-kind', 'fn2-checkpoint-summary-owner-slot', 'fn2-checkpoint-summary-owner-gen', 'fn2-checkpoint-summary-cut-commit', 'fn2-checkpoint-summary-cut-event', 'fn2-checkpoint-predecessor-control-rows', 'fn2-checkpoint-predecessor-control-phase', 'fn2-checkpoint-predecessor-control-token', 'fn2-checkpoint-predecessor-control-candidate', 'fn2-checkpoint-predecessor-control-owner-kind', 'fn2-checkpoint-predecessor-control-owner-slot', 'fn2-checkpoint-predecessor-control-owner-gen', 'fn2-checkpoint-predecessor-control-cut-commit', 'fn2-checkpoint-predecessor-control-cut-event', 'fn2-checkpoint-predecessor-control-completed-originals', 'fn2-checkpoint-predecessor-control-count', 'fn2-csnapshot-rows', 'fn2-csnapshot-phase', 'fn2-c-source-control-rows', 'fn2-c-source-control-phase', 'fn2-sealer-rows', 'fn2-sealer-checkpoint-tag'])
PURE={'and','or','not','=','<','<=','>','>=','equal','eq','natp','posp','nfix','+','-','mv'}
REGION='fn2-run-load-region-freep'
# Source literal geometry; controller/profile joins must use declared provider.
N=8
seen=set()
def body(n):
 if n in KNOWN:return KNOWN[n]
 seen.add(n)
 if n==REGION:return 6*N # six metadata reads per nonterminal; scalar terminal0
 f=D[n]
 return sum(expr(e) for e in f[3:] if not(isinstance(e,list) and e[:1]==['declare']))
def expr(x):
 if not isinstance(x,list) or not x:return 0
 h=x[0]
 if h=='quote':return 0
 if h in ('let','let*'):return sum(expr(b[1]) for b in x[1])+sum(map(expr,x[2:]))
 if h=='b*':return sum(expr(b[1])+(expr(b[0][1]) if isinstance(b[0],list) and b[0][0] in ('unless','when') else 0) for b in x[1])+sum(map(expr,x[2:]))
 if h=='stobj-let':return len(x[1])+expr(x[3])+sum(map(expr,x[4:]))
 if h=='if':return sum(map(expr,x[1:]))
 if h in PURE:return sum(map(expr,x[1:]))
 if h in ('fn2-run-load-region-count','fn2-run-load-region-cursor'):return sum(map(expr,x[1:]))
 if h in D or h in KNOWN:return sum(map(expr,x[1:]))+body(h)
 if h in LEAVES:return 1+sum(map(expr,x[1:]))
 raise ValueError(('unknown actual body/callee',h))
def report():
 return {n:body(n) for n in ('fn2-sealer-checkpoint-pending-op','fn2-sealer-checkpoint-resumed-p','fn2-sealer-checkpoint-resumable-p','fn2-sealer-checkpoint-wake-target')}
if __name__=='__main__':print(report())
