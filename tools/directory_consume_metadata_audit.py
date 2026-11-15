"""Advisory source footprint of canonical consume, never a runtime decision.

Structural units are native scalar-column/row/array-length GET or SET and a
bounded constant-list spine probe/end. Payload byte loops are audited separately
in their real typed layout; Lisp AST evaluations and declared guards are NOT
work units. Expand only executed function bodies (MBE :exec), generated column
PUT/GET and fixed-column WFP checks actually invoked there. Unknown calls or
unaccounted recursion fail. ACL2 arithmetic constants own admission.
"""
import sys
sys.path.insert(0,'tools')
from pathlib import Path
from collections import Counter
from lisp_source import forms,read_sexp
D={};COL={};GET=set();PUT={}
for p in Path('books').glob('*.lisp'):
 for raw in forms(p.read_text()):
  try:f=read_sexp(raw)
  except:continue
  if not isinstance(f,list) or len(f)<3:continue
  if f[0] in ('defun','defun-inline'):D[f[1]]=(p,f)
  if f[0]=='defcolumns':
   t=f[1];cols=f[2];COL[t]=cols;GET.add(t+'-rows')
   for c in cols:GET.update((t+'-'+c[0],t+'-set-'+c[0],t+'-'+c[0]+'$a-length'))
   if ':extra-fields' in f:
    for q in f[f.index(':extra-fields')+1]:
     n=q[0];GET.update((n,n+'i','update-'+n+'i',n+'-length','update-'+n))
   PUT[t+'-put']=t
LOOPS={'fn2-directory-rebase-transfer-bytes':520,'fn2-directory-rebase-seal-p':8,'fn2-directory-rebase-base-seal':8,'fn2-checkpoint-summary-authority-descriptor-p':32,'fn2-event-catalog-subject-descriptor-p':32,'fn2-directory-rebase-descriptor-matchp':8}
PRIM=set('= < > <= >= + - * / floor mod ash logand logior logxor not equal eql eq nfix ifix natp posp zp unsigned-byte-p integerp rationalp mv'.split())
# Scalar arithmetic/control do not become AST steps. All short-circuit and
# bank alternatives are summed to conservatively bound actual cell interactions.
UNKNOWN=set();BODIES={};ACTIVE=set();SEEN=set()
def ex(x,current=None):
 if not isinstance(x,list):return Counter()
 if not x:return Counter()
 n=x[0]
 if n in ('quote','function'):return Counter()
 if n=='declare':return Counter()
 if n=='mbe':return ex(x[x.index(':exec')+1],current)
 if n in ('let','let*','b*'):
  c=Counter()
  for pair in x[1]:
   c['metadata']+=0
   if isinstance(pair[0],list):c+=ex(pair[0],current)
   c+=ex(pair[1],current)
  for b in x[2:]:c+=ex(b,current)
  return c
 if n in ('cond','case'):
  c=Counter()
  if n=='case':c+=ex(x[1],current)
  for branch in x[1 if n=='cond' else 2:]:
   c['metadata']+=0
   for b in branch[0 if n=='cond' else 1:]:c+=ex(b,current)
  return c
 if n in ('when','unless','if','and','or','mv-let'):
  c=Counter()
  if n=='mv-let':
   c['metadata']+=0;args=x[2:]
  else:args=x[1:]
  for a in args:c+=ex(a,current)
  return c
 if n in PUT:
  t=PUT[n];virtual=['let*',[[t,[t+'-set-'+pair[0],x[1],pair[1],t]] for pair in x[2:]],t]
  return ex(virtual,current)
 if n=='member' or n=='member-equal':
  seq=x[2]
  if isinstance(seq,list) and seq and seq[0]=='list':length=len(seq)-1
  elif isinstance(seq,list) and seq and seq[0]=='quote' and isinstance(seq[1],list):length=len(seq[1])
  else:raise ValueError(('unboundedmember',x))
  # One bounded spine cell probe plus the terminal empty-list check.
  return Counter({'spine':length+1})+ex(x[1],current)+ex(seq,current)
 c=Counter()
 for a in x[1:]:c+=ex(a,current)
 if n in PRIM or n in ('list','endp','car','cdr'):return c
 if n in GET:
  data=(n in {'fn2-checkpoint-bytes-value','fn2-checkpoint-bytes-set-value'} or
        any(n.startswith(prefix) for prefix in ('fn2-checkpoint-summary-authority-descriptori','update-fn2-checkpoint-summary-authority-descriptori','fn2-checkpoint-summary-authority-frontieri','update-fn2-checkpoint-summary-authority-frontieri','fn2-checkpoint-summary-authority-cut-seali','update-fn2-checkpoint-summary-authority-cut-seali','fn2-directory-rebase-seal-wordsi','fn2-checkpoint-restore-events-catalog-descriptori')) or
        n.startswith('fn2-digests-w') and not n.endswith('length') or n.startswith('fn2-digests-set-w') or
        n.startswith('fn2-checkpoint-publication-base-hash-'))
  if not data:c['metadata']+=1
  return c
 if n.endswith('-wfp') and n[:-4] in COL:
  t=n[:-4];shape=['and',['natp',[t+'-rows',t]],['<',[t+'-rows',t],4294967296]]+[['equal',[t+'-'+q[0]+'$a-length',t],[t+'-rows',t]] for q in COL[t]]
  return c+ex(shape,current)
 if n==current:
  if n not in LOOPS:raise ValueError(('unbudgeted recursion',n))
  return c
 if n in D:
  return c+Counter({n:1})
 UNKNOWN.add(n);raise ValueError(('unknown',n))
def body(n):
 if n in BODIES:return BODIES[n].copy()
 if n in ACTIVE:raise ValueError(('unexpectedrecursion',n))
 ACTIVE.add(n);SEEN.add(n)
 p,f=D[n];c=Counter()
 for b in f[3:]:c+=ex(b,n)
 if n in LOOPS:c=Counter({k:v*(LOOPS[n]+1) for k,v in c.items()})
 ACTIVE.remove(n);BODIES[n]=c;return c.copy()
def expanded(n,active=None):
 active=set() if active is None else active
 if n in active:raise ValueError(('expansion cycle',n))
 c=body(n);result=Counter({k:c[k] for k in ('metadata','spine')})
 for name,times in c.items():
  if name not in ('metadata','spine'):
   result.update({key:value*times for key,value in expanded(name,active|{n}).items()})
 return result

def order(n,seen=None):
 seen=set() if seen is None else seen;result=[]
 for name in body(n):
  if name not in ('metadata','spine') and name not in seen:result+=order(name,seen)
 if n not in seen:result.append(n);seen.add(n)
 return result

if __name__=='__main__':
 for name in order('fn2-directory-rebase-consume'):print(name,dict(expanded(name)))
 print('RAW',dict(expanded('fn2-directory-rebase-consume')))
