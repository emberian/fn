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
from lisp_source import forms,read_sexp,generated_definition_expansion
D={};COL={};GET=set();PUT={};LITERAL_PROVIDERS={};PAYLOAD_MODE=False

def literal_definitions(form):
 """Only definitions emitted verbatim by a nullary literal PROGN macro.

 No Lisp evaluation, arbitrary tree mining or expansion of computed templates.
 Unquote/backquote constructors do not qualify as actual literal definitions.
 """
 if not isinstance(form,list) or len(form)<3:return []
 if form[0] in ('defun','defun-inline'):return [form]
 if form[0]!='defmacro' or form[2]!=[]:return []
 literal=form[-1]
 if not (isinstance(literal,list) and len(literal)==2 and literal[0]=='quote' and isinstance(literal[1],list) and literal[1] and literal[1][0]=='progn'):return []
 return [child for child in literal[1][1:] if isinstance(child,list) and len(child)>3 and child[0] in ('defun','defun-inline') and isinstance(child[1],str)]

for p in Path('books').glob('*.lisp'):
 for raw in forms(p.read_text()):
  try:f=read_sexp(raw)
  except:continue
  if not isinstance(f,list) or len(f)<2:continue
  generated=generated_definition_expansion(f)
  candidates=[definition for event in generated for definition in literal_definitions(event)] if generated is not None else literal_definitions(f)
  for definition in candidates:
   name=definition[1]
   if name in D and D[name][1]!=definition:raise ValueError(('ambiguous source definition',name,D[name][0],p))
   D[name]=(p,definition)
   if f[0]=='defmacro':LITERAL_PROVIDERS[name]=(p,f[1])
  if f[0]=='defmachine' and ':fields' in f and isinstance(f[f.index(':fields')+1],list):
   # SAME machine table generator: PHASE + four non-directory common fields
   # (generation/principal-slot/account-ref/deadline) + declared kind fields.
   t=f[1];cols=[['phase',':u8'],['generation',':u60'],['principal-slot',':u16'],['account-ref',':u32'],['deadline',':u60']]+f[f.index(':fields')+1]
   GET.add(t+'-rows')
   for c in cols:GET.update((t+'-'+c[0],t+'-set-'+c[0],t+'-'+c[0]+'$a-length'))
   if ':sub' not in f:COL[t]=cols;PUT[t+'-put']=t
  if f[0]=='make-event' and len(f)==2 and isinstance(f[1],list) and len(f[1])==2 and f[1][0]=='quasiquote':
   literal=f[1][1]
   if isinstance(literal,list) and literal[:2]==['defcolumns','fn2-machines']:
    # Exact one named splice of MACHINE-FORM directory fields; no general
    # evaluation of MAKE-EVENT or arbitrary declaration templates.
    literal=list(literal);cols=[]
    for col in literal[2]:
     if col==['unquote-splicing','*fn2-machine-directory-fields*']:
      cols.extend([['ready-prev',':link'],['ready-next',':link'],['wait-reason',':u8']])
     else:cols.append(col)
    literal[2]=cols;f=literal
  if f[0]=='defcolumns':
   t=f[1];cols=f[2];COL[t]=cols;GET.add(t+'-rows')
   for c in cols:GET.update((t+'-'+c[0],t+'-set-'+c[0],t+'-'+c[0]+'$a-length'))
   if ':extra-fields' in f:
    for q in f[f.index(':extra-fields')+1]:
     n=q[0];GET.update((n,n+'i','update-'+n+'i',n+'-length','update-'+n))
   PUT[t+'-put']=t
LOOPS={'fn2-checkpoint-live-query-descriptor-p':32,'fn2-checkpoint-cbase-row-hash-p':8,'fn2-checkpoint-live-catalog-descriptor-p':32,'fn2-checkpoint-summary-live-published-hash-p':8,'fn2-checkpoint-production-roots-p':6,'fn2-event-producer-roots-p':2,'fn2-directory-rebase-transfer-bytes':520,'fn2-directory-rebase-seal-p':8,'fn2-directory-rebase-base-seal':8,'fn2-checkpoint-summary-authority-descriptor-p':32,'fn2-event-catalog-subject-descriptor-p':32,'fn2-directory-rebase-descriptor-matchp':8}
PRIM=set('= < > <= >= + - * / floor mod ash logand logior logxor not equal eql eq nfix ifix natp posp zp unsigned-byte-p integerp rationalp ceiling max min mv'.split())
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
  c=Counter();branches=[]
  if n=='case':c+=ex(x[1],current)
  for branch in x[1 if n=='cond' else 2:]:
   part=Counter()
   for b in branch[0 if n=='cond' else 1:]:part+=ex(b,current)
   branches.append(part);c+=part
  if PAYLOAD_MODE and n=='case' and current in {'fn2-checkpoint-publication-base-word','fn2-checkpoint-cbase-word'}:
   if any(key not in ('metadata','spine','payload-read','payload-write') for part in branches for key in part):raise ValueError(('nonleaf payload selector',current))
   for key in ('payload-read','payload-write'):c[key]=max((v[key] for v in branches),default=0)
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
        any(n.startswith(prefix) for prefix in ('fn2-checkpoint-summary-authority-descriptori','update-fn2-checkpoint-summary-authority-descriptori','fn2-checkpoint-summary-authority-frontieri','update-fn2-checkpoint-summary-authority-frontieri','fn2-checkpoint-summary-authority-cut-seali','update-fn2-checkpoint-summary-authority-cut-seali','fn2-directory-rebase-seal-wordsi','fn2-checkpoint-restore-events-catalog-descriptori','fn2-checkpoint-summary-descriptori','update-fn2-checkpoint-summary-descriptori','fn2-checkpoint-cbase-holds-hash-')) or
        n.startswith('fn2-digests-w') and not n.endswith('length') or n.startswith('fn2-digests-set-w') or
        n.startswith('fn2-checkpoint-publication-base-hash-')) and not n.endswith('length')
  if not data:c['metadata']+=1
  elif PAYLOAD_MODE:
   width=1 if ('descriptori' in n or n in {'fn2-checkpoint-bytes-value','fn2-checkpoint-bytes-set-value'}) else 4
   c['payload-write' if n.startswith('update-') or '-set-' in n else 'payload-read']+=width
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
 if n not in D:raise ValueError(('unknown root/provider',n))
 ACTIVE.add(n);SEEN.add(n)
 try:
  p,f=D[n];c=Counter()
  bodies=[b for b in f[3:] if not (isinstance(b,list) and b and b[0]=='declare')]
  if n in LOOPS:
   if len(bodies)!=1:raise ValueError(('loop body must be explicit single form',n))
   b=bodies[0];limit=LOOPS[n]
   if b[0]=='if' and len(b)==4:
    c=ex(b[1],n);c=Counter({k:v*(limit+1) for k,v in c.items()})
    c+=ex(b[2],n)
    recursive=ex(b[3],n);c+=Counter({k:v*limit for k,v in recursive.items()})
   elif b[0]=='or' and len(b)==3:
    c=ex(b[1],n);c=Counter({k:v*(limit+1) for k,v in c.items()})
    recursive=ex(b[2],n);c+=Counter({k:v*limit for k,v in recursive.items()})
   else:raise ValueError(('unclassified loop terminal/iteration split',n))
  else:
   for b in bodies:c+=ex(b,n)
  BODIES[n]=c;return c.copy()
 finally:ACTIVE.discard(n)

def expanded(n,active=None):
 active=set() if active is None else active
 if n in active:raise ValueError(('expansion cycle',n))
 c=body(n);terminal=('metadata','spine','payload-read','payload-write') if PAYLOAD_MODE else ('metadata','spine');result=Counter({k:c[k] for k in terminal})
 for name,times in c.items():
  if name not in terminal:
   result.update({key:value*times for key,value in expanded(name,active|{n}).items()})
 return result

def order(n,seen=None):
 seen=set() if seen is None else seen;result=[]
 for name in body(n):
  if name not in ('metadata','spine','payload-read','payload-write') and name not in seen:result+=order(name,seen)
 if n not in seen:result.append(n);seen.add(n)
 return result

def payload_footprint(root):
 """Advisory native byte footprint using the SAME parsed bodies/recurrence.

 Only the two actual word selectors use CASE max (one word), all other
 alternatives remain summed. No execution, semantic source walk or charge.
 """
 global PAYLOAD_MODE,BODIES,ACTIVE,SEEN
 saved=(PAYLOAD_MODE,BODIES,ACTIVE,SEEN)
 PAYLOAD_MODE=True;BODIES={};ACTIVE=set();SEEN=set()
 try:return expanded(root)
 finally:PAYLOAD_MODE,BODIES,ACTIVE,SEEN=saved

if __name__=='__main__':
 for name in order('fn2-directory-rebase-consume'):print(name,dict(expanded(name)))
 print('RAW',dict(expanded('fn2-directory-rebase-consume')))
