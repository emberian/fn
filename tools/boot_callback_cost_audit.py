"""SOURCE categories for BOOT wrappers; no ACL2 evaluation or runtime decision.

Uses the existing canonical source walker. Byte primitives retain their accepted
boundary; fixed metadata outside them is expanded. Unknowns fail closed.
"""
from collections import Counter
from pathlib import Path
from lisp_source import forms,read_sexp
import directory_consume_metadata_audit as a
# ENCAPSULATE's direct production DEFUN events are actual book events; skip
# LOCAL/proofs and never mine quoted function-shaped data.
for path in Path('books').glob('*.lisp'):
 for raw in forms(path.read_text()):
  f=read_sexp(raw)
  if isinstance(f,list) and f[:1]==['encapsulate']:
   for d in f[2:]:
    if isinstance(d,list) and d[:1]==['defun']:a.D[d[1]]=(path,d)
OLD=a.ex
INDEX=4;FIELD=22;SNAPSHOT=16
COST={'fn2-machine-kind':INDEX,'fn2-machine-generation':INDEX,'fn2-boot-snapshot-read-code':SNAPSHOT}
BYTE_PRIMITIVES={'fn2-pool-read','fn2-pool-write','fn2-pool-compare','fn2-layout-copy','fn2-boot-pad','fn2-pool-append-text','fn2-b3-init','fn2-b3-update','fn2-b3-finalize','fn2-codec-emit-fixed','fn2-codec-emit-varint','fn2-codec-emit-be','fn2-checkpoint-restore-zero-range','fn2-digest-store'}
# Only actual machine fields reached by these provider bodies.
FIELDS='pending stage index total phase image-size checkpoint-index offset pool-slot pool-gen rx-slot rx-gen event-ready outcome count create checkpoint-length'.split()
COST.update({'fn2-machine-'+f:FIELD for f in FIELDS})
WRAPPERS=('fn2-boot-checkpoint-owner-p','fn2-boot-checkpoint-read-complete-p','fn2-boot-bootstrap-offset','fn2-boot-bootstrap-pack','fn2-boot-bootstrap-verify','fn2-boot-checkpoint-anchor-zero','fn2-boot-checkpoint-anchor-step','fn2-boot-checkpoint-descriptor-target','fn2-boot-checkpoint-descriptor-check')
# Callback leaves are summarized separately, never silently zeroed.
LOWER={'fn2-boot-bootstrap-pack-pool','fn2-boot-bootstrap-verify-pool','fn2-boot-anchor-admit-pool','fn2-boot-checkpoint-descriptor-pool','fn2-boot-checkpoint-descriptor-target-pool','fn2-boot-bootstrap-current-p'}
a.LOOPS.update({'fn2-boot-descriptor-geometry-matches-p':8,'fn2-checkpoint-boot-geometry-copy':8,'fn2-checkpoint-restore-load-hash':8,'fn2-checkpoint-hash-matchesp':32,'fn2-checkpoint-capture-roots':5,'fn2-checkpoint-copy-hash':32,'fn2-boot-save-geometry':32,'fn2-boot-save-anchor-digest':32,'fn2-checkpoint-copy-expected':32})
CODECS={'fn2-checkpoint-geometry-record-encode':(30,1),'fn2-format-bootstrap-encode':(28,4),'fn2-format-anchor-decode':(26+20*15,1),'fn2-format-checkpoint-descriptor-decode':(26+20*38,1)}
def ex(x,current=None):
 if isinstance(x,list) and x:
  n=x[0]
  if n=='member-eq':return OLD(['member-equal']+x[1:],current)
  if n in ('fn2-boot-config-geometryi','update-fn2-boot-config-geometryi','fn2-boot-config-anchor-evidencei','update-fn2-boot-config-anchor-evidencei'):return sum((ex(t,current) for t in x[1:]),Counter())
  if n=='stobj-let':return Counter(metadata=len(x[1])+len(set(b[0] for b in x[1])&set(x[2])))+sum((ex(t,current) for t in x[3:]),Counter())
  if n=='fn2-format-run':return Counter({'@format-run':1})+sum((ex(t,current) for t in x[1:]),Counter())
  if n=='fn2-pool-block-hash-loop':return Counter({'fn2-b3-ready':4,'spine':12})+sum((ex(t,current) for t in x[1:]),Counter())
  if n in CODECS:
   cells,ranges=CODECS[n]
   return Counter(metadata=cells,**{'fn2-layout-range-code':ranges})+sum((ex(t,current) for t in x[1:]),Counter())
  if n=='fn2-boot-geometry-fields':return Counter(metadata=15)+sum((ex(t,current) for t in x[1:]),Counter())
  if n=='fn2-boot-anchor-return':return sum((ex(t,current) for t in x[1:]),Counter())
  if n in COST:return Counter(metadata=COST[n])+sum((ex(t,current) for t in x[1:]),Counter())
  if n in LOWER and current in WRAPPERS:return Counter({n:1})+sum((ex(t,current) for t in x[1:]),Counter())
  if n in BYTE_PRIMITIVES:return sum((ex(t,current) for t in x[1:]),Counter())
  if n=='null':return sum((ex(t,current) for t in x[1:]),Counter())
 return OLD(x,current)
a.ex=ex

def wrapper(n):
 # Expand all actual local wrapper helpers, retaining lower typed components.
 def expand(name):
  c=a.body(name);result=Counter()
  for key,v in c.items():
   if key in LOWER or key in ('metadata','spine'):result[key]+=v
   else:result.update({k:z*v for k,z in expand(key).items()})
  return result
 return dict(expand(n))
if __name__=='__main__':
 for n in WRAPPERS:print(n,wrapper(n))

def full(n):
 def expand(name,active=()):
  if name in active:raise ValueError(('unaccounted recurrence',name))
  c=a.body(name);out=Counter()
  for key,v in c.items():
   if key in ('metadata','spine') or key.startswith('@'):out[key]+=v
   else:out.update({k:z*v for k,z in expand(key,active+(name,)).items()})
  return out
 return expand(n)
