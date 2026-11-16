"""Literal source-only include frontier, not an ACL2 world/refinement check."""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[1]
ROOTS=['checkpoint-master-state','checkpoint-master-events','assembly-callbacks-e-cns']
def report():
 seen=set();active=[];missing=set();cycles=[]
 def visit(p):
  p=p.resolve()
  if p in active:cycles.append([str(x.relative_to(ROOT)) for x in active[active.index(p):]+[p]]);return
  if p in seen:return
  active.append(p)
  for m in re.finditer(r'\(include-book\s+"([^"]+)"([^\n]*)',p.read_text()):
   if ':dir' in m.group(2):continue
   q=(p.parent/(m.group(1)+'.lisp')).resolve()
   if q.exists():visit(q)
   else:missing.add(str(q.relative_to(ROOT)))
  active.pop();seen.add(p)
 for b in ROOTS:visit(ROOT/'books'/(b+'.lisp'))
 return {'scope':'literal local includes only; no macroexpansion/admission/runtime claim',
         'base':'0abe4398c','master_events_and_pressure_donor':'864f4dcac',
         'roots':ROOTS,'local_books':len(seen),'cycles':cycles,'missing':sorted(missing),
         'prepared_fixture_dependency':'tests/checkpoint-second-adoption-support.lisp and its canonical SIM/actual-producer closure are not imported by this slice',
         'additional_registration_frontier':[
           'Actual MASTER kind/corechild declaration must enter the current pre-index/core profile assembly.',
           'Actual MASTER row must be created by current executor startup/genesis.',
           'Canonical page/writer/event/summary/live owner macro providers must match current guarded coordinator ABI.',
           'New inventory/request/wake/controller charges require exact cost binding before qualification.',
           'Activation remains NIL; prepared downstream fixture uses explicit existing test-only CATALOG entry.']}
if __name__=='__main__':print(json.dumps(report(),indent=2))
