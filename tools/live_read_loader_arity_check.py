"""Known source arities/explicit MV binding counts, not ACL2 admission."""
from pathlib import Path
import lisp_rewrite as lr
import read_observer_arity_check as arity
from read_observer_rewrite import nodes,sym
arity.errors=[];arity.checked=0;mvchecked=0
known_mv={'fn2-run-load-reserve':3,'fn2-run-load-release':6,
 'fn2-run-load-region-fill':6,'fn2-run-load-region-clean':6,'fn2-run-load-region-reserve':7,
 'fn2-run-load-region-drain':2,'fn2-run-load-region-suffix':2,'fn2-read-loader-job':2,
 'fn2-read-loader-selected':2,'fn2-read-loader-drain':2,'fn2-read-loader-suffix':2}
for name in ('run-physical-region','run-physical-range','machines-c-read-loader'):
 for f in lr.parse(Path('books/'+name+'.lisp').read_text()).forms:
  if isinstance(f,lr.Lst) and len(f.items)>3 and sym(f.items[0])=='defun':
   for b in f.items[3:]:arity.visit(b)
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or len(n.items)!=2:continue
   lhs,call=n.items
   if isinstance(lhs,lr.Lst) and lhs.items and sym(lhs.items[0])=='mv' and isinstance(call,lr.Lst) and call.items and sym(call.items[0]) in known_mv:
    mvchecked+=1
    if len(lhs.items)-1!=known_mv[sym(call.items[0])]:arity.errors.append(('MV',sym(call.items[0]),len(lhs.items)-1,known_mv[sym(call.items[0])]))
print('Loader calls:',arity.checked,'explicit known MV:',mvchecked,'errors:',arity.errors)
assert not arity.errors
