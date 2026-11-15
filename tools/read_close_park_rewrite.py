"""Thread canonical READ region CLOSE through actual child/core callbacks.

One structural projection; the RD kernels stay byte-identical. Mutating READ
operations return only actual mutable carriers, never their readonly pool.
"""
from pathlib import Path
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym,MUT
PARK=['fn2-run-loads','fn2-run-cursors','fn2-checkpoint-summary','fn2-checkpoint-summary-leases']
MORE=['fn2-id-decides',*PARK,'fn2-pool']
BASE=['fn2-reads','fn2-c-source-control','fn2-c-source-readers']
def project(src,helpers):
 if '(defun fn2-read-source-close ' in src:raise ValueError('READ CLOSE already projected')
 p=lr.parse(src);edits=[]
 def text(n):return src[n.start:n.end]
 def add(n,value):edits.append((n.end-1,n.end-1,' '+value))
 def extend_decl(n,extra):
  add(n.items[2],' '.join(extra));x=n.items[3].items[1]
  i=next(i for i,v in enumerate(x.items) if sym(v)==':stobjs');add(x.items[i+1],' '.join(extra))
  i=next(i for i,v in enumerate(x.items) if sym(v)==':guard');add(x.items[i+1],' '.join('('+v+'-wfp '+v+')' for v in extra))
 defs={sym(n.items[1]):n for f in p.forms for n in nodes(f) if isinstance(n,lr.Lst) and len(n.items)>3 and sym(n.items[0])=='defun'}
 inc=next(f for f in p.forms if isinstance(f,lr.Lst) and sym(f.items[0])=='include-book')
 edits.append((inc.end,inc.end,'\n(include-book "run-physical-park-region")'))
 release=defs['fn2-read-observer-release'];edits.append((release.start,release.end,helpers))
 enter=defs['fn2-read-observer-enter'];extend_decl(enter,MORE)
 body=text(enter.items[-1]);bp=lr.parse(body);be=[]
 skip=set()
 for f in bp.forms:
  for n in nodes(f):
   if isinstance(n,lr.Lst) and len(n.items)==2 and isinstance(n.items[0],lr.Lst) and sym(n.items[0].items[0])=='mv':
    if any(isinstance(v,lr.Lst) and v.items and sym(v.items[0]) in {'fn2-c-source-reader-acquire','fn2-c-source-reader-acquire-under'} for v in nodes(n.items[1])):skip.add(n.items[0].start)
 for f in bp.forms:
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or not n.items:continue
   if sym(n.items[0])=='mv' and n.start not in skip:be.append((n.end-1,n.end-1,' '+' '.join(PARK)))
   if sym(n.items[0])=='fn2-read-observer-release':be.append((n.end-1,n.end-1,' '+' '.join(MORE)))
 # The first MV binding is a B* binder, which nodes sees as (mv ...), same projection.
 edits.append((enter.items[-1].start,enter.items[-1].end,lr.write(body,be)))
 core={}
 for op in MUT:
  n=defs['fn2-read-'+op];st=n.items[-1];assert sym(st.items[0])=='stobj-let'
  outs=[text(v) for v in st.items[2].items];missing=[v for v in PARK if v not in outs];core[op]=(outs,missing)
  ins=[sym(v.items[0]) for v in st.items[1].items];extra=[v for v in MORE if v not in ins]
  add(st.items[1],' '.join('('+v+' ('+v.replace('fn2-','fn2-core-',1)+' fn2-core))' for v in extra))
  add(st.items[2],' '.join(missing));add(st.items[3],' '.join(extra))
 for op in MUT:
  n=defs['fn2-read-'+op+'-children'];ins=[sym(v) for v in n.items[2].items];extra=[v for v in MORE if v not in ins]
  extend_decl(n,extra);outs,missing=core[op];old=n.items[-1]
  returned=' '.join(outs+missing)
  failure=' '.join(v if v.startswith('fn2-') else '0' for v in outs[1:]+missing)
  if op in {'key','key-octets','release'}:
   assert sym(old.items[0])=='mv-let'
   kernelbind=text(old.items[1]);kernel=text(old.items[2])
   body=f'''(mv-let (closed {' '.join(BASE+PARK)})
 (fn2-read-observer-release x {' '.join(BASE+MORE)})
 (if (eq closed :ok)
  (mv-let {kernelbind} {kernel} (mv {returned}))
  (mv closed {failure})))'''
  else:
   assert sym(old.items[0])=='mv-let';enter_call=text(old.items[2]);enter_call=enter_call[:-1]+' '+' '.join(MORE)+')'
   raw=old.items[3].items[2];assert sym(raw.items[0])=='mv-let'
   body=f'''(mv-let (admitted {' '.join(BASE+PARK)})
 {enter_call}
 (if (eq admitted :ok)
  (mv-let {text(raw.items[1])} {text(raw.items[2])} (mv {returned}))
  (mv admitted {failure})))'''
  edits.append((old.start,old.end,body))
 for f in p.forms:
  if not isinstance(f,lr.Lst) or len(f.items)<3:continue
  head=sym(f.items[0]);name=sym(f.items[1]);op=name.removeprefix('fn2-read-')
  if head=='defcost' and op in MUT:
   i=next(i for i,v in enumerate(f.items) if sym(v)==':tables');tables=f.items[i+1];have=[sym(v) for v in tables.items]
   needed=list(dict.fromkeys(MORE+[v for v in core[op][0][1:] if v.startswith('fn2-')]))
   add(tables,' '.join(v.replace('fn2-','fn2-core-',1) for v in needed if v.replace('fn2-','fn2-core-',1) not in have))
  if head=='fn2-rd-shape' and name in {'fn2-read-observer-release','fn2-read-observer-enter'}:
   add(f.items[2],' '.join(MORE));add(f.items[3],' '.join('('+v+' '+str(i+4)+')' for i,v in enumerate(PARK)));add(f.items[4],' '.join(MORE))
   if name=='fn2-read-observer-release':add(f.items[5],'fn2-read-source-close')
 result=lr.write(src,edits)
 # New helper shape uses the existing generator after it has been defined.
 anchor='(fn2-rd-shape fn2-read-observer-release'
 frames='''(fn2-rd-shape fn2-read-source-close
 (x fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-run-loads 1) (fn2-run-cursors 2) (fn2-checkpoint-summary 3) (fn2-checkpoint-summary-leases 4))
 (fn2-reads fn2-id-decides fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-read-source-owner fn2-run-load-region-park))
'''
 return result.replace(anchor,frames+anchor,1)
if __name__=='__main__':
 import sys
 p=Path(sys.argv[1]);p.write_text(project(p.read_text(),Path('tools/fixtures/read-close-park/helpers.lisp').read_text()))

def project_endpoint_fixture(src):
 """Expand the existing real endpoint fixture for the same readonly/mutable ABI."""
 p=lr.parse(src);edits=[];extra=PARK+['fn2-pool']
 def add(n,x):edits.append((n.end-1,n.end-1,' '+x))
 for f in p.forms:
  if not isinstance(f,lr.Lst) or len(f.items)<2:continue
  if sym(f.items[0])=='defconst' and sym(f.items[1])=='*fn2-rdo-stobjs*':add(f.items[2].node,' '.join(extra))
  if sym(f.items[0])=='defun' and sym(f.items[1]).endswith('-body'):
   add(f.items[2],' '.join(extra));x=f.items[3].items[1];i=next(i for i,v in enumerate(x.items) if sym(v)==':stobjs');add(x.items[i+1],' '.join(extra))
   if any(sym(v)==':guard' for v in x.items):
    i=next(i for i,v in enumerate(x.items) if sym(v)==':guard');add(x.items[i+1],' '.join('('+v+'-wfp '+v+')' for v in extra))
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or not n.items:continue
   h=sym(n.items[0])
   if h in {'fn2-read-observer-enter','fn2-read-observer-release'}:add(n,' '.join(MORE))
   elif h=='fn2-read-key-children':add(n,' '.join(extra))
   elif h.startswith('fn2-rdo-') and h.endswith('-body'):add(n,' '.join(extra))
   if len(n.items)==2 and isinstance(n.items[0],lr.Lst) and sym(n.items[0].items[0])=='mv' and isinstance(n.items[1],lr.Lst) and sym(n.items[1].items[0]) in {'fn2-read-observer-enter','fn2-read-observer-release','fn2-read-key-children'}:add(n.items[0],' '.join(PARK))
   if len(n.items)==2 and sym(n.items[0])=='fn2-c-source-control' and isinstance(n.items[1],lr.Lst) and sym(n.items[1].items[0])=='fn2-c-source-control-init':
    init='''
      (fn2-run-loads (fn2-run-loads-init (+ (fn2-id-decides-rows fn2-id-decides) (* (+ 1 *fn2-b-range-source-cursors*) (fn2-reads-rows fn2-reads))) fn2-run-loads))
      (fn2-run-cursors (fn2-run-cursors-init (fn2-run-loads-rows fn2-run-loads) fn2-run-cursors))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 1 fn2-checkpoint-summary))
      (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init (fn2-run-loads-rows fn2-run-loads) fn2-checkpoint-summary-leases))
      (fn2-pool (fn2-pool-init nil 1 100 fn2-pool))'''
    edits.append((n.end,n.end,init))
 return lr.write(src,edits)
