"""Named physical C projection onto current ROOT; never replace whole books."""
from pathlib import Path
import json
import lisp_rewrite as lr
FIXTURE=Path(__file__).parent/'fixtures/physical-c-root-source.json'
DATA=json.loads(FIXTURE.read_text())
def node(text,head,name):
 found=lr.match('('+head+' '+name+' ?*body)',lr.parse(text).forms,deep=False)
 if len(found)!=1:raise ValueError('one event required '+head+' '+name)
 return found[0].node
def source(text,n):return text[n.start:n.end]
def project_runs(text):
 donor=DATA['donor']['runs'];edits=[]
 for name in ('fn2-run-cursors','fn2-run-paths','fn2-run-installed'):
  a=node(text,'defcolumns',name);b=node(donor,'defcolumns',name)
  if source(text,a)!=source(donor,b):edits.append((a.start,a.end,source(donor,b)))
 for name in ('fn2-run-cursor-start','fn2-run-install','fn2-run-retired-next'):
  a=node(text,'defun',name);b=node(donor,'defun',name)
  # Keep actual ROOT formals/declarations (including qualified guards/hints).
  if source(text,a.items[2])!=source(donor,b.items[2]) or source(text,a.items[3])!=source(donor,b.items[3]):raise ValueError('guard/interface conflict '+name)
  body=source(donor,b.items[4])
  if source(text,a.items[4])!=body:edits.append((a.items[4].start,a.items[4].end,body))
 text=lr.write(text,edits)
 added=[]
 names=('fn2-run-physical-rows-from','fn2-run-physical-count-consistent-p','fn2-run-install-physical','fn2-run-free-physical','fn2-run-cursor-hash-word','fn2-run-path-physical-note','fn2-run-cursor-parent-ref','fn2-run-ref-hash-word','fn2-run-cursor-copy-ref-hash','fn2-run-cursor-child-ref','fn2-run-cursor-start-installed')
 for form in lr.parse(donor).forms:
  if not isinstance(form,lr.Lst) or len(form.items)<2:continue
  head=getattr(form.items[0],'low','');name=getattr(form.items[1],'low','')
  if name in names and head in ('defun','fn2-run-installed-preserves','fn2-run-paths-preserves','fn2-run-cursors-preserves'):
   matches=lr.match('('+head+' '+name+' ?*body)',lr.parse(text).forms,deep=False)
   if matches:
    if source(text,matches[0].node)!=source(donor,form):raise ValueError('existing projected event changed '+name)
   else:added.append(source(donor,form))
 return text+('' if not added else '\n; FullRef physical source constructors and cursor/path identity.\n'+'\n'.join(added)+'\n')

def project_range(text):
 donor=DATA['donor']['range'];name='fn2-range-advance-run'
 # This defun is generated inside the existing event factory. Keep all ROOT
 # declarations and theorem hints; update only the actual start/entry paths.
 a=lr.match('(defun '+name+' ?*body)',lr.parse(text).forms,deep=True)
 b=lr.match('(defun '+name+' ?*body)',lr.parse(donor).forms,deep=True)
 if len(a)!=1 or len(b)!=1:raise ValueError('one actual generated range advance')
 old=a[0].node;new=b[0].node;edits=[]
 # Donor body has the same guarded inputs/outputs, with exact physical root.
 if source(text,old.items[2])!=source(donor,new.items[2]):raise ValueError('range ABI changed')
 edits.append((old.items[4].start,old.items[4].end,source(donor,new.items[4])))
 text=lr.write(text,edits)
 # Preserve current ROOT guard hints and call-guard theorem hooks verbatim
 # except the callee symbol that the new actual body invokes.
 return text.replace('fn2-run-cursor-start ', 'fn2-run-cursor-start-installed ')

def project_machines(text):
 donor=DATA['donor']['machines-c'];edits=[]
 # Add only loader/cut/observer prerequisites, not old successor field geometry.
 books=('c-snapshot','checkpoint-summary-state','run-physical-geometry','run-physical-harvest','c-source-observer')
 anchor=node(text,'include-book','"machines-b"')
 additions=['(include-book "'+b+'")' for b in books if not lr.match('(include-book "'+b+'")',lr.parse(text).forms,deep=False)]
 if additions:edits.append((anchor.end,anchor.end,'\n'+'\n'.join(additions)))
 text=lr.write(text,edits)
 # Endpoint geometry is part of the actual observer children, no host identity.
 names=('fn2-c-source-endpoint-rows','fn2-c-source-successor-endpoint','fn2-c-source-sealer-endpoint','fn2-c-source-request-endpoint','fn2-c-source-cns-endpoint')
 additions=[]
 for name in names:
  if not lr.match('(defun '+name+' ?*body)',lr.parse(text).forms,deep=False):additions.append(source(donor,node(donor,'defun',name)))
 if not lr.match('(defthm fn2-c-source-endpoint-rows-natp ?*body)',lr.parse(text).forms,deep=False):additions.append(source(donor,node(donor,'defthm','fn2-c-source-endpoint-rows-natp')))
 anchor=node(text,'defun','fn2-idc-profilep')
 if additions:text=lr.write(text,[(anchor.start,anchor.start,'\n'.join(additions)+'\n')])
 # Profile carries current ROOT conditions plus the actual new child bounds.
 a=node(text,'defun','fn2-idc-profilep');body=a.items[4];src=source(text,body)
 more=['(unsigned-byte-p 32 (fn2-c-source-endpoint-rows profile))','(unsigned-byte-p 32 (fn2-b-run-cursor-rows profile))','(unsigned-byte-p 32 (* *fn2-run-max-levels* (fn2-b-run-cursor-rows profile)))','(unsigned-byte-p 32 (+ (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile)))']
 missing=[x for x in more if x not in src]
 if missing:text=lr.write(text,[(body.end-1,body.end-1,'\n      '+'\n      '.join(missing))])
 # Existing resident cursor geometry is replaced by shared current helper.
 replacements={
 'fn2-core-run-installed':'(+ (fn2-b-capacity :identity-runs 64 profile) (fn2-b-capacity :extent-slots 16 profile))',
 'fn2-core-run-cursors':'(fn2-b-run-cursor-rows profile)',
 'fn2-core-run-paths':'(* *fn2-run-max-levels* (fn2-b-run-cursor-rows profile))'}
 edits=[]
 for name,expr in replacements.items():
  a=node(text,'fn2-idc-child',name);init=a.items[3];arg=init.items[1]
  if source(text,arg)!=expr:edits.append((arg.start,arg.end,expr))
 text=lr.write(text,edits)
 childnames=('fn2-core-c-source-control','fn2-core-c-source-readers','fn2-core-csnapshot','fn2-core-checkpoint-summary-leases','fn2-core-run-loads','fn2-core-run-load-ops','fn2-core-run-load-geometry','fn2-core-run-load-readiness')
 additions=[]
 for f in lr.parse(donor).forms:
  if not isinstance(f,lr.Lst) or len(f.items)<2:continue
  head=getattr(f.items[0],'low','');name=getattr(f.items[1],'low','')
  if name in childnames and head in ('fn2-idc-child','defcorechild') and not lr.match('('+head+' '+name+' ?*body)',lr.parse(text).forms,deep=False):additions.append(source(donor,f))
 # Register before following core consumers and physical operation costs.
 anchor=node(text,'fn2-idc-child','fn2-core-run-cache')
 if additions:text=lr.write(text,[(anchor.start,anchor.start,'\n'.join(additions)+'\n')])
 tail=donor[donor.index('(include-book "run-physical-step")'):]
 if '(defcost fn2-run-page-reserve ' not in text:text+='\n'+tail
 return text


def project_run_cursor_paths(text):
 donor=DATA['donor']['runs-assemble'];edits=[]
 # SAME actual generated cursor algorithm, preserving all current ROOT guards,
 # selected disables and carried call-guard theorem hooks around its body.
 for name in ('fn2-run-step-header','fn2-run-step-seek','fn2-run-step-child','fn2-run-step-up','fn2-run-cursor-step'):
  aa=lr.match('(defun '+name+' ?*body)',lr.parse(text).forms,deep=True)
  bb=lr.match('(defun '+name+' ?*body)',lr.parse(donor).forms,deep=True)
  if len(aa)!=1 or len(bb)!=1:raise ValueError('one cursor function '+name)
  a=aa[0].node;b=bb[0].node
  if source(text,a.items[2])!=source(donor,b.items[2]):raise ValueError('cursor ABI conflict '+name)
  body=source(donor,b.items[4])
  if source(text,a.items[4])!=body:edits.append((a.items[4].start,a.items[4].end,body))
 return lr.write(text,edits)

def _key(f):
 if isinstance(f,lr.Lst) and len(f.items)>1:return getattr(f.items[0],'low',''),getattr(f.items[1],'low','')
 return None

def _function_projection(oldtext,a,donortext,b):
 # Actual old guards/hints remain. New readonly/mutable stobjs are explicit;
 # append the donor guard conjuncts instead of deleting ROOT guard premises.
 edits=[(a.items[2].start,a.items[2].end,source(donortext,b.items[2])),(a.items[-1].start,a.items[-1].end,source(donortext,b.items[-1]))]
 olddecl=a.items[3];newdecl=b.items[3]
 for key in (':stobjs',':guard'):
  def value(d):
   for m in lr.match('(xargs ?*args)',[d],deep=True):
    xs=m.captures['args']
    for i,x in enumerate(xs[:-1]):
     if getattr(x,'low','')==key:return xs[i+1]
   return None
  ov=value(olddecl);nv=value(newdecl)
  if ov is None or nv is None:raise ValueError('explicit '+key+' required '+getattr(a.items[1],'low',''))
  old=source(oldtext,ov);new=source(donortext,nv)
  if old==new:continue
  if key==':stobjs':replacement=new
  elif old=='t':replacement=new
  elif new=='t' or new in old:replacement=old
  else:replacement='(and '+old+' '+new+')'
  edits.append((ov.start,ov.end,replacement))
 return lr.write(oldtext,edits)

def _project_events(text,book,keys):
 donor=DATA['donor'][book]
 # Existing named runtime functions retain declarations, actual guard hints,
 # and theorem hooks. Interface/shape/event factories are named projections.
 for key in keys:
  head,name=key
  aa=[x for x in lr.parse(text).forms if _key(x)==key]
  bb=[x for x in lr.parse(donor).forms if _key(x)==key]
  if len(bb)!=1:raise ValueError('one donor event '+str(key))
  if not aa:continue
  if len(aa)!=1:raise ValueError('one current event '+str(key))
  a=aa[0];b=bb[0]
  if source(text,a)==source(donor,b):continue
  if head=='defun':text=_function_projection(text,a,donor,b)
  else:text=lr.write(text,[(a.start,a.end,source(donor,b))])
 # Insert new events adjacent to their next existing donor anchor, so raw
 # implementations precede wrappers and helper definitions precede callers.
 pending=[];edits=[];present={_key(x) for x in lr.parse(text).forms}
 for f in lr.parse(donor).forms:
  k=_key(f)
  if k in keys and k not in present:pending.append(source(donor,f));continue
  if pending and k in present:
   anchors=[x for x in lr.parse(text).forms if _key(x)==k]
   if len(anchors)==1:edits.append((anchors[0].start,anchors[0].start,'\n'.join(pending)+'\n'));pending=[]
 if pending:edits.append((len(text),len(text),'\n'+'\n'.join(pending)+'\n'))
 return lr.write(text,edits)

def join_keys(book):
 donor=DATA['donor'][book];before=DATA['before'][book]
 old={_key(x):source(before,x) for x in lr.parse(before).forms if _key(x)}
 result=[]
 for f in lr.parse(donor).forms:
  key=_key(f)
  if not key:continue
  head,name=key
  if key in old and old[key]==source(donor,f):continue
  allowed=False
  if book=='machines-c-successor':
   allowed=(name=='fn2-succ-txns' or name in ('fn2-succ-resolve-next','fn2-succ-resolve-step','fn2-succ-resolve','fn2-succ-resolve-raw','fn2-succ-clear-ref-rows','fn2-succ-copy-scalar-row','fn2-succ-copy-scalar-rows','fn2-succ-source-values-scalar-p','fn2-succ-source-acquire','fn2-succ-source-close','fn2-succ-resolve-observed'))
   allowed=allowed or (head=='include-book' and name=='"run-physical-park-region"')
  elif book=='machines-c-bind':allowed=name in ('fn2-succ-release','fn2-succ-release-observed','fn2-successor-resolve','fn2-successor-stage','fn2-successor-release','fn2-successor-prepare-events','fn2-successor-commit-events')
  elif book=='machines-c-groups':allowed=name in ('fn2-xl-run-next','fn2-xl-step','fn2-id-decide-start','fn2-group-lookup','fn2-principal-lookup','fn2-directory-source-core-definition','fn2-groups-core-events','fn2-identity-decide','fn2-identity-core-events')
  elif book=='machines-c-read':allowed=(head in ('defun','defcost','defmacro','defcolumns','fn2-rd-shape','include-book'))
  elif book=='machines-c-stage':allowed=name in ('fn2-succ-clear-stage-refs','fn2-succ-stage-raw','fn2-succ-stage')
  if allowed:result.append(key)
 return result

def project_join(text,book):
 if book=='machines-c-stage' and not lr.match('(defun fn2-succ-stage-raw ?*body)',lr.parse(text).forms,deep=False):
  # Keep the actual current stage algorithm/guard as raw; only public cleanup
  # is added. Rename the exact existing theorem invocation alongside it.
  edits=[]
  for head in ('defun','fn2-idc-fn-shape'):
   a=node(text,head,'fn2-succ-stage');name=a.items[1]
   edits.append((name.start,name.end,'fn2-succ-stage-raw'))
  text=lr.write(text,edits)
 return _project_events(text,book,join_keys(book))

def project_c_workspace(text,book):
 if book=='machines-c':
  anchor=node(text,'include-book','"machines-b"')
  if '(include-book "successor-schema-geometry")' not in text:text=lr.write(text,[(anchor.end,anchor.end,'\n(include-book "successor-schema-geometry")')])
  a=lr.match('(defconst *fn2-succ-block* ?value)',lr.parse(text).forms,deep=False)
  if a:text=lr.write(text,[(a[0].node.start,a[0].node.end,'; Successor offsets/capacities are declared once from actual schemas.')])
  if '(defconst *fn2-idc-required-fields* ' not in text:
   a=node(text,'defconst','*fn2-idc-rb*')
   addition='\n(defconst *fn2-idc-required-fields* (fn2-successor-required-fields *fn2-succ-fields-max* *fn2-succ-values-max* *fn2-succ-slots* *fn2-run-entry-rows* *fn2-run-reader-fields*))\n(assert-event (<= *fn2-idc-required-fields* *fn2-idc-stride*))'
   text=lr.write(text,[(a.end,a.end,addition)])
  # Current B field floor includes its checkpoint stripe. Preserve actual
  # ROOT 2048 transaction stripe and every other geometry contribution.
  old='(* 3 *fn2-idc-stride*) *fn2-b-seal-field-rows*))))'
  new='(* 3 *fn2-idc-stride*) *fn2-b-seal-field-rows* *fn2-b-checkpoint-field-rows*))))'
  text=text.replace(old,new)
 elif book=='machines-c-successor':
  edits=[]
  for name in ('*fn2-idc-scratch-bytes*','*fn2-succ-entry*','*fn2-succ-raw*','*fn2-succ-eval*','*fn2-succ-res*','*fn2-succ-fresh*','*fn2-succ-fields-max*','*fn2-succ-values-max*'):
   m=lr.match('(defconst '+name+' ?value)',lr.parse(text).forms,deep=False)
   if m:edits.append((m[0].node.start,m[0].node.end,'; '+name+' comes from successor-schema-geometry.'))
  m=lr.match('(defun fn2-succ-octets-total ?*body)',lr.parse(text).forms,deep=False)
  if m:edits.append((m[0].node.start,m[0].node.end,'; Shared schema inventory owns fn2-succ-octets-total.'))
  text=lr.write(text,edits)
 return text

if __name__=='__main__':
 for name,fn in (('runs',project_runs),('range',project_range),('machines-c',lambda x:project_c_workspace(project_machines(x),'machines-c')),('runs-assemble',project_run_cursor_paths)):
  p=Path(__file__).resolve().parents[1]/'books'/(name+'.lisp');text=p.read_text();p.write_text(fn(text))
 for name in ('machines-c-successor','machines-c-bind','machines-c-groups','machines-c-stage','machines-c-read'):
  p=Path(__file__).resolve().parents[1]/'books'/(name+'.lisp');text=p.read_text();p.write_text(project_c_workspace(project_join(text,name),name))
