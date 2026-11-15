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

if __name__=='__main__':
 for name,fn in (('runs',project_runs),('range',project_range),('machines-c',project_machines)):
  p=Path(__file__).resolve().parents[1]/'books'/(name+'.lisp');p.write_text(fn(p.read_text()))
