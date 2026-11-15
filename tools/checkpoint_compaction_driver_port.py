"""Named actual ROOT1 driver migration; lower calls use current actual defun ABIs.

Frozen ordered-source input is preserved for exact source/negative controls.
This is a source transformation, not a second runtime driver.
"""
from pathlib import Path
import sys,re
sys.path.insert(0,'tools');import lisp_rewrite as lr
root=Path('books');p=root/'checkpoint-metadata-driver.lisp';s=Path('tools/fixtures/checkpoint-compaction/driver-before.lisp').read_text()
# Source calls use actual defun formal lists; no invented lower callback ABI.
def fn(name):
 for f in root.glob('*.lisp'):
  t=f.read_text()
  if '(defun '+name+'\n' in t or '(defun '+name+' ' in t:
   hits=lr.match('(defun '+name+' ?*body)',lr.parse(t).forms,deep=True)
   if hits:return hits[0].node
 raise ValueError(name)
def args(name):return [lr.emit(x,drop_comments=True) for x in fn(name).items[2].items]
def call(name,**kw):return '('+name+' '+' '.join(kw.get(a,a) for a in args(name))+')'
def binding(name,outputs,**kw):return '((mv code '+outputs+') '+call(name,**kw)+')'
def replace(name,text):
 global s
 forms=lr.parse(s).forms;hs=lr.match('(fn2-checkpoint-root1-operation '+name+' ?*body)',forms,deep=True)
 assert len(hs)==1,name
 n=hs[0].node;s=lr.write(s,[(n.start,n.end,text)])
C='fn2-checkpoint-compaction';P='fn2-checkpoint-predecessors';PC='fn2-checkpoint-predecessor-control'
common=C+' fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed '+P+' '+PC
out=C+' fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool'
merge=C+' fn2-run-cursors fn2-run-paths fn2-fields fn2-pool'
park=C+' fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases'
def ret(expr='code'):return '(fn2-checkpoint-root1-mv '+expr+')'
def op(name,body,scalar='budget kind owner gen'):return '(fn2-checkpoint-root1-operation fn2-checkpoint-root1-'+name+' ('+scalar+')\n '+body+')'
def branch(ph,name,outs,extra='',**kw):return '((equal phase *fn2-checkpoint-compaction-phase-'+ph+'*)\n (b* ('+binding(name,outs,**kw)+extra+') '+ret("(if (member-eq code '(:empty-end :retention-required)) :more code)")+'))'
owner='(fn2-checkpoint-root1-ownerp (fn2-checkpoint-root1-token 0 fn2-checkpoint-root1) kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot)'
# Add actual dependencies before macro expansion; no operational reader twin.
s=s.replace('(include-book "checkpoint-source-loader")','(include-book "checkpoint-source-loader")\n(include-book "checkpoint-compaction-schema")\n(include-book "checkpoint-compaction-empty")\n(include-book "checkpoint-compaction-park")\n(include-book "checkpoint-compaction-reader-finish")\n(include-book "checkpoint-bank-admission")')
s=re.sub(r'(?<![\w-])fn2-checkpoint-source(?![\w-])',C,s)
# All children remain inputs. Inventory control and bank receipt are readonly in STEP.
s=s.replace('fn2-checkpoint-summary-leases))','fn2-checkpoint-summary-leases '+P+' '+PC+' fn2-checkpoint-bank-admission))',1)
# Small inventory family is the only control mutator.
inv='''(b* (((unless (and (posp budget) OWNER)) (fn2-checkpoint-root1-mv :owner))
 (phase (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control)))
 (cond
 ((equal phase *fn2-checkpoint-predecessor-phase-capture*)
  (b* (CAPTURE) (fn2-checkpoint-root1-mv (if (eq code :captured) :more code))))
 ((equal phase *fn2-checkpoint-predecessor-phase-empty*)
  (b* (EMPTY
       (fn2-checkpoint-root1 (if (eq code :source) (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-source* fn2-checkpoint-root1) fn2-checkpoint-root1)))
   (fn2-checkpoint-root1-mv (if (member-eq code '(:source :ready)) :more code))))
 ((member phase (list *fn2-checkpoint-predecessor-phase-ready* *fn2-checkpoint-predecessor-phase-checking*))
  (b* (CHECK) (fn2-checkpoint-root1-mv (if (eq code :complete) :more code))))
 (t (fn2-checkpoint-root1-mv :state))))'''.replace('OWNER',owner)
inv=inv.replace('CAPTURE',binding('fn2-checkpoint-predecessor-capture-step',P+' '+PC)).replace('EMPTY',binding('fn2-checkpoint-predecessor-empty-next',C+' '+PC)).replace('CHECK',binding('fn2-checkpoint-predecessor-complete-step',PC))
# Separate control operation must not be selected during active source work.
inv=inv.replace('(posp budget) '+owner,'(posp budget) '+owner+' (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-select*)')
# Begin, retaining canonical directory/start work.
beg=lr.match('(fn2-checkpoint-root1-operation fn2-checkpoint-root1-begin ?*body)',lr.parse(s).forms,deep=True)[0].node
bt=s[beg.start:beg.end]
a=bt.index('      ((mv code '+C+')');b=bt.index('      (crow ',a)
bt=bt[:a]+'      '+binding('fn2-checkpoint-compaction-begin',C,generation='gen')+'\n      ((unless (eq code :more)) '+ret()+')\n'+bt[b:]
bt=bt.replace('(fn2-checkpoint-build-ownerp token kind owner gen fn2-checkpoint-build fn2-csnapshot)', '(and (fn2-checkpoint-build-ownerp token kind owner gen fn2-checkpoint-build fn2-csnapshot)\n (fn2-checkpoint-bank-admission-ready-p token kind owner gen fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission))')
# manifest begin now has readonly overlays/installed appended
name='fn2-checkpoint-metadata-manifest-begin';node=lr.match('('+name+' ?*args)',lr.parse(bt).forms,deep=True)[0].node
bt=lr.write(bt,[(node.end-1,node.end-1,' fn2-overlays fn2-run-installed')])
needle='  (fn2-checkpoint-root1-mv (if (eq code :ok) :more code))))'
assert bt.endswith(needle)
bt=bt[:-len(needle)].rstrip()[:-1]+'\n'+'''      ((unless (eq code :ok)) (fn2-checkpoint-root1-mv code))
      CONFIG
      ((unless (eq code :ok)) (fn2-checkpoint-root1-mv code))
      BEGIN)
  (fn2-checkpoint-root1-mv code)))'''.replace('CONFIG',binding('fn2-checkpoint-compaction-configure',C)).replace('BEGIN',binding('fn2-checkpoint-predecessor-begin',PC))
replace('fn2-checkpoint-root1-begin',bt)
select='''(b* (((unless (and (posp budget) OWNER
 (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-select*))) (fn2-checkpoint-root1-mv :owner))
 ((unless (fn2-checkpoint-predecessor-ready-p COMMON))
  (if (and (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-done*)
           (fn2-checkpoint-predecessor-complete-p COMMON))
   (let ((fn2-checkpoint-root1 (fn2-checkpoint-root1-put 0 (build *fn2-checkpoint-manifest-build*) (phase *fn2-checkpoint-root1-phase-finish*)))) (fn2-checkpoint-root1-mv :more))
   (fn2-checkpoint-root1-mv :inventory)))
 (phase (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction)))
 (cond
 ((equal phase *fn2-checkpoint-compaction-phase-done*) (fn2-checkpoint-root1-mv :inventory))
 ((equal phase *fn2-checkpoint-compaction-phase-schema*)
  (b* (SCAN) (fn2-checkpoint-root1-mv (if (member-eq code '(:schema :done)) :more code))))
 ((equal phase *fn2-checkpoint-compaction-phase-sources*)
  (b* (START
       (fn2-checkpoint-root1 (if (eq code :more) (fn2-checkpoint-root1-put 0 (build *fn2-checkpoint-source-build*) (phase *fn2-checkpoint-root1-phase-source*)) fn2-checkpoint-root1)))
   (fn2-checkpoint-root1-mv code)))
 (t (fn2-checkpoint-root1-mv :state))))'''.replace('OWNER',owner).replace('COMMON',common).replace('SCAN',binding('fn2-checkpoint-compaction-source-step',C)).replace('START',binding('fn2-checkpoint-compaction-schema-begin',out))
replace('fn2-checkpoint-root1-select',op('select',select))
# Dispatch one actual decoded-source transition. Physical IO stays READ.
source='(b* (((unless (and (posp budget) '+owner+')) '+ret(':owner')+')\n (phase (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction)))\n (cond\n'
readerouts='fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests'
source+='''((and (member phase (list *fn2-checkpoint-compaction-phase-seek* *fn2-checkpoint-compaction-phase-empty-seek*))
 (< (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) (fn2-run-cursors-rows fn2-run-cursors))
 (equal (fn2-checkpoint-compaction-source-started 0 fn2-checkpoint-compaction) 1)
 (equal (fn2-run-cursors-physical (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) fn2-run-cursors) 1)
 (equal (fn2-run-cursors-phase (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) fn2-run-cursors) *fn2-run-cursor-phase-miss*))
 (b* (READ (fn2-checkpoint-root1 (if (eq code :need-read) (fn2-checkpoint-root1-set-read-kind 0 3 fn2-checkpoint-root1) fn2-checkpoint-root1))) (fn2-checkpoint-root1-mv (if (eq code :ok) :more code))))
'''.replace('READ',binding('fn2-checkpoint-compaction-reader-step',readerouts,budget='(min budget 4096)'))
source+=branch('empty-seek','fn2-checkpoint-compaction-empty-step',merge,budget='(min budget 4096)').replace("(if (member-eq code '(:empty-end :retention-required)) :more code)", "(if (or (eq code :empty-end) (and (eq code :miss) (< (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) (fn2-run-cursors-rows fn2-run-cursors)) (equal (fn2-run-cursors-physical (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) fn2-run-cursors) 1) (equal (fn2-run-cursors-phase (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) fn2-run-cursors) *fn2-run-cursor-phase-miss*))) :more code)")+'\n'
for ph,name,outs in [('empty-end','fn2-checkpoint-predecessor-empty-end',C+' '+P),('equal-lower','fn2-checkpoint-predecessor-source-key',C+' '+P),('source-end','fn2-checkpoint-predecessor-source-end',C+' '+P)]:source+=branch(ph,name,outs)+'\n'
source+=branch('park','fn2-checkpoint-compaction-park-source',park,extra='\n(fn2-checkpoint-root1 (if (and (eq code :more) (equal (fn2-checkpoint-compaction-schema-open 0 fn2-checkpoint-compaction) 0)) (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-select* fn2-checkpoint-root1) fn2-checkpoint-root1))')+'\n'
source+=branch('sources','fn2-checkpoint-compaction-source-step',C).replace(":empty-end :retention-required", ":source :scan-complete")+'\n' 
source+='((member phase (list *fn2-checkpoint-compaction-phase-seek* *fn2-checkpoint-compaction-phase-compare* *fn2-checkpoint-compaction-phase-copy*)) (b* ('+binding('fn2-checkpoint-compaction-merge-step',merge,budget='(min budget 4096)')+') '+ret("(if (or (member-eq code '(:source-key :source-end :selected)) (and (eq code :miss) (< (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) (fn2-run-cursors-rows fn2-run-cursors)) (equal (fn2-run-cursors-physical (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) fn2-run-cursors) 1) (equal (fn2-run-cursors-phase (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) fn2-run-cursors) *fn2-run-cursor-phase-miss*))) :more code)")+'))\n'
source+=branch('selected','fn2-checkpoint-compaction-selected-bind',out,extra='\n(fn2-checkpoint-root1 (if (eq code :retention-required) (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-retention* fn2-checkpoint-root1) fn2-checkpoint-root1))')+'\n'
source+='((member phase (list *fn2-checkpoint-compaction-phase-retention* *fn2-checkpoint-compaction-phase-append*)) (b* ('+binding('fn2-checkpoint-compaction-append-step',out,budget='(min budget 4096)')+') '+ret('(if (eq code :need-page) :more code)')+'))\n'
source+=branch('lower-copy','fn2-checkpoint-compaction-lower-step',out,budget='(min budget 4096)')+'\n'+branch('schema-done','fn2-checkpoint-compaction-schema-finish',out).replace(":empty-end :retention-required", ":ok")+'\n(t '+ret(':state')+')))'
# Insert before WORK so generated call target exists at admission.
idx=s.index('; Formatting and promotion')
s=s[:idx]+op('inventory',inv)+'\n\n'+op('source',source)+'\n\n'+s[idx:]
# Work source branch delegates same family, preserving page work first.
forms=lr.parse(s).forms;n=lr.match('(fn2-checkpoint-root1-operation fn2-checkpoint-root1-work ?*body)',forms,deep=True)[0].node
wt=s[n.start:n.end];a=wt.index('   ((equal phase *fn2-checkpoint-root1-phase-source*)');b=wt.index('   ((equal phase *fn2-checkpoint-root1-phase-manifest*)',a)
wt=wt[:a]+'   ((equal phase *fn2-checkpoint-root1-phase-source*) (fn2-checkpoint-root1-call fn2-checkpoint-root1-source budget kind owner gen))\n'+wt[b:]
replace('fn2-checkpoint-root1-work',wt)
# Every migrated manifest call uses its ACTUAL formal tail; preserve scalar args for BEGIN handled above.
for name in ['emit','finish','scan-begin','scan-step']:
 full='fn2-checkpoint-metadata-manifest-'+name;nodes=lr.match('('+full+' ?*args)',lr.parse(s).forms,deep=True)
 s=lr.write(s,[(h.node.start,h.node.end,call(full)) for h in nodes])
# Mutating EMIT return changed source→compaction already via symbol replacement.
# Actual source READ canonical lower issue.
name='fn2-checkpoint-source-reader-issue';hs=lr.match('('+name+' ?*args)',lr.parse(s).forms,deep=True);assert len(hs)==1
n=hs[0].node;s=lr.write(s,[(n.start,n.end,call('fn2-checkpoint-compaction-reader-issue'))])
# Finish must bind new lower completion constructor, never old ordered DONE.
name='fn2-checkpoint-source-reader-finish';hs=lr.match('('+name+' ?*args)',lr.parse(s).forms,deep=True);assert len(hs)==1
n=hs[0].node;s=lr.write(s,[(n.start,n.end,call('fn2-checkpoint-compaction-reader-finish',token='(fn2-checkpoint-root1-token 0 fn2-checkpoint-root1)'))])
# Empty prepass has no builder. Dispatch directly rather than guessing build state.
needle='''((member phase (list *fn2-checkpoint-root1-phase-source* *fn2-checkpoint-root1-phase-manifest* *fn2-checkpoint-root1-phase-finish*))'''
s=s.replace(needle,'''((and (equal phase *fn2-checkpoint-root1-phase-source*) (equal (fn2-checkpoint-compaction-schema-open 0 fn2-checkpoint-compaction) 0))
    (fn2-checkpoint-root1-call fn2-checkpoint-root1-source budget kind owner gen))
   '''+needle,1)
# BEGIN control write, SELECT schema builder writes fields/restarts, SOURCE hooks write predecessors.
# Declaration is exact mutating union, no readonly input dropped.
node=lr.match('(defconst *fn2-checkpoint-root1-outputs* ?*rest)',lr.parse(s).forms,deep=True)[0].node
text=s[node.start:node.end]
rows={}
for row in lr.parse(text).forms[0].items[2].node.items:
 vals=[lr.emit(x,drop_comments=True) for x in row.items];rows[vals[0]]=vals[1:]
def extend(n,items):
 for i in items.split():
  if i not in rows[n]:rows[n].append(i)
extend('fn2-checkpoint-root1-begin',PC)
extend('fn2-checkpoint-root1-select','fn2-run-restarts fn2-fields')
rows['fn2-checkpoint-root1-inventory']=['fn2-checkpoint-root1',C,P,PC]
rows['fn2-checkpoint-root1-source']=['fn2-checkpoint-root1',C,P,'fn2-checkpoint-metadata','fn2-run-builds','fn2-run-writers','fn2-run-restarts','fn2-run-cursors','fn2-run-paths','fn2-fields','fn2-pool','fn2-run-loads','fn2-checkpoint-summary','fn2-checkpoint-summary-leases','fn2-fc','fn2-fc-context','fn2-b3','fn2-digests']
for nm in ['fn2-checkpoint-root1-work','fn2-checkpoint-root1-step']:extend(nm,P)
# Step mutating outputs encompass every family (except separately controlled inventory).
for nm in ['fn2-checkpoint-root1-select','fn2-checkpoint-root1-source','fn2-checkpoint-root1-work','fn2-checkpoint-root1-retention','fn2-checkpoint-root1-payload-start','fn2-checkpoint-root1-closure']:extend('fn2-checkpoint-root1-step',' '.join(rows[nm]))
for k,v in rows.items():assert len(v)+(3 if k.endswith('-read') else 1)<=32,(k,len(v))
new="(defconst *fn2-checkpoint-root1-outputs*\n '("+'\n   '.join('('+k+' '+' '.join(v)+')' for k,v in rows.items())+'))'
s=lr.write(s,[(node.start,node.end,new)])
lr.parse(s)
EXPECTED=s
COUNTS={k:len(v)+(3 if k.endswith('-read') else 1) for k,v in rows.items()}
def validate(text):
 if text!=EXPECTED:raise ValueError('actual driver differs from named compaction projection')
 return COUNTS
if __name__=='__main__':
 if '--apply' in sys.argv:p.write_text(EXPECTED)
 else:validate(p.read_text())
 print(COUNTS)
