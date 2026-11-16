"""Named actual MASTER join: sealer request, bounded inventory, checked wake.

Only MASTER leaves and the named late materialization boundary are projected.
Canonical B coordinator, commit/recovery implementations and activation stay put.
"""
from pathlib import Path
import json
import lisp_rewrite as lr
import replacement_bank_master_rewrite as bank
ROOT=Path(__file__).resolve().parents[1]
FIX=ROOT/'tools/fixtures/master-request-join'
BEFORE=json.loads((FIX/'bank-before.json').read_text())['before']
def one(s,pattern):return bank.event(s,pattern)
def once(s,a,b):return bank.once(s,a,b)
def pressure_leaf(donor):
 fn=one(donor,'(defun fn2-checkpoint-master-pressure-children ?*body)')
 cost=one(donor,'(defcost fn2-checkpoint-master-pressure-op ?*body)')
 s=donor[fn.start:fn.end]+'\n'+donor[cost.start:cost.end]+'\n'
 s=once(s,'(seen fn2-checkpoint-root1','(seen requested fn2-checkpoint-root1')
 s=once(s,'(unsigned-byte-p 60 seen))))','(unsigned-byte-p 60 seen) (booleanp requested))))')
 s=once(s,'''       (< 0 (fn2-alloc-blocked fn2-extents))
       (< seen (fn2-alloc-last-retirement fn2-extents))''','''       ; REQUESTED is only a validated scheduling hint, never HELD authority.
       (or (and (< 0 (fn2-alloc-blocked fn2-extents))
                (< seen (fn2-alloc-last-retirement fn2-extents))) requested)''')
 s=once(s,'Report actual retirement debt with cached bundle and directory hints;',
          'Report actual retirement debt or internal source-compaction request under common resource gates;')
 return '''; SAME actual pressure implementation, extracted to keep late kind tags out
; of the lower resource leaf. A requested hint bypasses only the debt trigger.
(in-package "ACL2")
(include-book "checkpoint-master-abort")
(fn2-book-layer :c)
'''+s

def project_control(donor):
 fn=one(donor,'(defun fn2-checkpoint-master-pressure-children ?*body)')
 cost=one(donor,'(defcost fn2-checkpoint-master-pressure-op ?*body)')
 s=lr.write(donor,[(fn.start,fn.end,''),(cost.start,cost.end,'')])
 return once(s,'(in-package "ACL2")','(in-package "ACL2")\n(include-book "checkpoint-master-pressure")')

def project_state(s):
 s=bank.project_state(s)
 machine=one(s,'(defmachine fn2-checkpoint-master ?*body)');edits=[]
 for i,n in enumerate(machine.items):
  key=lr.emit(n,drop_comments=True)
  if key==':states':a=machine.items[i+1];edits.append((a.end-1,a.end-1,' :root1-inventory :sealer-resume-wake'))
  elif key==':arms':a=machine.items[i+1];edits.append((a.end-1,a.end-1,' (:root1-inventory) (:sealer-resume-wake)'))
  elif key==':holds':a=machine.items[i+1];edits.append((a.end-1,a.end-1,' (:root1-inventory :storage-window :storage-window)'))
 assert len(edits)==3
 return lr.write(s,edits)

INVENTORY='''
  ; Control mutation is separate from STEP's32-value carrier projection.
  (:root1-inventory :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-root1-inventory-op *fn2-checkpoint-master-pure-byte-quantum* *fn2-checkpoint-master-kind* id row-generation)
    :accept () :case
    (((:more) (:next :root1-source) (:charge :bytes *fn2-checkpoint-root1-turn-bytes* :steps *fn2-work-stage* :runnable t))
     ((:yield) (:yield))
     ((:wait) (:wait :completion :steps *fn2-work-small*))
     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
'''
WAKE='''
  ; This turn is after real typed reopen/rearm and C snapshot release. A
  ; checked wake target is a notification, not an adoption completion flag.
  (:sealer-resume-wake :on-refusal ((:stop :checkpoint) (:charge :steps *fn2-work-small*))
   (:do (code target) (fn2-sealer-checkpoint-wake-target) :accept (:ok :absent))
   (:if (not (= target *fn2-none*)) ((:wake-row target)) ())
   (:next :teardown-transfer-begin) (:charge :steps *fn2-work-stage* :runnable t))
'''
def project_arms(s):
 s=bank.project_arms(s)
 idle=one(s,'(:idle :on-refusal ?*body)');t=s[idle.start:idle.end]
 t=once(t,'((:do (code needed retirement) (fn2-checkpoint-master-pressure-op row-retirement-seen))',
 '''((:do (notify requested) (fn2-sealer-checkpoint-pending-op) :accept (:ok))
       (:do (code needed retirement) (fn2-checkpoint-master-pressure-op row-retirement-seen (if requested t nil)))''')
 s=lr.write(s,[(idle.start,idle.end,t)])
 src=one(s,'(:root1-source :on-refusal ?*body)');t=s[src.start:src.end]
 t=once(t,'     ((:page)', '''     ((:inventory) (:next :root1-inventory) (:charge :bytes *fn2-checkpoint-root1-turn-bytes* :steps *fn2-work-stage* :runnable t))
     ((:page)''')
 s=lr.write(s,[(src.start,src.end,t)])
 read=one(s,'(:root1-read :on-refusal ?*body)');s=lr.write(s,[(read.start,read.start,INVENTORY)])
 release=one(s,'(:snapshot-release :on-refusal ?*body)');t=s[release.start:release.end]
 t=once(t,'(:next :teardown-transfer-begin)','(:next :sealer-resume-wake)')
 return lr.write(s,[(release.start,release.end,t+'\n'+WAKE)])

def project_events(s):
 # Existing ready/grant wait discipline is unchanged. The same common pressure
 # predicate consumes a hint obtained only from the actual late sealer snapshot.
 s=once(s,'''(fn2-checkpoint-master-pressure-op
                                  (fn2-checkpoint-master-row-retirement-seen id fn2-core) fn2-core)''',
 '''(fn2-checkpoint-master-pressure-op
                                  (fn2-checkpoint-master-row-retirement-seen id fn2-core)
                                  (if (mv-nth 1 (fn2-sealer-checkpoint-pending-op fn2-core)) t nil) fn2-core)''')
 return once(s,'(include-book "checkpoint-master-arms")','(include-book "checkpoint-master-arms")\n(include-book "checkpoint-master-pressure")')

def project_late(current):
 # Reuse the integrator's named typed/loader emitter projection rather than
 # copying the entire donor assembly or any C/B actor/coordinator book.
 donor=bank.project_emitter(BEFORE['assembly-callbacks-e-cns'])
 keep=('include-book','fn2-c-actor-loader-core-events','fn2-run-load-readiness-core-events',
       'fn2-checkpoint-live-finish-events','make-event','fn2-checkpoint-master-events')
 forms=lr.parse(donor).forms;addition=[]
 for f in forms:
  if not getattr(f,'items',None):continue
  head=lr.emit(f.items[0],drop_comments=True);raw=donor[f.start:f.end]
  if head=='include-book':
   if lr.emit(f.items[1],drop_comments=True) not in ('"c-actor-loader"','"run-physical-readiness-core"','"checkpoint-live-finish"'):continue
  elif head not in keep:continue
  if raw not in current:addition.append(raw)
 # The actual late MASTER macro provider must be included; no core/index row
 # declaration is invented here. Core child/kind registration is a dependency.
 addition.insert(0,'(include-book "checkpoint-master-events")')
 # The current assembly-C lacks these canonical owner materializations. Take
 # only their actual macro calls, not its donor includes/core/coordinator.
 c=(FIX/'canonical-c-materialization-before.lisp').read_text()
 names=('fn2-checkpoint-page-worker-events','fn2-checkpoint-writer-events',
        'fn2-event-producer-rearm-events','fn2-checkpoint-summary-authority-live-events',
        'fn2-checkpoint-live-catalog-events','fn2-checkpoint-live-cbase-events',
        'fn2-checkpoint-live-install-events','fn2-checkpoint-live-retire-events')
 emitted=[]
 for name in names:
  n=one(c,'('+name+')');raw=c[n.start:n.end]
  if raw not in current:emitted.append(raw)
 index=addition.index('(fn2-checkpoint-live-finish-events)')
 addition[index:index]=['(include-book "checkpoint-live-retire")']+emitted
 return once(current,'(fn2-auth-read-events)','\n'.join(addition)+'\n(fn2-auth-read-events)')

CONTROL=(FIX/'checkpoint-master-control-before.lisp').read_text()
EXPECTED={
 'checkpoint-master-state':project_state(BEFORE['checkpoint-master-state']),
 'checkpoint-master-arms':project_arms(BEFORE['checkpoint-master-arms']),
 'checkpoint-master-events':project_events((FIX/'checkpoint-master-events-before.lisp').read_text()),
 'checkpoint-master-pressure':pressure_leaf(CONTROL),
 'checkpoint-master-control':project_control(CONTROL),
 'assembly-callbacks-e-cns':project_late((FIX/'late-current-before.lisp').read_text())}
def validate(book,text):
 if text!=EXPECTED[book]:raise ValueError('not the named actual MASTER request/inventory/wake projection: '+book)
if __name__=='__main__':
 import sys
 for b,s in EXPECTED.items():
  lr.parse(s);p=ROOT/'books'/(b+'.lisp')
  if '--apply' in sys.argv:p.write_text(s)
  else:validate(b,p.read_text())
