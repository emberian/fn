"""Bind the actual semantic receipt to a bounded digest-fetch continuation.

The saved scalar class is one declaration/capture/comparison transformation.
All bytes remain in the same owner-held slot; no second frame or digest codec.
"""
from pathlib import Path
import lisp_rewrite as lr
SAVED=[('token','u60'),('commit','u60'),('slot','u32'),('gen','u60'),
 ('owner-kind','u8'),('owner-slot','u32'),('owner-gen','u60'),('checker','u32'),
 ('field-base','u32'),('body-off','u32'),('body-len','u32'),('extent','u32'),
 ('epoch','u60'),('allocation','u60'),('first','u60'),('members','u32'),
 ('journal-history','u60'),('journal-incarnation','u60'),('cut-commit','u60'),('cut-event','u60')]
RETURN='fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests'
def one(source,pattern):
 m=lr.match(pattern,lr.parse(source).forms)
 if len(m)!=1:raise ValueError((pattern,len(m)))
 return m[0].node
def state(source):
 if '(record-fetch-next :u8)' in source:return source
 decl=one(source,'(defcolumns fn2-event-read ?*body)')
 text=source[decl.start:decl.end]
 if text.count(':semantic-seal :witness-seal')!=1:raise ValueError('phase declaration drift')
 text=text.replace(':semantic-seal :witness-seal',':semantic-seal :record-digest :witness-seal')
 anchor='(seal-span-started :bool)'
 fields='(record-fetch-next :u8) (record-fetch-acc :u32) (record-fetch-off :u32)\n  '+ '\n  '.join('(fetch-'+name+' :'+typ+')' for name,typ in SAVED)+'\n  '
 text=text.replace(anchor,fields+anchor)
 source=lr.write(source,[(decl.start,decl.end,text)])
 pred=one(source,'(defun fn2-event-read-format-phase-p ?*body)')
 text=source[pred.start:pred.end].replace('*fn2-event-read-phase-semantic-seal*','*fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-record-digest*')
 return lr.write(source,[(pred.start,pred.end,text)])
def helpers():
 same='\n'.join('       (equal (fn2-event-read-fetch-'+name+' 0 fn2-event-read) (fn2-event-read-'+name+' 0 fn2-event-read))' for name,_ in SAVED)
 return '''; Only the actual semantic-verifier success captures this receipt. Each
; resumed byte visit rebinds every saved source scalar and the decoded Ref.
(defun fn2-event-read-record-digest-current-p (expected fn2-event-read fn2-fc fn2-fields fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-fc fn2-fields fn2-digests) :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-fc-wfp fn2-fc)
              (fn2-fields-wfp fn2-fields) (fn2-digests-wfp fn2-digests))))
 (and (< 0 (fn2-event-read-rows fn2-event-read))
  (let* ((row (fn2-event-read-checker 0 fn2-event-read))
         (base (fn2-event-read-field-base 0 fn2-event-read))
         (field (+ base *fn2-format-sealed-batch-field-record-stream*))
         (off (fn2-event-read-record-fetch-off 0 fn2-event-read)))
   (and (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-record-digest*)
        (< row (fn2-fc-rows fn2-fc))
        (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)
        (<= (+ base *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))
        (fn2-digest-rowp expected fn2-digests)
        (fn2-digest-rowp (fn2-digest-slot row *fn2-fc-result*) fn2-digests)
        (fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)
        (fn2-rec-fetch-state-p (fn2-event-read-record-fetch-next 0 fn2-event-read)
                              (fn2-event-read-record-fetch-acc 0 fn2-event-read))
        (equal (fn2-fields-ref-slot field fn2-fields) (fn2-event-read-slot 0 fn2-event-read))
        (equal (fn2-fields-ref-gen field fn2-fields) (fn2-event-read-gen 0 fn2-event-read))
        (equal (fn2-fields-ref-off field fn2-fields) off)
        (equal (fn2-fields-ref-len field fn2-fields) 32)
        (<= (fn2-event-read-body-off 0 fn2-event-read) off)
        (<= (+ off 32) (+ (fn2-event-read-body-off 0 fn2-event-read) (fn2-event-read-body-len 0 fn2-event-read)))
'''+same+'''))))

(defun fn2-event-read-record-digest-step (budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests) :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-fc-wfp fn2-fc)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (fn2-event-read-record-digest-current-p expected fn2-event-read fn2-fc fn2-fields fn2-digests))
       (mv :source fn2-event-read fn2-digests))
      ((unless (and (natp budget) (<= budget *fn2-commit-unit-bytes*)))
       (mv :bounds fn2-event-read fn2-digests))
      ((when (zp budget)) (mv :more fn2-event-read fn2-digests))
      (row (fn2-event-read-checker 0 fn2-event-read))
      (hash (fn2-digest-slot row *fn2-fc-hash*))
      ((unless (fn2-digest-rowp hash fn2-digests)) (mv :bounds fn2-event-read fn2-digests))
      ((mv code next acc fn2-digests)
       (fn2-rec-fetch-step budget (fn2-event-read-record-fetch-next 0 fn2-event-read)
        (fn2-event-read-record-fetch-acc 0 fn2-event-read) hash
        (fn2-event-read-slot 0 fn2-event-read) (fn2-event-read-gen 0 fn2-event-read)
        (fn2-event-read-record-fetch-off 0 fn2-event-read)
        (fn2-event-read-owner-kind 0 fn2-event-read) (fn2-event-read-owner-slot 0 fn2-event-read)
        (fn2-event-read-owner-gen 0 fn2-event-read) fn2-pool fn2-digests))
      (complete (and (eq code :ok) (equal next 32) (equal acc 0)))
      (capture (and complete (equal (fn2-event-read-witness-enabled 0 fn2-event-read) 1)))
      (fn2-event-read (fn2-event-read-put 0
       (record-fetch-next next) (record-fetch-acc acc)
       (phase (cond (complete (if capture *fn2-event-read-phase-witness-seal* *fn2-event-read-phase-read-records*))
                    ((eq code :more) *fn2-event-read-phase-record-digest*) (t *fn2-event-read-phase-uncertain*)))
       (witness-phase (if capture *fn2-event-witness-phase-seal* (fn2-event-read-witness-phase 0 fn2-event-read)))
       (witness-commit (if capture (fn2-event-read-commit 0 fn2-event-read) (fn2-event-read-witness-commit 0 fn2-event-read)))
       (witness-first (if capture (fn2-event-read-first 0 fn2-event-read) (fn2-event-read-witness-first 0 fn2-event-read)))
       (witness-members (if capture (fn2-event-read-members 0 fn2-event-read) (fn2-event-read-witness-members 0 fn2-event-read)))
       (witness-seal-length (if capture (fn2-event-read-body-len 0 fn2-event-read) (fn2-event-read-witness-seal-length 0 fn2-event-read)))
       (witness-cursor (if capture 0 (fn2-event-read-witness-cursor 0 fn2-event-read))))))
  (mv (if (and (eq code :ok) (not complete)) :invariant code) fn2-event-read fn2-digests)))
(fn2-event-read-preserves fn2-event-read-record-digest-step
 (budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests) :position 1)

'''
def verify(source):
 if '(defun fn2-event-read-record-digest-current-p ' in source:return source
 core=one(source,'(defun fn2-event-read-format-core ?*body)')
 text=source[core.start:core.end]
 old=one(text,'((when semantic) ?*body)')
 capture='\n'.join('             (fetch-'+name+' (fn2-event-read-'+name+' 0 fn2-event-read))' for name,_ in SAVED)
 semantic='''((when semantic)
       (b* ((first (fn2-event-read-first 0 fn2-event-read))
            (members (fn2-event-read-members 0 fn2-event-read))
            (field (+ base *fn2-format-sealed-batch-field-record-stream*))
            (off (fn2-fields-ref-off field fn2-fields))
            (valid (and (fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)
                        (posp first) (posp members)
                        (equal (fn2-fields-value (+ base *fn2-format-sealed-batch-field-event-first*) fn2-fields) first)
                        (equal (fn2-fields-value (+ base *fn2-format-sealed-batch-field-event-last*) fn2-fields) (+ first members -1))
                        (equal (fn2-fields-ref-slot field fn2-fields) slot)
                        (equal (fn2-fields-ref-gen field fn2-fields) gen)
                        (equal (fn2-fields-ref-len field fn2-fields) 32)
                        (<= (fn2-event-read-body-off 0 fn2-event-read) off)
                        (<= (+ off 32) (+ (fn2-event-read-body-off 0 fn2-event-read) (fn2-event-read-body-len 0 fn2-event-read)))))
            (fn2-event-read (if valid (fn2-event-read-put 0
             (phase *fn2-event-read-phase-record-digest*)
             (record-fetch-next 0) (record-fetch-acc 0) (record-fetch-off off)
'''+capture+''')
             (fn2-event-read-set-phase 0 *fn2-event-read-phase-uncertain* fn2-event-read))))
        (mv (if valid :more :seal) '''+RETURN+''')))'''
 text=lr.write(text,[(old.start,old.end,semantic)])
 anchor=one(text,'((when (member-equal phase (list *fn2-event-read-phase-witness-seal* *fn2-event-read-phase-witness-header*))) ?*body)')
 branch='''((when (equal phase *fn2-event-read-phase-record-digest*))
       (mv-let (code fn2-event-read fn2-digests)
        (fn2-event-read-record-digest-step budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests)
        (mv code '''+RETURN+''')))
      '''
 text=lr.write(text,[(anchor.start,anchor.start,branch)])
 source=lr.write(source,[(core.start,core.end,helpers()+text)])
 step=one(source,'(defun fn2-event-read-format-step ?*body)')
 text=source[step.start:step.end]
 anchor=one(text,'((mv expected-code expected fn2-digests) ?body)')
 # Retain owner/source refusal order, yield before archived-seal row writes.
 text=lr.write(text,[(anchor.start,anchor.start,'((when (equal budget 0)) (mv :more '+RETURN+'))\n      ')])
 return lr.write(source,[(step.start,step.end,text)])
def source_begin(source):
 if '(record-fetch-next 0)' in source:return source
 form=one(source,'(defun fn2-event-read-open-core ?*body)')
 text=source[form.start:form.end]
 anchor='(journal-history 0) (journal-incarnation 0)'
 if text.count(anchor)!=1:raise ValueError('open reset drift')
 text=text.replace(anchor,anchor+'\n       (record-fetch-next 0) (record-fetch-acc 0) (record-fetch-off 0)\n       '+ ' '.join('(fetch-'+name+' 0)' for name,_ in SAVED))
 return lr.write(source,[(form.start,form.end,text)])

def fixture(s):
 if '(defun fn2-epv-fetch-controls ' in s:return s
 s=s.replace('(fn2-epv-wrapper fn2-epv-format nil','(fn2-epv-wrapper fn2-epv-format (budget)',1).replace('(fn2-event-read-format-step 4096 ','(fn2-event-read-format-step budget ',1)
 anchor='(defun fn2-epv-physical '
 helper='''; Full mutable-carrier snapshots are test observations, never served work.
 (defun fn2-epv-fetch-snapshot (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core))
              (fn2-journal-members (fn2-core-journal-members fn2-core))
              (fn2-fc (fn2-core-fc fn2-core)) (fn2-fc-context (fn2-core-fc-context fn2-core))
              (fn2-b3 (fn2-core-b3 fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
              (fn2-pool (fn2-core-pool fn2-core)) (fn2-digests (fn2-core-digests fn2-core))) (answer)
   (list (fn2-event-read-copy fn2-event-read) (fn2-journal-members-copy fn2-journal-members)
         (fn2-fc-copy fn2-fc) (fn2-fc-context-copy fn2-fc-context) (fn2-b3-copy fn2-b3)
         (fn2-fields-copy fn2-fields) (fn2-pool-copy fn2-pool) (fn2-digests-copy fn2-digests)) answer))
 (defun fn2-epv-fetch-readonly (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (cdr (butlast (fn2-epv-fetch-snapshot fn2-core) 1)))
 
 ; Apply one deliberate between-visit substitution, then restore the exact
 ; scalar. The production step must refuse without touching any carrier.
 (defun fn2-epv-fetch-substitute (fault restore saved fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core))
              (fn2-fields (fn2-core-fields fn2-core)) (fn2-digests (fn2-core-digests fn2-core)))
   (value fn2-event-read fn2-fields fn2-digests)
   (b* ((field (+ (fn2-event-read-field-base 0 fn2-event-read) *fn2-format-sealed-batch-field-record-stream*))
        (result (fn2-digest-slot (fn2-event-read-checker 0 fn2-event-read) *fn2-fc-result*))
        (value (case fault
 '''
 for field in ['token','slot','gen','commit']:
  helper+=f'        (:{field} (fn2-event-read-{field} 0 fn2-event-read))\n'
 helper+='''        (:ref (fn2-fields-ref-off field fn2-fields))
         (otherwise (fn2-digest-word result 0 fn2-digests))))
        (new (if restore saved (if (eq fault :result) (logxor 1 value) (+ 1 value))))
        (fn2-event-read (case fault
 '''
 for field in ['token','slot','gen','commit']:
  helper+=f'        (:{field} (fn2-event-read-set-{field} 0 new fn2-event-read))\n'
 helper+='''        (otherwise fn2-event-read)))
        (fn2-fields (if (eq fault :ref) (fn2-fields-set-ref-off field new fn2-fields) fn2-fields))
        (fn2-digests (if (eq fault :result) (fn2-digest-set-word result 0 new fn2-digests) fn2-digests)))
    (mv value fn2-event-read fn2-fields fn2-digests)) (mv value fn2-core)))
 (defun fn2-epv-fetch-refusals (faults fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (endp faults) (mv t fn2-core)
   (b* ((original (fn2-epv-fetch-snapshot fn2-core))
        ((mv saved fn2-core) (fn2-epv-fetch-substitute (car faults) nil 0 fn2-core))
        (before (fn2-epv-fetch-snapshot fn2-core))
        ((mv code fn2-core) (fn2-epv-format 1 fn2-core))
        (untouched (equal before (fn2-epv-fetch-snapshot fn2-core)))
        ((mv & fn2-core) (fn2-epv-fetch-substitute (car faults) t saved fn2-core))
        ((unless (and (eq code (if (eq (car faults) :token) :snapshot :source)) untouched
                      (equal original (fn2-epv-fetch-snapshot fn2-core)))) (mv nil fn2-core)))
    (fn2-epv-fetch-refusals (cdr faults) fn2-core))))
 (defun fn2-epv-fetch-controls (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((before (fn2-epv-fetch-snapshot fn2-core))
       ((mv code fn2-core) (fn2-epv-format 0 fn2-core))
       ((unless (and (eq code :more) (equal before (fn2-epv-fetch-snapshot fn2-core)))) (mv nil fn2-core)))
   (fn2-epv-fetch-refusals '(:token :slot :gen :commit :ref :result) fn2-core)))
 ; Removing the owned source loan after one genuine byte is a hypothesis
 ; removal control: the next real reader visit must report stale, preserve the
 ; partial digest, and enter UNCERTAIN rather than expose records.
 (defun fn2-epv-fetch-loan-error (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv released fn2-core)
        (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core)) (fn2-pool (fn2-core-pool fn2-core))) (code fn2-pool)
         (fn2-pool-release (fn2-event-read-slot 0 fn2-event-read) (fn2-event-read-gen 0 fn2-event-read)
          (fn2-event-read-owner-kind 0 fn2-event-read) (fn2-event-read-owner-slot 0 fn2-event-read)
          (fn2-event-read-owner-gen 0 fn2-event-read) fn2-pool) (mv code fn2-core)))
       (before (fn2-epv-fetch-readonly fn2-core))
       ((mv acc digest)
        (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core)) (fn2-digests (fn2-core-digests fn2-core))) (acc digest)
         (mv (fn2-event-read-record-fetch-acc 0 fn2-event-read) (fn2-digests-copy fn2-digests)) (mv acc digest)))
       ((mv code fn2-core) (fn2-epv-format 1 fn2-core))
       (after
        (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core)) (fn2-digests (fn2-core-digests fn2-core))) (after)
         (and (= (fn2-event-read-record-fetch-next 0 fn2-event-read) 1)
              (= (fn2-event-read-record-fetch-acc 0 fn2-event-read) acc)
              (= (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-uncertain*)
              (equal digest (fn2-digests-copy fn2-digests))) after)))
   (mv (and (eq released :ok) (eq code :stale) after
            (equal before (fn2-epv-fetch-readonly fn2-core))) fn2-core)))
 (defun fn2-epv-fetch-word-frame (i next before after)
  (declare (xargs :measure (nfix (- 8 (nfix i))) :verify-guards nil))
  (if (or (not (natp i)) (>= i 8)) t
   (and (or (and (= (mod next 4) 0) (= i (- (floor next 4) 1)))
            (equal (nth i before) (nth i after)))
        (fn2-epv-fetch-word-frame (+ 1 i) next before after))))
 (defun fn2-epv-fetch-one (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv next before)
        (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core)) (fn2-digests (fn2-core-digests fn2-core))) (next before)
         (mv (fn2-event-read-record-fetch-next 0 fn2-event-read)
             (fn2-digest-list (fn2-digest-slot (fn2-event-read-checker 0 fn2-event-read) *fn2-fc-hash*) fn2-digests))
         (mv next before)))
       (readonly (fn2-epv-fetch-readonly fn2-core))
       ((mv code fn2-core) (fn2-epv-format 1 fn2-core))
       (good
        (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core)) (fn2-digests (fn2-core-digests fn2-core))) (good)
         (let ((after (fn2-event-read-record-fetch-next 0 fn2-event-read)))
          (and (< next 32) (= after (+ next 1))
               (fn2-rec-fetch-state-p after (fn2-event-read-record-fetch-acc 0 fn2-event-read))
               (eq code (if (= after 32) :ok :more))
               (= (fn2-event-read-phase 0 fn2-event-read)
                  (if (= after 32) *fn2-event-read-phase-read-records* *fn2-event-read-phase-record-digest*))
               (fn2-epv-fetch-word-frame 0 after before
                (fn2-digest-list (fn2-digest-slot (fn2-event-read-checker 0 fn2-event-read) *fn2-fc-hash*) fn2-digests)))) good)))
   (mv (and good (equal readonly (fn2-epv-fetch-readonly fn2-core))) fn2-core)))
 
 '''
 assert s.count(anchor)==1;s=s.replace(anchor,helper+anchor)
 anchor='      ((mv & fn2-core)\n       (cond ((member-equal phase'
 insert='''      (fetch (equal phase *fn2-event-read-phase-record-digest*))
       (first-fetch (and fetch (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core))) (first)
                                 (member-equal (fn2-event-read-record-fetch-next 0 fn2-event-read) '(0 1)) first)))
       ((mv controls fn2-core) (if first-fetch (fn2-epv-fetch-controls fn2-core) (mv t fn2-core)))
       ((unless controls) (mv *fn2-event-read-phase-uncertain* (reverse records) fn2-core fn2-sim fn2-own))
       (loan-error (and (eq fault :loan) fetch
                    (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core))) (partial)
                     (= (fn2-event-read-record-fetch-next 0 fn2-event-read) 1) partial)))
       ((mv failed-closed fn2-core) (if loan-error (fn2-epv-fetch-loan-error fn2-core) (mv t fn2-core)))
       ((when loan-error) (mv (if failed-closed *fn2-event-read-phase-uncertain* *fn2-event-read-phase-idle*)
                            (reverse records) fn2-core fn2-sim fn2-own))
       ((mv fetched fn2-core) (if fetch (fn2-epv-fetch-one fn2-core) (mv t fn2-core)))
       ((unless fetched) (mv *fn2-event-read-phase-uncertain* (reverse records) fn2-core fn2-sim fn2-own))
 '''
 assert s.count(anchor)==1;s=s.replace(anchor,insert+anchor)
 s=s.replace('((fn2-event-read-format-phase-p phase)\n              (fn2-epv-format fn2-core))','((and (not fetch) (fn2-event-read-format-phase-p phase))\n              (fn2-epv-format 4096 fn2-core))',1)
 s += '(assert-event (fn2-epv-test :loan))\n'
 return '\n'.join(line.rstrip() for line in s.splitlines())+'\n'
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 for name,fun in [('event-read-state',state),('event-read-verify',verify),('event-read-source',source_begin)]:
  p=root/'books'/(name+'.lisp');p.write_text(fun(p.read_text()))
 p=root/'tests/event-read-verified-unit.lisp';p.write_text(fixture(p.read_text()))
