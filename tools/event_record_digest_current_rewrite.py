"""Bind the actual semantic receipt to a bounded digest-fetch continuation.

The existing owner/source receipt remains in the phase-gated reader row.
All bytes remain in the same owner-held slot; no second frame or digest codec.
"""
from pathlib import Path
import lisp_rewrite as lr
RETURN='fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests'
def one(source,pattern):
 m=lr.match(pattern,lr.parse(source).forms)
 if len(m)!=1:raise ValueError((pattern,len(m)))
 return m[0].node
def state(source):
 if '(record-fetch-next :u8)' in source:return source
 decl=one(source,'(defcolumns fn2-event-read ?*body)')
 text=source[decl.start:decl.end]
 if text.count(':semantic-seal')!=1:raise ValueError('phase declaration drift')
 text=text.replace(':semantic-seal',':semantic-seal :record-digest',1)
 anchor='(seal-span-started :bool)'
 fields='(record-fetch-next :u8) (record-fetch-acc :u32) (record-fetch-off :u32)\n  '
 text=text.replace(anchor,fields+anchor)
 source=lr.write(source,[(decl.start,decl.end,text)])
 pred=one(source,'(defun fn2-event-read-format-phase-p ?*body)')
 text=source[pred.start:pred.end].replace('*fn2-event-read-phase-semantic-seal*','*fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-record-digest*')
 return lr.write(source,[(pred.start,pred.end,text)])
def helpers():
 return '''; Only actual semantic-verifier success enters RECORD-DIGEST. Source identity
; stays in the existing reader row; each byte visit rechecks its decoded Ref,
; authenticated result/window and the public wrapper's external source owner.
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
))))

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

      (fn2-event-read (fn2-event-read-put 0
       (record-fetch-next next) (record-fetch-acc acc)
       (phase (cond (complete *fn2-event-read-phase-read-records*)
                    ((eq code :more) *fn2-event-read-phase-record-digest*)
                    (t *fn2-event-read-phase-uncertain*))))))
  (mv (if (and (eq code :ok) (not complete)) :invariant code) fn2-event-read fn2-digests)))
(fn2-event-read-preserves fn2-event-read-record-digest-step
 (budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests) :position 1)

'''
def verify(source):
 if '(defun fn2-event-read-record-digest-current-p ' in source:return source
 core=one(source,'(defun fn2-event-read-format-core ?*body)')
 text=source[core.start:core.end]
 old=one(text,'((when semantic) ?*body)')
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
)
             (fn2-event-read-set-phase 0 *fn2-event-read-phase-uncertain* fn2-event-read))))
        (mv (if valid :more :seal) '''+RETURN+''')))'''
 text=lr.write(text,[(old.start,old.end,semantic)])
 anchor=one(text,'((when (member-equal phase (list *fn2-event-read-phase-seal-span* *fn2-event-read-phase-seal-tail*))) ?*body)')
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
 text=lr.write(text,[(anchor.start,anchor.start,'((unless (and (natp budget) (<= budget 4096) (fn2-event-read-format-phase-p (fn2-event-read-phase 0 fn2-event-read)))) (mv :state '+RETURN+'))\n      ((when (equal budget 0)) (mv :more '+RETURN+'))\n      ')])
 source=lr.write(source,[(step.start,step.end,text)])
 load=one(source,'(defun fn2-event-source-load-seal ?*body)')
 text=source[load.start:load.end].replace('(if (>= (nfix i) 8)', '(if (or (not (natp i)) (>= i 8))')
 return lr.write(source,[(load.start,load.end,text)])
def source_begin(source):
 if '(record-fetch-next 0)' in source:return source
 form=one(source,'(defun fn2-event-read-open-core ?*body)')
 text=source[form.start:form.end]
 anchor='(journal-history 0) (journal-incarnation 0)'
 if text.count(anchor)!=1:raise ValueError('open reset drift')
 text=text.replace(anchor,anchor+'\n       (record-fetch-next 0) (record-fetch-acc 0) (record-fetch-off 0)')
 return lr.write(source,[(form.start,form.end,text)])

OBSERVED=('fn2-event-read','fn2-journal-members','fn2-fc','fn2-fc-context','fn2-b3','fn2-fields','fn2-pool','fn2-mk','fn2-extents','fn2-alloc-edges','fn2-ops','fn2-control','fn2-digests')
def observations(source):
 snapshot=one(source,'(defun fn2-epv-fetch-snapshot ?*body)')
 bindings=' '.join('('+name+' (fn2-core-'+name.removeprefix('fn2-')+' fn2-core))' for name in OBSERVED)
 values=' '.join('(fn2-test-table-snapshot-'+name+' '+name+')' for name in OBSERVED)
 replacement='(defun fn2-epv-fetch-snapshot (fn2-core)\n (declare (xargs :stobjs fn2-core :verify-guards nil))\n (stobj-let ('+bindings+') (answer)\n  (list '+values+') answer))'
 source=lr.write(source,[(snapshot.start,snapshot.end,replacement)])
 for name in OBSERVED:
  source=source.replace('('+name+'-copy '+name+')', '(fn2-test-table-snapshot-'+name+' '+name+')')
 return source
def verified(source):
 if '(defun fn2-epv-fetch-one ' in source:return source
 fixtures=Path(__file__).parent/'fixtures/event-record-digest-current'
 reference='(include-book "column-snapshot-support")\n'
 for name in OBSERVED:
  reference+=f"(make-event (if (function-symbolp 'fn2-test-table-snapshot-{name} (w state)) (value '(value-triple :invisible)) (cons 'progn (fn2-test-column-snapshot-events '{name} (w state)))))\n"
 source=source.replace('(fn2-epv-wrapper fn2-epv-format nil','(fn2-epv-wrapper fn2-epv-format (budget)',1).replace('(fn2-event-read-format-step 4096','(fn2-event-read-format-step budget',1)
 anchor=one(source,'(defun fn2-epv-physical ?*body)')
 source=lr.write(source,[(anchor.start,anchor.start,reference+observations((fixtures/'verified-additions.lisp').read_text())+'\n')])
 drive=one(source,'(defun fn2-epv-drive ?*body)')
 source=lr.write(source,[(drive.start,drive.end,(fixtures/'verified-drive-after.lisp').read_text().strip())])
 return source+'\n(assert-event (fn2-epv-test :loan))\n'

if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 for name,fun in [('event-read-state',state),('event-read-verify',verify),('event-read-source',source_begin)]:
  p=root/'books'/(name+'.lisp');p.write_text(fun(p.read_text()))

