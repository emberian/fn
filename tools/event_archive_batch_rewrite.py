"""Actual selected schema20 source -> resumable original-header continuation.

One source scalar/Ref class emits fields, capture and rebinding. This is an
intermediate constructor: HEADER-CHECKED never grants batch/prefix authority.
"""
from pathlib import Path
import lisp_rewrite as lr
FIELDS=[('batch-page','u32'),('batch-page-gen','u60'),('batch-entry','u32'),
 ('batch-source-unit','u60'),('batch-source-epoch','u60'),('batch-source-allocation','u60'),
 ('batch-header-off','u32'),('batch-header-length','u32'),('batch-seal-off','u32'),('batch-seal-length','u32'),
 ('batch-first','u60'),('batch-last','u60'),('batch-commit','u60'),('batch-extent','u32'),
 ('batch-epoch','u60'),('batch-allocation','u60'),('batch-history','u60'),('batch-incarnation','u60'),
 ('batch-decode-started','bool'),('batch-cursor','u32')]
def node(s,p):
 m=lr.match(p,lr.parse(s).forms)
 if len(m)!=1:raise ValueError((p,len(m)))
 return m[0].node
def state(s):
 if '(batch-header-length :u32)' in s:return s
 n=node(s,'(defcolumns fn2-event-archive ?*body)')
 anchor=node(s,'(accumulator-slot :u32)')
 decl='''; Private original-batch work retains the same selected source owner.
  ; Neither header decode nor copied witness data is a verified batch receipt.
  (batch-phase (:enum fn2-event-archive-batch-phase (:idle :header :seal-copy :seal-span :expected :semantic :records-zero :records-header :records-members :records-trailer :records-verify :complete :uncertain)))
  '''+'\n  '.join('('+name+' :'+typ+')' for name,typ in FIELDS)+'\n  '
 if not (n.start<anchor.start<n.end):raise ValueError('archive declaration source drift')
 return lr.write(s,[(anchor.start,anchor.start,decl)])

CHILDREN='''fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-run-loads fn2-run-cursors fn2-fc fn2-fields fn2-pool'''
PAGE_ARGS=CHILDREN.replace(' fn2-fc','')
REFS=[('header','original-records-header'),('seal','original-sealed-batch')]
BIND=[('batch-page','page'),('batch-page-gen','pgen'),('batch-entry','(fn2-run-cursors-idx c fn2-run-cursors)'),
 ('batch-source-unit','(fn2-run-loads-unit c fn2-run-loads)'),('batch-source-epoch','(fn2-run-loads-epoch c fn2-run-loads)'),
 ('batch-source-allocation','(fn2-run-loads-allocation c fn2-run-loads)')]
def source_body():
 refs='\n'.join('      ('+short+' (+ eb *fn2-event-archive-member-entry-field-'+long+'*))' for short,long in REFS)
 captures='\n'.join('       ('+name+' '+value+')' for name,value in BIND)
 captures+='\n'+ '\n'.join('       (batch-'+short+'-off (fn2-fields-ref-off '+short+' fn2-fields)) (batch-'+short+'-length (fn2-fields-ref-len '+short+' fn2-fields))' for short,_ in REFS)
 matches='\n'.join('        (equal (fn2-event-archive-'+name+' 1 fn2-event-archive) '+value+')' for name,value in BIND)
 matches+='\n'+'\n'.join('        (equal (fn2-fields-ref-slot '+short+' fn2-fields) page) (equal (fn2-fields-ref-gen '+short+' fn2-fields) pgen)\n        (equal (fn2-fields-ref-off '+short+' fn2-fields) (fn2-event-archive-batch-'+short+'-off 1 fn2-event-archive))\n        (equal (fn2-fields-ref-len '+short+' fn2-fields) (fn2-event-archive-batch-'+short+'-length 1 fn2-event-archive))' for short,_ in REFS)
 return '''; This original-header substep is not yet routed by the boot machine
; (unreachable-in-composition). It grants no batch or prefix authority.
; Reuse the actual initialized checker/field stripe geometry; malformed direct
; tables must not alias the frozen archive entry with the private decoder.
(defun fn2-event-archive-cold-batch-fields-p (fn2-run-loads fn2-run-cursors fn2-fc fn2-fields)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-fc fn2-fields) :verify-guards nil
  :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-fc-wfp fn2-fc) (fn2-fields-wfp fn2-fields))))
 (and (fn2-b-fixed-cursor-rows-p (fn2-run-loads-rows fn2-run-loads))
      (equal (fn2-run-loads-rows fn2-run-loads) (fn2-run-cursors-rows fn2-run-cursors))
  (let* ((c (fn2-b-event-archive-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
         (row (fn2-b-event-row (fn2-fc-rows fn2-fc)))
         (checker (fn2-run-loads-checker c fn2-run-loads)))
   (and (< checker (fn2-fc-rows fn2-fc)) (< row (fn2-fc-rows fn2-fc)) (not (equal row checker))
        (equal (fn2-run-cursors-rb c fn2-run-cursors) (* 128 checker))
        (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)
        (<= *fn2-format-frame-header-num-fields* 128) (<= *fn2-format-sealed-batch-num-fields* 128)
        (<= (* 128 (+ row 1)) (fn2-fields-rows fn2-fields))))))

; The existing selected-page predicate remains the authority wrapper. These
; steps decode an original header, not a verified original batch or prefix.
(fn2-event-archive-operation fn2-event-archive-cold-batch-begin
 ('''+CHILDREN+''') (fn2-event-archive)
 (:bytes *fn2-commit-unit-bytes*)
 (b* (((unless (fn2-event-archive-cold-member-page-p '''+PAGE_ARGS+''')) (mv :source fn2-event-archive))
      ((unless (and (fn2-event-archive-cold-batch-fields-p fn2-run-loads fn2-run-cursors fn2-fc fn2-fields)
                    (equal (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-idle*))) (mv :state fn2-event-archive))
      (c (fn2-b-event-archive-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
      (base (fn2-run-cursors-rb c fn2-run-cursors)) (eb (+ base *fn2-run-reader-entry*))
      (page (fn2-run-loads-page c fn2-run-loads)) (pgen (fn2-run-loads-page-gen c fn2-run-loads))
      (event (fn2-event-archive-next-event 1 fn2-event-archive))
'''+refs+'''
      ((unless (and (equal event 1) (equal (fn2-event-archive-member-seen 1 fn2-event-archive) 0)
                    (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-history*) fn2-fields) (fn2-event-archive-history 1 fn2-event-archive))
                    (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-incarnation*) fn2-fields) (fn2-event-archive-incarnation 1 fn2-event-archive))
                    (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-event*) fn2-fields) event)
                    (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-batch-first*) fn2-fields) event)
                    (equal (fn2-fields-ref-slot header fn2-fields) page) (equal (fn2-fields-ref-gen header fn2-fields) pgen)
                    (posp (fn2-fields-ref-len header fn2-fields)) (<= (fn2-fields-ref-len header fn2-fields) *fn2-format-frame-header-max-size*)
                    (<= (+ (fn2-fields-ref-off header fn2-fields) (fn2-fields-ref-len header fn2-fields)) (fn2-pool-fill page fn2-pool))
                    (equal (fn2-fields-ref-slot seal fn2-fields) page) (equal (fn2-fields-ref-gen seal fn2-fields) pgen)
                    (posp (fn2-fields-ref-len seal fn2-fields)) (<= (fn2-fields-ref-len seal fn2-fields) *fn2-format-sealed-batch-max-size*)
                    (<= (+ (fn2-fields-ref-off seal fn2-fields) (fn2-fields-ref-len seal fn2-fields)) (fn2-pool-fill page fn2-pool))))
       (mv :witness fn2-event-archive))
      (fn2-event-archive (fn2-event-archive-put 1 (batch-phase *fn2-event-archive-batch-phase-header*)
       (batch-decode-started 0) (batch-cursor (fn2-fields-ref-off header fn2-fields)) (batch-first event)
'''+captures+''')))
  (mv :more fn2-event-archive)))

(defun fn2-event-archive-cold-batch-header-current-p ('''+CHILDREN+''')
 (declare (xargs :stobjs ('''+CHILDREN+''') :verify-guards nil
  :guard (and '''+' '.join('('+x+'-wfp '+x+')' for x in CHILDREN.split())+''')))
 (and (fn2-event-archive-cold-member-page-p '''+PAGE_ARGS+''')
  (fn2-event-archive-cold-batch-fields-p fn2-run-loads fn2-run-cursors fn2-fc fn2-fields)
  (equal (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-header*)
  (let* ((c (fn2-b-event-archive-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
         (eb (+ (fn2-run-cursors-rb c fn2-run-cursors) *fn2-run-reader-entry*))
         (page (fn2-run-loads-page c fn2-run-loads)) (pgen (fn2-run-loads-page-gen c fn2-run-loads))
         (header (+ eb *fn2-event-archive-member-entry-field-original-records-header*))
         (seal (+ eb *fn2-event-archive-member-entry-field-original-sealed-batch*)))
   (and (equal (fn2-event-archive-next-event 1 fn2-event-archive) (fn2-event-archive-batch-first 1 fn2-event-archive))
        (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-event*) fn2-fields) (fn2-event-archive-batch-first 1 fn2-event-archive))
        (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-batch-first*) fn2-fields) (fn2-event-archive-batch-first 1 fn2-event-archive))
'''+matches+'''))))

(fn2-event-archive-operation (fn2-event-archive-cold-batch-header-step budget)
 ('''+CHILDREN+''') (fn2-event-archive fn2-fields)
 (:bytes *fn2-commit-unit-bytes*)
 (b* (((unless (fn2-event-archive-cold-batch-header-current-p '''+CHILDREN+''')) (mv :source fn2-event-archive fn2-fields))
      ((unless (and (natp budget) (<= budget *fn2-commit-unit-bytes*))) (mv :bounds fn2-event-archive fn2-fields))
      ((when (zp budget)) (mv :more fn2-event-archive fn2-fields))
      (row (fn2-b-event-row (fn2-fc-rows fn2-fc))) (base (* 128 row))
      ((unless (and (< row (fn2-fc-rows fn2-fc)) (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)
                    (<= (+ base *fn2-format-frame-header-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :fields fn2-event-archive fn2-fields))
      (slot (fn2-event-archive-batch-page 1 fn2-event-archive)) (gen (fn2-event-archive-batch-page-gen 1 fn2-event-archive))
      (off (fn2-event-archive-batch-header-off 1 fn2-event-archive)) (end (+ off (fn2-event-archive-batch-header-length 1 fn2-event-archive)))
      (kind (fn2-event-archive-owner-kind 1 fn2-event-archive)) (owner (fn2-event-archive-owner-slot 1 fn2-event-archive)) (generation (fn2-event-archive-owner-gen 1 fn2-event-archive))
      (fn2-fields (if (equal (fn2-event-archive-batch-decode-started 1 fn2-event-archive) 0) (fn2-format-frame-header-start base fn2-fields) fn2-fields))
      ((mv code next fn2-fields) (fn2-format-frame-header-decode-step base slot gen off end kind owner generation budget fn2-fields fn2-pool))
      (history (fn2-fields-value (+ base *fn2-format-frame-header-field-history*) fn2-fields))
      (incarnation (fn2-fields-value (+ base *fn2-format-frame-header-field-incarnation*) fn2-fields))
      (extent (fn2-fields-value (+ base *fn2-format-frame-header-field-extent*) fn2-fields))
      (epoch (fn2-fields-value (+ base *fn2-format-frame-header-field-extent-writer-epoch*) fn2-fields))
      (allocation (fn2-fields-value (+ base *fn2-format-frame-header-field-extent-allocation*) fn2-fields))
      (commit (fn2-fields-value (+ base *fn2-format-frame-header-field-commit*) fn2-fields))
      (valid (and (eq code :ok) (equal next end) (fn2-origin-physicalp history incarnation)
                  (unsigned-byte-p 32 extent) (posp epoch) (posp allocation) (equal commit 1)
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-writer-epoch*) fn2-fields) epoch)
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-magic*) fn2-fields) *fn2-format-frame-magic*)
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-frame-kind*) fn2-fields) *frame-kind-records*)
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-ordinal*) fn2-fields) 0)
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-fragment-offset*) fn2-fields) 0)
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-payload-length*) fn2-fields) *fn2-commit-records-room*)
                  (<= (+ (- end off) *fn2-commit-records-room*) *fn2-commit-frame-trailer*)))
      (fn2-event-archive (fn2-event-archive-put 1 (batch-decode-started 1) (batch-cursor next)
       (batch-phase (cond ((eq code :more) *fn2-event-archive-batch-phase-header*) (valid *fn2-event-archive-batch-phase-seal-copy*) (t *fn2-event-archive-batch-phase-uncertain*)))
       (batch-history (if valid history (fn2-event-archive-batch-history 1 fn2-event-archive)))
       (batch-incarnation (if valid incarnation (fn2-event-archive-batch-incarnation 1 fn2-event-archive)))
       (batch-extent (if valid extent (fn2-event-archive-batch-extent 1 fn2-event-archive)))
       (batch-epoch (if valid epoch (fn2-event-archive-batch-epoch 1 fn2-event-archive)))
       (batch-allocation (if valid allocation (fn2-event-archive-batch-allocation 1 fn2-event-archive)))
       (batch-commit (if valid commit (fn2-event-archive-batch-commit 1 fn2-event-archive))))))
  (mv (cond ((eq code :more) :more) (valid :header-checked) ((eq code :ok) :header) (t code)) fn2-event-archive fn2-fields)))

'''
def members(s):
 if '(fn2-event-archive-operation fn2-event-archive-cold-batch-begin' in s:return s
 n=node(s,'(fn2-event-archive-operation fn2-event-archive-cold-member-step ?*body)')
 return lr.write(s,[(n.start,n.start,source_body())])
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 for name,fun in [('event-archive-state',state),('event-archive-cold-members',members)]:
  p=root/'books'/(name+'.lisp');p.write_text(fun(p.read_text()))
