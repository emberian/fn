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
 ('batch-decode-started','bool'),('batch-cursor','u32'),('batch-copy-started','bool'),('batch-copy-next','u32'),
 ('batch-accumulator-slot','u32'),('batch-accumulator-gen','u60')]
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
 ('batch-source-allocation','(fn2-run-loads-allocation c fn2-run-loads)'),
 ('batch-accumulator-slot','(fn2-event-archive-accumulator-slot 1 fn2-event-archive)'),
 ('batch-accumulator-gen','(fn2-event-archive-accumulator-gen 1 fn2-event-archive)')]
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
      ((unless (and (equal event 1) (posp (fn2-event-archive-cut-commit 1 fn2-event-archive))
                    (<= event (fn2-event-archive-cut-event 1 fn2-event-archive))
                    (equal event (fn2-event-archive-member-first-event 1 fn2-event-archive))
                    (<= event (fn2-event-archive-member-last-event 1 fn2-event-archive))
                    (posp (fn2-event-archive-member-entries 1 fn2-event-archive))
                    (equal (fn2-event-archive-member-seen 1 fn2-event-archive) 0)
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
       (batch-copy-started 0) (batch-copy-next 0)
'''+captures+''')))
  (mv :more fn2-event-archive)))

(defun fn2-event-archive-cold-batch-header-current-p ('''+CHILDREN+''')
 (declare (xargs :stobjs ('''+CHILDREN+''') :verify-guards nil
  :guard (and '''+' '.join('('+x+'-wfp '+x+')' for x in CHILDREN.split())+''')))
 (and (fn2-event-archive-cold-member-page-p '''+PAGE_ARGS+''')
  (fn2-event-archive-cold-batch-fields-p fn2-run-loads fn2-run-cursors fn2-fc fn2-fields)
  (member-equal (fn2-event-archive-batch-phase 1 fn2-event-archive) (list *fn2-event-archive-batch-phase-header* *fn2-event-archive-batch-phase-seal-copy*))
  (let* ((c (fn2-b-event-archive-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
         (work (* 128 (fn2-b-event-row (fn2-fc-rows fn2-fc))))
         (eb (+ (fn2-run-cursors-rb c fn2-run-cursors) *fn2-run-reader-entry*))
         (page (fn2-run-loads-page c fn2-run-loads)) (pgen (fn2-run-loads-page-gen c fn2-run-loads))
         (header (+ eb *fn2-event-archive-member-entry-field-original-records-header*))
         (seal (+ eb *fn2-event-archive-member-entry-field-original-sealed-batch*)))
   (and (<= (+ (fn2-event-archive-batch-header-off 1 fn2-event-archive) (fn2-event-archive-batch-header-length 1 fn2-event-archive)) (fn2-pool-fill page fn2-pool))
        (<= (+ (fn2-event-archive-batch-seal-off 1 fn2-event-archive) (fn2-event-archive-batch-seal-length 1 fn2-event-archive)) (fn2-pool-fill page fn2-pool))
        (or (equal (fn2-event-archive-batch-decode-started 1 fn2-event-archive) 0)
                 (equal (fn2-fields-decode-next work fn2-fields) (fn2-event-archive-batch-cursor 1 fn2-event-archive)))
        (equal (fn2-event-archive-next-event 1 fn2-event-archive) (fn2-event-archive-batch-first 1 fn2-event-archive))
        (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-event*) fn2-fields) (fn2-event-archive-batch-first 1 fn2-event-archive))
        (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-batch-first*) fn2-fields) (fn2-event-archive-batch-first 1 fn2-event-archive))
'''+matches+'''))))

(fn2-event-archive-operation (fn2-event-archive-cold-batch-header-step budget)
 ('''+CHILDREN+''') (fn2-event-archive fn2-fields)
 (:bytes *fn2-commit-unit-bytes*)
 (b* (((unless (and (fn2-event-archive-cold-batch-header-current-p '''+CHILDREN+''')
                    (equal (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-header*))) (mv :source fn2-event-archive fn2-fields))
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

def fixture(s):
 if '(defun fn2-eabh-run ' in s:return s
 children=CHILDREN
 snapshot='(list (fn2-event-archive-copy fn2-event-archive) (fn2-fields-copy fn2-fields))'
 helper='''; Writer-produced original header -> selected-source substep. This unit
; retains its explicitly synthetic page/reach premise, not physical authority.
(defun fn2-eabh-drive (fuel budget '''+children+''')
 (declare (xargs :stobjs ('''+children+''') :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel fn2-event-archive fn2-fields)
  (b* ((cursor (fn2-event-archive-batch-cursor 1 fn2-event-archive))
       ((mv code fn2-event-archive fn2-fields) (fn2-event-archive-cold-batch-header-step budget '''+children+'''))
       (after (fn2-event-archive-batch-cursor 1 fn2-event-archive))
       ((unless (and (<= cursor after) (<= (- after cursor) budget))) (mv :overrun fn2-event-archive fn2-fields))
       ((unless (eq code :more)) (mv code fn2-event-archive fn2-fields)))
   (fn2-eabh-drive (- fuel 1) budget '''+children+'''))))
(defun fn2-eabh-substitutions (faults '''+children+''')
 (declare (xargs :stobjs ('''+children+''') :verify-guards nil))
 (if (endp faults) (mv t fn2-event-archive fn2-fields)
  (b* ((c (fn2-b-event-archive-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
       (base (* 128 (fn2-b-event-row (fn2-fc-rows fn2-fc))))
       (entry (+ (fn2-run-cursors-rb c fn2-run-cursors) *fn2-run-reader-entry*))
       (decoder (eq (car faults) :decoder-next))
       (field (+ entry (if (eq (car faults) :header-off)
                        *fn2-event-archive-member-entry-field-original-records-header*
                        *fn2-event-archive-member-entry-field-original-sealed-batch*)))
       (saved (if decoder (fn2-fields-decode-next base fn2-fields) (fn2-fields-ref-off field fn2-fields)))
       (original '''+snapshot+''')
       (fn2-fields (if decoder (fn2-fields-set-decode-next base (+ saved 1) fn2-fields)
                     (fn2-fields-set-ref-off field (+ saved 1) fn2-fields)))
       (before '''+snapshot+''')
       ((mv code fn2-event-archive fn2-fields) (fn2-event-archive-cold-batch-header-step 1 '''+children+'''))
       (untouched (equal before '''+snapshot+'''))
       (fn2-fields (if decoder (fn2-fields-set-decode-next base saved fn2-fields)
                     (fn2-fields-set-ref-off field saved fn2-fields)))
       ((unless (and (eq code :source) untouched (equal original '''+snapshot+'''))) (mv nil fn2-event-archive fn2-fields)))
   (fn2-eabh-substitutions (cdr faults) '''+children+'''))))
(defun fn2-eabh-run ('''+children+''')
 (declare (xargs :stobjs ('''+children+''') :verify-guards nil))
 (b* (((mv code fn2-event-archive) (fn2-event-archive-cold-batch-begin '''+children+'''))
      ((unless (and (eq code :more) (fn2-event-archive-cold-batch-header-current-p '''+children+'''))) (mv :premise fn2-event-archive fn2-fields))
      (before '''+snapshot+''')
      ((mv zero fn2-event-archive fn2-fields) (fn2-event-archive-cold-batch-header-step 0 '''+children+'''))
      ((unless (and (eq zero :more) (equal before '''+snapshot+'''))) (mv :zero fn2-event-archive fn2-fields))
      (off (fn2-event-archive-batch-header-off 1 fn2-event-archive))
      ((mv first fn2-event-archive fn2-fields) (fn2-event-archive-cold-batch-header-step 1 '''+children+'''))
      ((unless (and (eq first :more) (= (fn2-event-archive-batch-cursor 1 fn2-event-archive) (+ off 1)))) (mv :first fn2-event-archive fn2-fields))
      ((mv controls fn2-event-archive fn2-fields) (fn2-eabh-substitutions '(:decoder-next :header-off :seal-off) '''+children+'''))
      ((unless controls) (mv :interleaving fn2-event-archive fn2-fields)))
  (fn2-eabh-drive (+ *fn2-format-frame-header-max-size* *fn2-format-frame-header-num-fields* 2) 1 '''+children+''')))

'''
 n=node(s,'(defun fn2-eamcu-body ?*body)');s=lr.write(s,[(n.start,n.start,helper)])
 n=node(s,'(defun fn2-eamcu-body ?*body)');text=s[n.start:n.end]
 anchor='      (canonical (fn2-pool-logical-octets'
 insert='''      (batch-mode (member-eq fault '(:batch-header :batch-commit :batch-tail)))
      ((mv fh fend fn2-fields fn2-pool)
       (if batch-mode (fn2-commit-pack :frame 1 0 scratch sg 256 scratch sg 1 2 3
                       (if (eq fault :batch-commit) 2 1) 1 1 1 2 3 1 2 3 17 19 fn2-fields fn2-pool)
        (mv :ok 256 fn2-fields fn2-pool)))
      ((mv fs send fn2-fields fn2-pool)
       (if batch-mode (fn2-commit-pack :seal 2 0 scratch sg 512 scratch sg 1 2 3 1 1 1 1 2 3 1 2 3 17 19 fn2-fields fn2-pool)
        (mv :ok 512 fn2-fields fn2-pool)))
'''
 if text.count(anchor)!=1:raise ValueError('member fixture producer anchor drift')
 text=text.replace(anchor,insert+anchor)
 old='(value 1) (ref-slot scratch) (ref-gen sg) (ref-off 0) (ref-len 0)'
 refs=lr.match('(fn2-fields-put (+ eb ?field) ?*bindings)',lr.parse(text).forms)
 edits=[]
 for m in refs:
  field=getattr(m.captures['field'],'low','')
  if field.endswith('field-original-records-header*'):
   replacement='(value 1) (ref-slot scratch) (ref-gen sg) (ref-off (if batch-mode 256 0)) (ref-len (if batch-mode (+ (- fend 256) (if (eq fault :batch-tail) 1 0)) 0))'
  elif field.endswith('field-original-sealed-batch*'):
   replacement='(value 1) (ref-slot scratch) (ref-gen sg) (ref-off (if batch-mode 512 0)) (ref-len (if batch-mode (- send 512) 0))'
  else:continue
  actual=text[m.node.start:m.node.end]
  if actual.count(old)!=1:raise ValueError('member fixture witness span drift')
  edits.append((m.node.start,m.node.end,actual.replace(old,replacement)))
 if len(edits)!=2:raise ValueError('member witness Ref class drift')
 text=lr.write(text,edits)
 old=node(text,'(fn2-eamcu-drive 30 ?*args)')
 actual=text[old.start:old.end]
 dispatch='''(if batch-mode
       (mv-let (code fn2-event-archive fn2-fields) (fn2-eabh-run '''+children+''')
        (mv code fn2-event-archive fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests))
       '''+actual+')'
 text=lr.write(text,[(old.start,old.end,dispatch)])
 anchor="(cond ((member-eq fault '(:event :generation"
 replacement='''(cond ((member-eq fault '(:batch-header :batch-commit :batch-tail))
                  (and (eq fh :ok) (eq fs :ok) (= (fn2-mk-size row fn2-mk) 0)
                       (= (fn2-event-archive-next-event 1 fn2-event-archive) 1)
                       (= (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-members*)
                       (= (fn2-event-archive-entry-pending 1 fn2-event-archive) 1)
                       (if (eq fault :batch-header)
                        (and (eq code :header-checked)
                             (= (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-seal-copy*)
                             (= (fn2-event-archive-batch-history 1 fn2-event-archive) 17)
                             (= (fn2-event-archive-batch-incarnation 1 fn2-event-archive) 19)
                             (= (fn2-event-archive-history 1 fn2-event-archive) 123)
                             (= (fn2-event-archive-incarnation 1 fn2-event-archive) 456)
                             (= (fn2-event-archive-batch-commit 1 fn2-event-archive) 1))
                        (and (eq code :header)
                             (= (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-uncertain*)))))
                 ((member-eq fault '(:event :generation'''
 if text.count(anchor)!=1:raise ValueError('member fixture conclusion drift')
 text=text.replace(anchor,replacement)
 s=lr.write(s,[(n.start,n.end,text)])
 return s+'''\n(assert-event (fn2-eamcu-test :batch-header))
(assert-event (fn2-eamcu-test :batch-commit))
(assert-event (fn2-eamcu-test :batch-tail))
'''


def arity_test(s):
 if 'import event_archive_batch_rewrite as batch' not in s:
  s=s.replace('import event_archive_member_rewrite as rw','import event_archive_member_rewrite as rw\nimport event_archive_batch_rewrite as batch')
 s=s.replace("after=acc.project('cursor', fixed.rewrite(rw.cursor(read('tools/fixtures/archive-members-before-cursor.lisp'))))", "after=batch.project_cursor(acc.project('cursor', fixed.rewrite(rw.cursor(read('tools/fixtures/archive-members-before-cursor.lisp')))))")
 s=s.replace("self.assertEqual(acc.project('cursor', fixed.rewrite(rw.cursor(after))),after)", "self.assertEqual(batch.project_cursor(acc.project('cursor', fixed.rewrite(rw.cursor(after)))),after)")
 count="  self.assertEqual(len(calls(s,'(assert-event (fn2-eamcu-test ?fault))')),7)"
 expected="  self.assertCountEqual([lr.flat(m.captures['fault']) for m in calls(s,'(assert-event (fn2-eamcu-test ?fault))')], ['nil',':event',':generation',':owner',':leaf',':accumulator-alias',':accumulator-generation',':batch-header',':batch-commit',':batch-tail',':batch-copy'])"
 if count in s:s=s.replace(count,expected)
 elif expected not in s:raise ValueError('actual fixture assertion class drift')
 old="    definitions[m.captures['name'].low]=(len(m.captures['children'].items),1+len(m.captures['outputs'].items))"
 new="""    decl=m.captures['name']
   name=decl.items[0].low if isinstance(decl,lr.Lst) else decl.low
   scalars=len(decl.items)-1 if isinstance(decl,lr.Lst) else 0
   definitions[name]=(scalars+len(m.captures['children'].items),1+len(m.captures['outputs'].items))"""
 if old not in s:
  if new in s:return s
  raise ValueError('source arity test drift')
 if s.count(old)!=1:raise ValueError('ambiguous source arity test')
 return s.replace(old,new)


def copy_body():
 return '''; Copy the exact source-owned semantic body into the existing role3
; accumulator. The first positive quantum resets it; quantum0 changes nothing.
(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-copy-step budget)
 ('''+CHILDREN+''') (fn2-event-archive fn2-pool)
 (:bytes *fn2-commit-unit-bytes*)
 (b* (((unless (and (fn2-event-archive-cold-batch-header-current-p '''+CHILDREN+''')
                    (equal (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-seal-copy*)))
       (mv :source fn2-event-archive fn2-pool))
      ((unless (and (natp budget) (<= budget *fn2-commit-unit-bytes*))) (mv :bounds fn2-event-archive fn2-pool))
      (cursor (fn2-event-archive-batch-copy-next 1 fn2-event-archive))
      (length (fn2-event-archive-batch-seal-length 1 fn2-event-archive))
      (slot (fn2-event-archive-batch-page 1 fn2-event-archive)) (gen (fn2-event-archive-batch-page-gen 1 fn2-event-archive))
      (off (fn2-event-archive-batch-seal-off 1 fn2-event-archive))
      (dst (fn2-event-archive-batch-accumulator-slot 1 fn2-event-archive)) (dgen (fn2-event-archive-batch-accumulator-gen 1 fn2-event-archive))
      (kind (fn2-event-archive-owner-kind 1 fn2-event-archive)) (owner (fn2-event-archive-owner-slot 1 fn2-event-archive)) (generation (fn2-event-archive-owner-gen 1 fn2-event-archive))
      (started (equal (fn2-event-archive-batch-copy-started 1 fn2-event-archive) 1))
      ((unless (and (posp length) (<= length *fn2-format-sealed-batch-max-size*)
                    (<= cursor length) (not (equal slot dst))
                    (eq (fn2-pool-workspace-code dst dgen kind owner generation fn2-pool) :ok)
                    (<= *fn2-commit-unit-bytes* (fn2-pool-cap dst fn2-pool))
                    (if started (equal (fn2-pool-fill dst fn2-pool) cursor) (equal cursor 0))))
       (mv :source fn2-event-archive fn2-pool))
      ((when (zp budget)) (mv :more fn2-event-archive fn2-pool))
      ((mv reset fn2-pool) (if started (mv :ok fn2-pool) (fn2-pool-reset dst dgen kind owner generation fn2-pool)))
      ((unless (eq reset :ok)) (mv reset fn2-event-archive fn2-pool))
      (count (min budget (- length cursor)))
      ((mv code fn2-pool) (fn2-pool-copy-range slot gen (+ off cursor) dst dgen cursor count kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-pool))
      (next (+ cursor count)) (complete (equal next length))
      (fn2-event-archive (fn2-event-archive-put 1 (batch-copy-started 1) (batch-copy-next next)
       (batch-phase (if complete *fn2-event-archive-batch-phase-seal-span* *fn2-event-archive-batch-phase-seal-copy*)))))
  (mv (if complete :seal-copied :more) fn2-event-archive fn2-pool)))

'''


def seal_copy(s):
 if '(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-copy-step budget)' in s:return s
 n=node(s,'(fn2-event-archive-operation fn2-event-archive-cold-member-step ?*body)')
 return lr.write(s,[(n.start,n.start,copy_body())])


def copy_fixture(s):
 if '(defun fn2-eabs-run ' in s:return s
 snapshot='(list (fn2-event-archive-copy fn2-event-archive) (fn2-pool-copy fn2-pool))'
 children=CHILDREN
 helper='''; Exact selected witness bytes, not a seal receipt. The same owner-bound
; accumulator is reused; zero quantum preserves even preexisting contents.
(defun fn2-eabs-drive (fuel '''+children+''')
 (declare (xargs :stobjs ('''+children+''') :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel fn2-event-archive fn2-pool)
  (b* ((cursor (fn2-event-archive-batch-copy-next 1 fn2-event-archive))
       ((mv code fn2-event-archive fn2-pool) (fn2-event-archive-cold-batch-seal-copy-step 1 '''+children+'''))
       (next (fn2-event-archive-batch-copy-next 1 fn2-event-archive))
       ((unless (= next (+ cursor 1))) (mv :overrun fn2-event-archive fn2-pool))
       ((unless (eq code :more)) (mv code fn2-event-archive fn2-pool)))
   (fn2-eabs-drive (- fuel 1) '''+children+'''))))
(defun fn2-eabs-run ('''+children+''')
 (declare (xargs :stobjs ('''+children+''') :verify-guards nil))
 (b* ((slot (fn2-event-archive-accumulator-slot 1 fn2-event-archive)) (gen (fn2-event-archive-accumulator-gen 1 fn2-event-archive))
      (kind (fn2-event-archive-owner-kind 1 fn2-event-archive)) (owner (fn2-event-archive-owner-slot 1 fn2-event-archive)) (generation (fn2-event-archive-owner-gen 1 fn2-event-archive))
      ((mv seed fn2-pool) (fn2-pool-write slot gen 0 77 kind owner generation fn2-pool))
      (before '''+snapshot+''')
      ((mv zero fn2-event-archive fn2-pool) (fn2-event-archive-cold-batch-seal-copy-step 0 '''+children+'''))
      ((unless (and (eq seed :ok) (eq zero :more) (equal before '''+snapshot+'''))) (mv :zero fn2-event-archive fn2-pool))
      ((mv first fn2-event-archive fn2-pool) (fn2-event-archive-cold-batch-seal-copy-step 1 '''+children+'''))
      ((unless (and (eq first :more) (= (fn2-event-archive-batch-copy-next 1 fn2-event-archive) 1) (= (fn2-pool-fill slot fn2-pool) 1))) (mv :first fn2-event-archive fn2-pool))
      (fn2-event-archive (fn2-event-archive-set-accumulator-gen 1 (+ gen 1) fn2-event-archive))
      (before '''+snapshot+''')
      ((mv stale fn2-event-archive fn2-pool) (fn2-event-archive-cold-batch-seal-copy-step 1 '''+children+'''))
      (same (equal before '''+snapshot+'''))
      (fn2-event-archive (fn2-event-archive-set-accumulator-gen 1 gen fn2-event-archive))
      ((unless (and (eq stale :source) same)) (mv :stale-control fn2-event-archive fn2-pool))
      (fn2-pool (fn2-pool-set-fill slot 2 fn2-pool))
      (before '''+snapshot+''')
      ((mv shifted fn2-event-archive fn2-pool) (fn2-event-archive-cold-batch-seal-copy-step 1 '''+children+'''))
      (same (equal before '''+snapshot+'''))
      (fn2-pool (fn2-pool-set-fill slot 1 fn2-pool))
      ((unless (and (eq shifted :source) same)) (mv :fill-control fn2-event-archive fn2-pool)))
  (fn2-eabs-drive (+ 1 (fn2-event-archive-batch-seal-length 1 fn2-event-archive)) '''+children+''')))

'''
 n=node(s,'(defun fn2-eamcu-body ?*body)');s=lr.write(s,[(n.start,n.start,helper)])
 n=node(s,'(defun fn2-eamcu-body ?*body)');text=s[n.start:n.end]
 anchor="(batch-mode (member-eq fault '(:batch-header :batch-commit :batch-tail)))"
 if text.count(anchor)!=1:raise ValueError('copy fixture producer-mode drift')
 text=text.replace(anchor,"(batch-mode (member-eq fault '(:batch-header :batch-commit :batch-tail :batch-copy)))")
 branch=node(text,'(mv-let (code fn2-event-archive fn2-fields) (fn2-eabh-run ?*args) ?*body)')
 last=branch.items[-1];old=text[last.start:last.end]
 text=lr.write(text,[(last.start,last.end,'''(if (and (eq fault :batch-copy) (eq code :header-checked))
         (mv-let (code fn2-event-archive fn2-pool) (fn2-eabs-run '''+children+''')
          '''+old+''')
         '''+old+')')])
 anchor="(cond ((member-eq fault '(:batch-header :batch-commit :batch-tail))"
 replacement='''(cond ((eq fault :batch-copy)
                  (and (eq code :seal-copied) (= (fn2-mk-size row fn2-mk) 0)
                       (= (fn2-event-archive-next-event 1 fn2-event-archive) 1)
                       (= (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-members*)
                       (= (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-seal-span*)
                       (= (fn2-event-archive-entry-pending 1 fn2-event-archive) 1)
                       (= (fn2-pool-fill accumulator fn2-pool) (fn2-event-archive-batch-seal-length 1 fn2-event-archive))
                       (equal (fn2-pool-logical-octets (fn2-event-archive-batch-seal-length 1 fn2-event-archive) (fn2-pool-base accumulator fn2-pool) fn2-pool)
                              (fn2-pool-logical-octets (fn2-event-archive-batch-seal-length 1 fn2-event-archive)
                               (+ (fn2-pool-base page fn2-pool) (fn2-event-archive-batch-seal-off 1 fn2-event-archive)) fn2-pool))))
                 ((member-eq fault '(:batch-header :batch-commit :batch-tail))'''
 if text.count(anchor)!=1:raise ValueError('copy fixture expected-result drift')
 text=text.replace(anchor,replacement)
 s=lr.write(s,[(n.start,n.end,text)])
 return s+'\n(assert-event (fn2-eamcu-test :batch-copy))\n'


def cursor_reset(s):
 n=node(s,'(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)')
 already=lr.match('(batch-phase *fn2-event-archive-batch-phase-idle*)',[n])
 if already:return s
 puts=lr.match('(fn2-event-archive-put 1 (phase *fn2-event-archive-phase-cold-manifest*) ?*fields)',[n])
 if len(puts)!=1:raise ValueError('actual cold admission reset drift')
 p=puts[0].node
 fields=' (batch-phase *fn2-event-archive-batch-phase-idle*) '+ ' '.join('('+name+' 0)' for name,_ in FIELDS)
 return lr.write(s,[(p.end-1,p.end-1,fields)])


def project_cursor(s):
 import event_archive_fixed_rows_rewrite as fixed
 import event_archive_accumulator_rewrite as acc
 import event_archive_seal_rewrite as seal
 return seal.cursor(cursor_reset(acc.cursor(fixed.rewrite(s))))


def source_test(s,name):
 if name=='event_archive_member_rewrite_test.py':return arity_test(s)
 if name=='event_archive_frontier_begin_rewrite_test.py':
  if 'import event_archive_batch_rewrite as batch' not in s:
   s=s.replace('import event_archive_member_rewrite as member','import event_archive_member_rewrite as member\nimport event_archive_batch_rewrite as batch')
  old="   after=acc.project(name, fixed.rewrite(member.cursor(after) if name=='cursor' else after))"
  new=old+"\n   after=batch.project_cursor(after) if name=='cursor' else after"
  if new not in s:
   if s.count(old)!=1:raise ValueError('frontier cursor projection drift')
   s=s.replace(old,new)
 if name=='event_archive_root_rewrite_test.py':
  if 'import event_archive_batch_rewrite as batch' not in s:
   s=s.replace('import event_archive_member_rewrite as member','import event_archive_member_rewrite as member\nimport event_archive_batch_rewrite as batch')
  s=s.replace('composed=member.cursor(frontier.cursor(after))','composed=batch.project_cursor(member.cursor(frontier.cursor(after)))')
 return s
