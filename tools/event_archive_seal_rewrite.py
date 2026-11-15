"""Reuse the actual event seal verifier over the owned original archive body.

This source component proves no original records-frame relation by itself.
Only a completed shared verifier transition produces the partial seal receipt.
"""
from pathlib import Path
import lisp_rewrite as lr
import event_archive_batch_rewrite as batch
EXTRA=[('batch-reader-started','bool'),('batch-fetch-next','u8'),('batch-fetch-acc','u32'),('batch-fetch-off','u32')]
XR=batch.CHILDREN+' fn2-event-read fn2-journal-members fn2-fc-context fn2-b3 fn2-digests fn2-extents'
OUT='fn2-event-archive fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests'
def node(s,p):return batch.node(s,p)
def state(s):
 if '(batch-reader-started :bool)' in s:return s
 n=node(s,'(batch-copy-started :bool)')
 return lr.write(s,[(n.start,n.start,' '.join('('+name+' :'+typ+')' for name,typ in EXTRA)+'\n  ')])
def cursor(s):
 if '(batch-reader-started 0)' in s:return s
 n=node(s,'(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)')
 p=lr.match('(fn2-event-archive-put 1 (phase *fn2-event-archive-phase-cold-manifest*) ?*rest)',[n])[0].node
 return lr.write(s,[(p.end-1,p.end-1,' '+ ' '.join('('+name+' 0)' for name,_ in EXTRA))])
def first_page(s):
 if '(defun fn2-event-archive-cold-batch-first-page-p ' in s:return s
 n=node(s,'(defun fn2-event-archive-cold-batch-header-current-p ?*body)')
 original=s[n.start:n.end];decl=original[original.index('(declare'):original.index('\n (and')]
 edits=[]
 patterns=['(member-equal (fn2-event-archive-batch-phase 1 fn2-event-archive) (list *fn2-event-archive-batch-phase-header* *fn2-event-archive-batch-phase-seal-copy*))',
 '(or (equal (fn2-event-archive-batch-decode-started 1 fn2-event-archive) 0) (equal (fn2-fields-decode-next work fn2-fields) (fn2-event-archive-batch-cursor 1 fn2-event-archive)))',
 '(work (* 128 (fn2-b-event-row (fn2-fc-rows fn2-fc))))']
 for pattern in patterns:
  p=node(original,pattern);edits.append((p.start,p.end,''))
 generic=lr.write(original,edits).replace('(defun fn2-event-archive-cold-batch-header-current-p ', '(defun fn2-event-archive-cold-batch-first-page-p ',1)
 anchor='   (and (<= (+ (fn2-event-archive-batch-header-off'
 if generic.count(anchor)!=1:raise ValueError('first-page source bounds drift')
 generic=generic.replace(anchor,'''   (and (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-history*) fn2-fields) (fn2-event-archive-history 1 fn2-event-archive))
        (equal (fn2-fields-value (+ eb *fn2-event-archive-member-entry-field-incarnation*) fn2-fields) (fn2-event-archive-incarnation 1 fn2-event-archive))
        (<= (+ (fn2-event-archive-batch-header-off''',1)
 wrapper='''

(defun fn2-event-archive-cold-batch-header-current-p ('''+batch.CHILDREN+''')
 '''+decl+'''
 (and (fn2-event-archive-cold-batch-first-page-p '''+batch.CHILDREN+''')
      (member-equal (fn2-event-archive-batch-phase 1 fn2-event-archive)
       (list *fn2-event-archive-batch-phase-header* *fn2-event-archive-batch-phase-seal-copy*))
      (let ((row (fn2-b-event-row (fn2-fc-rows fn2-fc))))
       (and (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)
            (or (equal (fn2-event-archive-batch-decode-started 1 fn2-event-archive) 0)
                (equal (fn2-fields-decode-next (* 128 row) fn2-fields) (fn2-event-archive-batch-cursor 1 fn2-event-archive)))))))'''
 s=lr.write(s,[(n.start,n.end,generic+wrapper)])
 geometry=node(s,'(defun fn2-event-archive-cold-batch-fields-p ?*body)')
 p=lr.match('(equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)',[geometry])[0].node
 s=lr.write(s,[(p.start,p.end,'')])
 begin=node(s,'(fn2-event-archive-operation fn2-event-archive-cold-batch-begin ?*body)')
 text=s[begin.start:begin.end]
 old='(fn2-event-archive-cold-batch-fields-p fn2-run-loads fn2-run-cursors fn2-fc fn2-fields)'
 text=text.replace(old,old+'\n                    (equal (fn2-fc-phase (fn2-b-event-row (fn2-fc-rows fn2-fc)) fn2-fc) *fn2-fc-phase-idle*)',1)
 text=text.replace('(equal event 1)', '(equal (fn2-event-archive-leaf-pending 1 fn2-event-archive) 0) (equal event 1)',1)
 text=text.replace('(batch-copy-started 0) (batch-copy-next 0)', '(batch-copy-started 0) (batch-copy-next 0) '+ ' '.join('('+name+' 0)' for name,_ in EXTRA),1)
 return '\n'.join(line.rstrip() for line in lr.write(s,[(begin.start,begin.end,text)]).splitlines())+'\n'

def source_reader():
 # These are exact actual source fields, not a copied DONE flag.
 same=[('token','source-generation'),('owner-kind','owner-kind'),('owner-slot','owner-slot'),('owner-gen','owner-gen'),
 ('cut-commit','cut-commit'),('cut-event','cut-event'),('commit','batch-commit'),('extent','batch-extent'),
 ('epoch','batch-epoch'),('allocation','batch-allocation'),('slot','batch-accumulator-slot'),('gen','batch-accumulator-gen'),
 ('journal-history','batch-history'),('journal-incarnation','batch-incarnation'),('first','batch-first')]
 comparisons='\n'.join('       (equal (fn2-event-read-'+r+' 0 fn2-event-read) (fn2-event-archive-'+a+' 1 fn2-event-archive))' for r,a in same)
 return '''(defun fn2-event-archive-cold-seal-reader-p (fn2-event-archive fn2-event-read fn2-fc)
 (declare (xargs :stobjs (fn2-event-archive fn2-event-read fn2-fc) :verify-guards nil
  :guard (and (fn2-event-archive-wfp fn2-event-archive) (fn2-event-read-wfp fn2-event-read) (fn2-fc-wfp fn2-fc))))
 (and (< 1 (fn2-event-archive-rows fn2-event-archive)) (< 0 (fn2-event-read-rows fn2-event-read))
      (equal (fn2-event-archive-batch-reader-started 1 fn2-event-archive) 1)
      (equal (fn2-event-read-pending 0 fn2-event-read) 0)
      (equal (fn2-event-read-witness-enabled 0 fn2-event-read) 0)
      (equal (fn2-event-read-checker 0 fn2-event-read) (fn2-b-event-row (fn2-fc-rows fn2-fc)))
      (equal (fn2-event-read-field-base 0 fn2-event-read) (* 128 (fn2-b-event-row (fn2-fc-rows fn2-fc))))
      (equal (fn2-event-read-body-off 0 fn2-event-read) 0)
'''+comparisons+'''))

'''


def crypto_body():
 t='''; The copied body remains provisional. Only the shared seal verifier plus
; its real digest continuation can reach RECORDS-ZERO; the original frame is
; still unverified there. No root4/prefix authority is published by this step.
(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-step budget)
 (@XR@) (@OUT@)
 (:bytes *fn2-commit-unit-bytes*)
 (b* (((unless (fn2-event-archive-cold-batch-first-page-p @FIRST@)) (mv :source @OUT@))
      (phase (fn2-event-archive-batch-phase 1 fn2-event-archive))
      ((unless (member-equal phase (list *fn2-event-archive-batch-phase-seal-span* *fn2-event-archive-batch-phase-expected* *fn2-event-archive-batch-phase-semantic*))) (mv :state @OUT@))
      ((unless (and (natp budget) (<= budget *fn2-commit-unit-bytes*))) (mv :bounds @OUT@))
      ((when (zp budget)) (mv :more @OUT@))
      (row (fn2-b-event-row (fn2-fc-rows fn2-fc))) (base (* 128 row))
      (expected (fn2-b-event-expected-digest (fn2-fc-rows fn2-fc) (fn2-extents-rows fn2-extents)))
      (previous (fn2-b-event-previous-digest (fn2-fc-rows fn2-fc) (fn2-extents-rows fn2-extents)))
      (saved-seal (fn2-b-event-root-digest (fn2-fc-rows fn2-fc) (fn2-extents-rows fn2-extents)))
      (slot (fn2-event-archive-batch-accumulator-slot 1 fn2-event-archive)) (gen (fn2-event-archive-batch-accumulator-gen 1 fn2-event-archive))
      (length (fn2-event-archive-batch-seal-length 1 fn2-event-archive))
      (kind (fn2-event-archive-owner-kind 1 fn2-event-archive)) (owner (fn2-event-archive-owner-slot 1 fn2-event-archive)) (generation (fn2-event-archive-owner-gen 1 fn2-event-archive))
      ((unless (and (< 0 (fn2-event-read-rows fn2-event-read)) (< row (fn2-fc-context-rows fn2-fc-context))
                    (fn2-b3-ready row fn2-b3 fn2-digests)
                    (fn2-digest-rowp expected fn2-digests) (unsigned-byte-p 32 expected)
                    (fn2-digest-rowp previous fn2-digests) (unsigned-byte-p 32 previous)
                    (fn2-digest-rowp saved-seal fn2-digests) (unsigned-byte-p 32 saved-seal)
                    (not (equal expected previous)) (not (equal saved-seal previous)) (not (equal saved-seal expected))
                    (<= (* *fn2-digest-stride* (fn2-fc-rows fn2-fc)) expected)
                    (<= (* *fn2-digest-stride* (fn2-fc-rows fn2-fc)) previous)
                    (<= (* *fn2-digest-stride* (fn2-fc-rows fn2-fc)) saved-seal)
                    (posp length) (<= length *fn2-format-sealed-batch-max-size*)
                    (eq (fn2-pool-workspace-code slot gen kind owner generation fn2-pool) :ok)
                    (equal (fn2-pool-fill slot fn2-pool) length))) (mv :bounds @OUT@))
      ((when (equal (fn2-event-archive-batch-reader-started 1 fn2-event-archive) 0))
       (b* (((unless (and (equal phase *fn2-event-archive-batch-phase-seal-span*)
                          (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)
                          (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-idle*)
                          (equal (fn2-event-read-pending 0 fn2-event-read) 0)
                          (equal (fn2-event-read-witness-enabled 0 fn2-event-read) 0)
                          (equal (fn2-event-archive-batch-commit 1 fn2-event-archive) 1)
                          (equal (fn2-event-archive-batch-first 1 fn2-event-archive) 1))) (mv :state @OUT@))
            ; The format's actual J1 predecessor is the zero digest. This is
            ; the fresh full-prefix constructor, never a caller supplied cut.
            (fn2-digests (fn2-digests-put previous (w0 0) (w1 0) (w2 0) (w3 0) (w4 0) (w5 0) (w6 0) (w7 0)))
            (fn2-event-read (fn2-event-read-put 0
             (phase *fn2-event-read-phase-seal-span*) (token (fn2-event-archive-source-generation 1 fn2-event-archive))
             (owner-kind kind) (owner-slot owner) (owner-gen generation)
             (cut-commit (fn2-event-archive-cut-commit 1 fn2-event-archive)) (cut-event (fn2-event-archive-cut-event 1 fn2-event-archive))
             (commit (fn2-event-archive-batch-commit 1 fn2-event-archive)) (extent (fn2-event-archive-batch-extent 1 fn2-event-archive))
             (epoch (fn2-event-archive-batch-epoch 1 fn2-event-archive)) (allocation (fn2-event-archive-batch-allocation 1 fn2-event-archive))
             (journal-history (fn2-event-archive-batch-history 1 fn2-event-archive)) (journal-incarnation (fn2-event-archive-batch-incarnation 1 fn2-event-archive))
             (history (fn2-event-archive-history 1 fn2-event-archive)) (history-incarnation (fn2-event-archive-incarnation 1 fn2-event-archive))
             (first (fn2-event-archive-batch-first 1 fn2-event-archive)) (members 0)
             (slot slot) (gen gen) (checker row) (field-base base) (pending 0) (op-slot 0) (op-gen 0)
             (body-off 0) (body-len length) (seal-span-started 0) (seal-span-next 0) (seal-span-length 0)
             (record-fetch-next 0) (record-fetch-acc 0) (record-fetch-off 0)))
            (fn2-event-archive (fn2-event-archive-put 1 (batch-reader-started 1)
             (batch-fetch-next 0) (batch-fetch-acc 0) (batch-fetch-off 0))))
        (mv :more @OUT@)))
      ((unless (fn2-event-archive-cold-seal-reader-p fn2-event-archive fn2-event-read fn2-fc)) (mv :source @OUT@))
      ((when (equal phase *fn2-event-archive-batch-phase-seal-span*))
       (b* (((mv code fn2-event-read fn2-fields) (fn2-event-read-seal-span-step budget fn2-event-read fn2-fields fn2-pool))
            ((unless (eq code :more))
             (let ((fn2-event-archive (fn2-event-archive-set-batch-phase 1 *fn2-event-archive-batch-phase-uncertain* fn2-event-archive))) (mv code @OUT@)))
            ((unless (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-semantic-seal*)) (mv :more @OUT@))
            (first (fn2-fields-value (+ base *fn2-format-sealed-batch-field-event-first*) fn2-fields))
            (last (fn2-fields-value (+ base *fn2-format-sealed-batch-field-event-last*) fn2-fields))
            (members (+ 1 (- last first)))
            (field (+ base *fn2-format-sealed-batch-field-final-seal*))
            (off (fn2-fields-ref-off field fn2-fields))
            (valid (and (equal (fn2-event-read-body-len 0 fn2-event-read) length)
                        (equal first (fn2-event-archive-batch-first 1 fn2-event-archive))
                        (posp first) (<= first last) (<= last (fn2-event-archive-cut-event 1 fn2-event-archive))
                        (posp members) (unsigned-byte-p 32 members)
                        (equal (fn2-fields-ref-slot field fn2-fields) slot) (equal (fn2-fields-ref-gen field fn2-fields) gen)
                        (equal (fn2-fields-ref-len field fn2-fields) *fn2-commit-digest-bytes*) (<= (+ off *fn2-commit-digest-bytes*) length)))
            (fn2-event-read (if valid (fn2-event-read-set-members 0 members fn2-event-read) fn2-event-read))
            (fn2-event-archive (fn2-event-archive-put 1
             (batch-phase (if valid *fn2-event-archive-batch-phase-expected* *fn2-event-archive-batch-phase-uncertain*))
             (batch-last (if valid last (fn2-event-archive-batch-last 1 fn2-event-archive)))
             (batch-fetch-next 0) (batch-fetch-acc 0) (batch-fetch-off (if valid off 0)))))
        (mv (if valid :more :seal-span) @OUT@)))
      ((unless (and (equal (fn2-event-read-body-len 0 fn2-event-read) length)
                    (equal (fn2-event-read-members 0 fn2-event-read) (+ 1 (- (fn2-event-archive-batch-last 1 fn2-event-archive) (fn2-event-archive-batch-first 1 fn2-event-archive)))))) (mv :source @OUT@))
      ((when (equal phase *fn2-event-archive-batch-phase-expected*))
       (b* ((field (+ base *fn2-format-sealed-batch-field-final-seal*))
            (off (fn2-event-archive-batch-fetch-off 1 fn2-event-archive))
            ((unless (and (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-semantic-seal*)
                          (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)
                          (equal (fn2-fields-ref-slot field fn2-fields) slot) (equal (fn2-fields-ref-gen field fn2-fields) gen)
                          (equal (fn2-fields-ref-off field fn2-fields) off) (equal (fn2-fields-ref-len field fn2-fields) *fn2-commit-digest-bytes*)
                          (<= (+ off *fn2-commit-digest-bytes*) length)
                          (fn2-rec-fetch-state-p (fn2-event-archive-batch-fetch-next 1 fn2-event-archive) (fn2-event-archive-batch-fetch-acc 1 fn2-event-archive)))) (mv :source @OUT@))
            ((mv code next acc fn2-digests) (fn2-rec-fetch-step budget (fn2-event-archive-batch-fetch-next 1 fn2-event-archive)
              (fn2-event-archive-batch-fetch-acc 1 fn2-event-archive) expected slot gen off kind owner generation fn2-pool fn2-digests))
            (complete (and (eq code :ok) (equal next *fn2-commit-digest-bytes*) (equal acc 0)))
            (fn2-event-archive (fn2-event-archive-put 1 (batch-fetch-next next) (batch-fetch-acc acc)
             (batch-phase (cond (complete *fn2-event-archive-batch-phase-semantic*) ((eq code :more) phase) (t *fn2-event-archive-batch-phase-uncertain*))))))
        (mv (if (or complete (eq code :more)) :more code) @OUT@)))
      ((unless (member-equal (fn2-event-read-phase 0 fn2-event-read) (list *fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-record-digest*))) (mv :state @OUT@))
      ((mv code fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-event-read-format-core budget expected previous fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((when (eq code :more)) (mv :more @OUT@))
      (verified (and (eq code :ok) (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-read-records*)))
      ; Leaf validation later uses EXPECTED, while ROOT retains this actual
      ; completed Jseal until records-frame verification finishes the batch.
      (fn2-digests (if verified (fn2-digest-copy saved-seal expected fn2-digests) fn2-digests))
      (fn2-event-read (if verified (fn2-event-read-set-phase 0 *fn2-event-read-phase-idle* fn2-event-read) fn2-event-read))
      (fn2-event-archive (fn2-event-archive-set-batch-phase 1
       (if verified *fn2-event-archive-batch-phase-records-zero* *fn2-event-archive-batch-phase-uncertain*) fn2-event-archive)))
  (mv (if verified :seal-checked (if (eq code :ok) :invariant code)) @OUT@)))

'''
 return t.replace('@XR@',XR).replace('@OUT@',OUT).replace('@FIRST@',batch.CHILDREN)

def members(s):
 if '(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-step budget)' in s:return s
 s=first_page(s)
 n=node(s,'(fn2-event-archive-operation fn2-event-archive-cold-member-step ?*body)')
 return lr.write(s,[(n.start,n.start,source_reader()+crypto_body())])

if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 for name,fun in [('event-archive-state',state),('event-archive-cold-cursor',cursor),('event-archive-cold-members',members)]:
  p=root/'books'/(name+'.lisp');p.write_text(fun(p.read_text()))
