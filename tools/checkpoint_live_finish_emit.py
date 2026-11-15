from pathlib import Path
import re
src=Path('books/checkpoint-live-install.lisp').read_text();a=src.index('(defun fn2-checkpoint-live-replace-install-step ');header=src[a:src.index('\n (declare',a)];base=header.split(' ',2)[2].rsplit(')',1)[0].split()[1:]
resources='fn2-checkpoint-summary fn2-c-source-control fn2-run-load-readiness fn2-run-load-geometry fn2-id-decides fn2-reads fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-run-load-ops fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool'.split()
args=list(dict.fromkeys(base+resources))
outs='fn2-checkpoint-summary fn2-checkpoint-summary-authority fn2-id-engine fn2-seals fn2-c-source-control'
def mv(c):return '(mv '+c+' '+outs+')'
b=src.index(' (b* (((unless (posp budget))',a);e=src.index('  (stage ',b);gate=src[b:e];gate=gate[gate.index('      ((unless '):] if False else gate
# Reuse exact full typed installation authority; final has no budget/yield.
gate=gate[gate.index('  ((unless '):] if '  ((unless ' in gate else gate
# robust extract source/current unless binding with balanced text boundaries.
start=src.index('  ((unless (and ',b)
end=src.index('  (stage ',start)
gate=src[start:end].replace('fn2-checkpoint-summary fn2-checkpoint-metadata-manifest fn2-run-installed',outs)
summaryfields='phase tag candidate checkpoint cut-commit cut-event history incarnation generation semantic-tag owner-kind owner-slot owner-gen priority-base application-stage count cursor target free-count installed lease-count'.split()
authfields='phase origin tag candidate checkpoint cut-commit cut-event history incarnation generation catalog-tag source-count source-observation cursor owner-kind owner-slot owner-gen'.split()
s='''; Fixed-size terminal for actual completed live replacement. This is emitted
; only after the actual live loader provider/actor plan is available. It does
; not construct readiness or select a catalog; every antecedent is an actual
; producer, replacement, C-base, old drain or maintained scan result.
; The caller carries the source observer count invariant. Endpoint rows and
; next-receipt are never reset. No new allocation, IO or bounded traversal.
(in-package "ACL2")
(include-book "checkpoint-live-retire")
(fn2-book-layer :c)
(defconst *fn2-checkpoint-live-promotion-bytes*
 (+ *fn2-event-frontier-bytes* (* 3 *fn2-commit-digest-bytes*)))
; Fixed representation: 32 descriptor octets + 480 frontier words + 8 cutseal.
(defun fn2-checkpoint-live-promote-evidence (i fn2-checkpoint-summary fn2-checkpoint-summary-authority)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-summary-authority)
  :measure (nfix (- 520 (nfix i)))
  :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
              (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority)
              (natp i) (<= i 520))))
 (if (>= (nfix i) 520) (mv fn2-checkpoint-summary fn2-checkpoint-summary-authority)
  (b* ((fn2-checkpoint-summary
        (if (< i 32) (update-fn2-checkpoint-summary-descriptori i
          (fn2-checkpoint-summary-descriptori (+ 32 i) fn2-checkpoint-summary) fn2-checkpoint-summary)
         fn2-checkpoint-summary))
       (fn2-checkpoint-summary-authority
        (cond ((< i 32) (update-fn2-checkpoint-summary-authority-descriptori i
                (fn2-checkpoint-summary-authority-descriptori (+ 32 i) fn2-checkpoint-summary-authority) fn2-checkpoint-summary-authority))
              ((< i 512) (update-fn2-checkpoint-summary-authority-frontieri (- i 32)
                (fn2-checkpoint-summary-authority-frontieri (+ 480 (- i 32)) fn2-checkpoint-summary-authority) fn2-checkpoint-summary-authority))
              (t (update-fn2-checkpoint-summary-authority-cut-seali (- i 512)
                (fn2-checkpoint-summary-authority-cut-seali (+ 8 (- i 512)) fn2-checkpoint-summary-authority) fn2-checkpoint-summary-authority)))))
   (fn2-checkpoint-live-promote-evidence (+ 1 i) fn2-checkpoint-summary fn2-checkpoint-summary-authority))))
(defmacro fn2-checkpoint-live-finish-events ()
 '(progn
'''
s+='(defun fn2-checkpoint-live-replace-finish ('+' '.join(args)+')\n'
s+=' (declare (xargs :stobjs ('+' '.join(args)+') :guard (and '+' '.join('('+x+'-wfp '+x+')' for x in args)+')))\n'
s+=' (b* ('+gate.lstrip()+'''  ((unless (and
    (= (fn2-checkpoint-summary-application-stage 1 fn2-checkpoint-summary) *fn2-live-replace-stage-resources*)
    (= (fn2-checkpoint-summary-installed 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary))
    (= (fn2-checkpoint-summary-lease-count 1 fn2-checkpoint-summary) 0)
    (= (fn2-checkpoint-summary-installed 0 fn2-checkpoint-summary) 0)
    (= (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 0)
    (or (= (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) 0)
        (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-retired*))
    (fn2-checkpoint-summary-authority-row-current-p 1 fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
    (= (fn2-checkpoint-summary-authority-phase 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-phase-complete*)
    (= (fn2-checkpoint-summary-authority-origin 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-origin-live*)
    (= (fn2-checkpoint-summary-authority-generation 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary))
    (= (fn2-checkpoint-summary-authority-owner-kind 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-owner-kind 1 fn2-checkpoint-summary))
    (= (fn2-checkpoint-summary-authority-owner-slot 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-owner-slot 1 fn2-checkpoint-summary))
    (= (fn2-checkpoint-summary-authority-owner-gen 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-owner-gen 1 fn2-checkpoint-summary))
    (= (fn2-checkpoint-summary-authority-tag 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary))
    (= (fn2-checkpoint-summary-authority-cursor 1 fn2-checkpoint-summary-authority) 488)
    (= (fn2-checkpoint-summary-authority-source-count 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary))
    (fn2-run-load-readiness-live-complete-current-p '''+' '.join(resources)+''')
    (< 0 (fn2-id-engine-rows fn2-id-engine)) (< 0 (fn2-seals-rows fn2-seals))
    (unsigned-byte-p 60 (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))
    (<= (fn2-id-engine-seq 0 fn2-id-engine) (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))
    (<= (fn2-seals-runs 0 fn2-seals) (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))))
   '''+mv(':source')+''')
  ; All refusal and scalar overflow checks precede the first mutation.
  ((mv fn2-checkpoint-summary fn2-checkpoint-summary-authority)
   (fn2-checkpoint-live-promote-evidence 0 fn2-checkpoint-summary fn2-checkpoint-summary-authority))
  (fn2-id-engine (fn2-id-engine-put 0 (seq (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))
   (published (max (fn2-id-engine-published 0 fn2-id-engine) (fn2-checkpoint-summary-cut-event 1 fn2-checkpoint-summary)))))
  (fn2-seals (fn2-seals-set-runs 0 (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)) fn2-seals))
  (fn2-checkpoint-summary-authority (fn2-checkpoint-summary-authority-put 0
'''
for f in authfields:
 value='(fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary)' if f=='catalog-tag' else f'(fn2-checkpoint-summary-authority-{f} 1 fn2-checkpoint-summary-authority)'
 s+=f'   ({f} {value})\n'
s+='''  ))
  (fn2-checkpoint-summary (fn2-checkpoint-summary-put 0
'''
for f in summaryfields:
 value='*fn2-checkpoint-summary-phase-applied*' if f=='phase' else f'(fn2-checkpoint-summary-{f} 1 fn2-checkpoint-summary)'
 s+=f'   ({f} {value})\n'
s+='''  ))
  (fn2-checkpoint-summary (fn2-checkpoint-summary-put 1
'''+ '\n'.join('   ('+f+' '+('*fn2-checkpoint-summary-phase-idle*' if f=='phase' else '0')+')' for f in summaryfields)+'''
  ))
  ; Sole typed reopen. Preserve next-receipt and readers0; no endpoint reset.
  (fn2-c-source-control (fn2-c-source-control-put 0
   (phase *fn2-c-source-writer-phase-idle*) (writer-kind 0) (writer-owner 0)
   (writer-gen 0) (writer-token 0) (cut-commit 0) (cut-event 0) (wake-pending 0))))
  '''+mv(':applied')+'''))
))
(defcost fn2-checkpoint-live-replace-finish-op :child fn2-checkpoint-live-replace-finish :answers (:source :applied)
 :steps *fn2-work-stage* :bytes *fn2-checkpoint-live-promotion-bytes* :descriptors 0
 :tables ('''+ ' '.join(x.replace('fn2-','fn2-core-',1) for x in args)+''')
 :doc "Promote actual complete exclusive live replacement and reopen its writer in the same fixed-size transition.")
'''
Path('books/checkpoint-live-finish.lisp').write_text(s)
