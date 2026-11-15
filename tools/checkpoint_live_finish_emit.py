"""Emit bounded query-catalog promotion and sole post-rebase writer reopen.

ACL2, not this source transformation, decides identity and transition results.
Canonical directory consume remains the only authority transfer implementation.
"""
from pathlib import Path
src=Path('books/checkpoint-live-install.lisp').read_text()
a=src.index('(defun fn2-checkpoint-live-replace-install-step ')
header=src[a:src.index('\n (declare',a)]
base=header.split(' ',2)[2].rsplit(')',1)[0].split()[1:]
resources='fn2-checkpoint-summary fn2-c-source-control fn2-run-load-readiness fn2-run-load-geometry fn2-id-decides fn2-reads fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases fn2-run-load-ops fn2-ops fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-digests fn2-pool'.split()
args=list(dict.fromkeys(base+resources))
fields='phase tag candidate checkpoint cut-commit cut-event history incarnation generation semantic-tag owner-kind owner-slot owner-gen priority-base application-stage count cursor target free-count installed lease-count'.split()
b=src.index(' (b* (((unless (posp budget))',a)
b=src.index('  ((unless (and ',b);e=src.index('  (stage ',b)
rawgate=src[b:e]
# SAME actual full post-Fence/C-base/exclusive gate; no weakened authorizer.
def gate(outs):return rawgate.replace('fn2-checkpoint-summary fn2-checkpoint-metadata-manifest fn2-run-installed',' '.join(outs))
def mv(c,outs):return '(mv '+c+' '+' '.join(outs)+')'
def definition(name,params):
 return '(defun '+name+' ('+' '.join(params)+')\n (declare (xargs :stobjs ('+' '.join(params)+') :guard (and '+' '.join('('+x+'-wfp '+x+')' for x in params)+')))\n'
# Exact pending authority identity, used only BEFORE canonical consume.
auth='''(and
 (fn2-checkpoint-summary-authority-row-complete-p 1 fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
 (= (fn2-checkpoint-summary-authority-origin 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-origin-live*)
 (= (fn2-checkpoint-summary-authority-tag 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary))
 (= (fn2-checkpoint-summary-authority-generation 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary))
'''
for f in ['owner-kind','owner-slot','owner-gen','candidate','checkpoint','cut-commit','cut-event','history','incarnation']:
 auth+=' (= (fn2-checkpoint-summary-authority-'+f+' 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-'+f+' 1 fn2-checkpoint-summary))\n'
auth+=' (= (fn2-checkpoint-summary-authority-source-count 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))'
common='''(and
 (= (fn2-checkpoint-summary-installed 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary))
 (= (fn2-checkpoint-summary-lease-count 1 fn2-checkpoint-summary) 0)
 (fn2-run-load-readiness-live-complete-current-p '''+' '.join(resources)+'''))'''
s='''; Bounded query-only publication under the actual exclusive source receipt.
; SUMMARY1 survives every turn and actual directory rebase consumption.
; Canonical fn2-directory-rebase-consume ALONE transfers AUTHORITY1 to0.
; Crash before reopen loses this volatile continuation; persisted publication
; remains the recovery source. No partial summary is APPLIED/servable.
(in-package "ACL2")
(include-book "checkpoint-live-retire")
(include-book "checkpoint-directory-rebase-state")
(fn2-book-layer :c)
(defconst *fn2-live-replace-stage-promoting* 6)
(defconst *fn2-live-replace-stage-promoted* 7)
; Digest/reference validation charge retained separately from copy payload.
; The full physical-work proof for the preflight is a separate owed boundary.
(defconst *fn2-checkpoint-live-promotion-preflight-bytes* (* 8 *fn2-commit-digest-bytes*))
(defconst *fn2-checkpoint-live-promotion-bytes* (+ *fn2-checkpoint-live-promotion-preflight-bytes* 2))
(defconst *fn2-checkpoint-live-reopen-bytes* (+ *fn2-checkpoint-live-promotion-preflight-bytes* (* 2 *fn2-commit-digest-bytes*)))
; Eight component shape checks + scalar preflight and fixed generated columns.
; This declares callback charge; it is not a proved physical-work refinement.
(defconst *fn2-checkpoint-live-promotion-steps* (+ 80 8 (* 2 21) 20))
(defun fn2-checkpoint-live-copy-query-cell (i fn2-checkpoint-summary)
 (declare (xargs :stobjs fn2-checkpoint-summary
  :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (natp i) (< i 32))))
 (update-fn2-checkpoint-summary-descriptori i
  (fn2-checkpoint-summary-descriptori (+ *fn2-commit-digest-bytes* i) fn2-checkpoint-summary) fn2-checkpoint-summary))
; A terminal read-only comparison, never a copier or authority transfer.
(defun fn2-checkpoint-live-query-descriptor-p (i fn2-checkpoint-summary)
 (declare (xargs :stobjs fn2-checkpoint-summary :measure (nfix (- 32 (nfix i)))
  :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (natp i) (<= i 32))))
 (or (>= (nfix i) 32)
  (and (= (fn2-checkpoint-summary-descriptori i fn2-checkpoint-summary)
          (fn2-checkpoint-summary-descriptori (+ 32 i) fn2-checkpoint-summary))
       (fn2-checkpoint-live-query-descriptor-p (+ 1 i) fn2-checkpoint-summary))))
(defmacro fn2-checkpoint-live-finish-events ()
 '(progn
'''
outs=['fn2-checkpoint-summary','fn2-checkpoint-summary-authority']
s+=definition('fn2-checkpoint-live-replace-finish',args)
s+=' (b* ('+gate(outs).lstrip()+'''  ((unless (and '''+common+' '+auth+''')) '''+mv(':source',outs)+''')
  (stage (fn2-checkpoint-summary-application-stage 1 fn2-checkpoint-summary))
  (i (fn2-checkpoint-summary-cursor 1 fn2-checkpoint-summary)))
  (cond
   ((= stage *fn2-live-replace-stage-resources*)
    (b* (((unless (and (= (fn2-checkpoint-summary-installed 0 fn2-checkpoint-summary) 0)
                       (= (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 0)
                       (or (= (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) 0)
                           (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-retired*))
                       (or (= (fn2-checkpoint-summary-authority-catalog-tag 1 fn2-checkpoint-summary-authority) 0)
                           (= (fn2-checkpoint-summary-authority-catalog-tag 1 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary)))))
           '''+mv(':source',outs)+''')
         ; Retire the query authority BEFORE the first partial descriptor write.
         ; No AUTHORITY bytes/phase are changed here; sole consume owns them.
         (fn2-checkpoint-summary-authority (fn2-checkpoint-summary-authority-set-catalog-tag 1 (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary) fn2-checkpoint-summary-authority))
         (fn2-checkpoint-summary (fn2-checkpoint-summary-put 0 (phase *fn2-checkpoint-summary-phase-promoting*)))
         (fn2-checkpoint-summary (fn2-checkpoint-summary-put 1 (application-stage *fn2-live-replace-stage-promoting*) (cursor 0))))
     '''+mv(':more',outs)+'''))
   ((= stage *fn2-live-replace-stage-promoting*)
    (b* (((unless (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-promoting*)) '''+mv(':source',outs)+''')
         ((when (< i *fn2-commit-digest-bytes*))
          (b* ((fn2-checkpoint-summary (fn2-checkpoint-live-copy-query-cell i fn2-checkpoint-summary))
               (fn2-checkpoint-summary (fn2-checkpoint-summary-set-cursor 1 (+ 1 i) fn2-checkpoint-summary))) '''+mv(':more',outs)+'''))
         ((unless (= i *fn2-commit-digest-bytes*)) '''+mv(':bounds',outs)+''')
         (fn2-checkpoint-summary (fn2-checkpoint-summary-put 0
'''
for f in fields:
 v='*fn2-checkpoint-summary-phase-promoting*' if f=='phase' else '(fn2-checkpoint-summary-'+f+' 1 fn2-checkpoint-summary)'
 s+='          ('+f+' '+v+')\n'
s+='''         ))
         (fn2-checkpoint-summary (fn2-checkpoint-summary-set-application-stage 1 *fn2-live-replace-stage-promoted* fn2-checkpoint-summary)))
     '''+mv(':promoted',outs)+'''))
   (t '''+mv(':state',outs)+'''))))
'''
# Reopen consumes actual canonical rebase result, never accepts pendingCOMPLETE.
reopenargs=args+['fn2-directory-rebase']
routs=['fn2-checkpoint-summary','fn2-id-engine','fn2-seals','fn2-c-source-control']
s+=definition('fn2-checkpoint-live-replace-reopen',reopenargs)
s+=' (b* ('+gate(routs).lstrip()+'''  ((unless (and '''+common+'''
   (= (fn2-checkpoint-summary-application-stage 1 fn2-checkpoint-summary) *fn2-live-replace-stage-promoted*)
   (= (fn2-checkpoint-summary-cursor 1 fn2-checkpoint-summary) *fn2-commit-digest-bytes*)
   (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-promoting*)
   (fn2-checkpoint-live-query-descriptor-p 0 fn2-checkpoint-summary)
   (< 0 (fn2-directory-rebase-rows fn2-directory-rebase))
   (= (fn2-directory-rebase-phase 0 fn2-directory-rebase) *fn2-directory-rebase-phase-committed*)
   (= (fn2-checkpoint-summary-authority-phase 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-phase-idle*)
   (= (fn2-checkpoint-summary-authority-origin 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-origin-none*)
   (= (fn2-checkpoint-summary-authority-cursor 1 fn2-checkpoint-summary-authority) 0)
   (fn2-checkpoint-summary-authority-row-complete-p 0 fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
   (= (fn2-checkpoint-summary-authority-origin 0 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-origin-live*)
   (= (fn2-checkpoint-summary-authority-catalog-tag 0 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary))
'''
for f in ['candidate','checkpoint','history','incarnation','cut-commit','cut-event','generation','owner-kind','owner-slot','owner-gen']:
 s+='   (= (fn2-checkpoint-summary-authority-'+f+' 0 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-'+f+' 1 fn2-checkpoint-summary))\n'
for f,q in [('token','generation'),('owner-kind','owner-kind'),('owner-slot','owner-slot'),('owner-gen','owner-gen'),('candidate','candidate'),('checkpoint','checkpoint'),('history','history'),('incarnation','incarnation'),('target','cut-commit'),('target-event','cut-event')]:
 s+='   (= (fn2-directory-rebase-'+f+' 0 fn2-directory-rebase) (fn2-checkpoint-summary-'+q+' 1 fn2-checkpoint-summary))\n'
for f in fields:
 if f not in ['phase','application-stage']:
  s+='   (= (fn2-checkpoint-summary-'+f+' 0 fn2-checkpoint-summary) (fn2-checkpoint-summary-'+f+' 1 fn2-checkpoint-summary))\n'
s+='''   (= (fn2-commit-root-base-batch 0 fn2-commit-root) (fn2-checkpoint-summary-cut-commit 1 fn2-checkpoint-summary))
   (= (fn2-commit-root-base-event 0 fn2-commit-root) (fn2-checkpoint-summary-cut-event 1 fn2-checkpoint-summary))
   (< 0 (fn2-id-engine-rows fn2-id-engine)) (< 0 (fn2-seals-rows fn2-seals))
   (unsigned-byte-p 60 (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))
   (<= (fn2-id-engine-seq 0 fn2-id-engine) (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))
   (<= (fn2-seals-runs 0 fn2-seals) (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary))))) '''+mv(':source',routs)+''')
  ; Every refusal precedes the fixed scalar-only mutation sequence.
  (fn2-id-engine (fn2-id-engine-put 0 (seq (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)))
   (published (max (fn2-id-engine-published 0 fn2-id-engine) (fn2-checkpoint-summary-cut-event 1 fn2-checkpoint-summary)))))
  (fn2-seals (fn2-seals-set-runs 0 (+ (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary)) fn2-seals))
  (fn2-checkpoint-summary (fn2-checkpoint-summary-set-phase 0 *fn2-checkpoint-summary-phase-applied* fn2-checkpoint-summary))
  (fn2-checkpoint-summary (fn2-checkpoint-summary-put 1
'''
for f in fields:s+='   ('+f+' '+('*fn2-checkpoint-summary-phase-idle*' if f=='phase' else '0')+')\n'
s+='''  ))
  (fn2-c-source-control (fn2-c-source-control-put 0
   (phase *fn2-c-source-writer-phase-idle*) (writer-kind 0) (writer-owner 0) (writer-gen 0)
   (writer-token 0) (cut-commit 0) (cut-event 0) (wake-pending 0))))
  '''+mv(':applied',routs)+'''))
))
'''
for name,params,cost,answers in [('finish',args,'promotion',':source :state :bounds :more :promoted'),('reopen',reopenargs,'reopen',':source :applied')]:
 s+='(defcost fn2-checkpoint-live-replace-'+name+'-op :child fn2-checkpoint-live-replace-'+name+' :answers ('+answers+')\n :steps *fn2-checkpoint-live-promotion-steps* :bytes *fn2-checkpoint-live-'+cost+'-bytes* :descriptors 0\n :tables ('+' '.join(('fn2-core-checkpoint-directory-rebase' if x=='fn2-directory-rebase' else x.replace('fn2-','fn2-core-',1)) for x in params)+')\n :doc "Actual exclusive query promotion/reopen; canonical rebase alone transfers authority; no new allocation or IO.")\n'
Path('books/checkpoint-live-finish.lisp').write_text(s)
