; C directory-row admission before construction. Original source count is
; NOT the output-root count after schema compaction. The canonical retained
; inactive-bank scan supplies row headroom; physical B extents and working
; recipe admission remain separate real prerequisites.
(in-package "ACL2")
(include-book "checkpoint-bank-admission")
(fn2-book-layer :c)

(defun fn2-checkpoint-live-fit-step (token kind owner generation
 fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission)
 (declare (xargs :stobjs (fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission)
  :guard (and (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
              (fn2-run-installed-wfp fn2-run-installed) (fn2-checkpoint-bank-admission-wfp fn2-checkpoint-bank-admission))))
 ; Consume completed actual HELD/token/cut/active-bank/configured-geometry
 ; evidence. Never restart its scan, count originals or mint a new receipt.
 (if (fn2-checkpoint-bank-admission-ready-p token kind owner generation
       fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission)
     :fit :resources))

; Expose the SAME canonical constructor/step via the ordinary core generator.
; No local scan or new bank authority implementation is introduced.
(defcost fn2-checkpoint-live-bank-begin-op :child fn2-checkpoint-bank-admission-begin :answers t
 :steps *fn2-work-stage* :bytes 0 :descriptors 0
 :tables (fn2-core-csnapshot fn2-core-checkpoint-summary fn2-core-run-installed fn2-core-checkpoint-bank-admission)
 :doc "Begin actual HELD inactive-bank row admission before any construction allocation.")
(defcost fn2-checkpoint-live-bank-step-op :child fn2-checkpoint-bank-admission-step :answers t
 :steps *fn2-work-stage* :bytes 0 :descriptors 0
 :tables (fn2-core-csnapshot fn2-core-checkpoint-summary fn2-core-run-installed fn2-core-checkpoint-bank-admission)
 :doc "Inspect one actual inactive-bank row, retaining exact owner/cut/current-bank identity.")
(defcost fn2-checkpoint-live-fit-step-op :child fn2-checkpoint-live-fit-step :answers (:fit :resources)
 :steps *fn2-work-stage* :bytes 0 :descriptors 0
 :tables (fn2-core-csnapshot fn2-core-checkpoint-summary fn2-core-run-installed fn2-core-checkpoint-bank-admission)
 :doc "Consume canonical completed inactive-bank admission; no source count/global free-row inference.")
