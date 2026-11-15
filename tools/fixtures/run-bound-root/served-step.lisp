; Source-only actual provider 41a2e1dcd6e347ea45da7e5b1c5e8f6ac0a1b813; never included by an ACL2 book.
; The same format verifier used at cold recovery authenticates all 64KiB
; before a physical cursor can enter the existing generated header path.
(in-package "ACL2")
(include-book "run-physical-io")
(include-book "run-physical-bound-step")
(fn2-book-layer :c)


(defun fn2-run-load-step (c budget fn2-run-loads fn2-run-cursors
 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-boot-config
 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors)
  (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources)
  (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-run-installed-wfp fn2-run-installed)
  (fn2-boot-config-wfp fn2-boot-config) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
  (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (cond ((not (and (posp budget) (<= budget *fn2-commit-unit-bytes*))) (fn2-run-load-step-mv :yield))
       ((not (fn2-run-load-sourcep c fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed)) (fn2-run-load-step-mv :source))
       (t (fn2-run-bound-step c budget fn2-run-loads fn2-run-cursors fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))

(fn2-run-load-frames fn2-run-load-step
 (c budget fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 ((fn2-run-loads 1) (fn2-run-cursors 2) (fn2-fc 3) (fn2-fc-context 4) (fn2-b3 5) (fn2-fields 6) (fn2-pool 7) (fn2-digests 8)))
