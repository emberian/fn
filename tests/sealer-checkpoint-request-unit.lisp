; Prepared, unexecuted lower admission control. Overlay bytes are produced by
; the existing real load/insert/freeze fixture. The negative phase/receipt/loan
; perturbations are deliberate guard-removal controls, not a publication proof.
; This does not seed APPLIED/READY or claim a complete checkpoint roundtrip.
(in-package "ACL2")
(include-book "sealer-unit")
(include-book "../books/sealer-checkpoint-request")

(defmacro fn2-scrq-events ()
 (let ((stobjs (append *fn2-su-stobjs* '(fn2-run-loads fn2-checkpoint-summary-leases))))
 `(progn
   (defun fn2-scrq-lower (,@stobjs)
    (declare (xargs :stobjs ,stobjs :verify-guards nil))
    (b* (((mv code ,@*fn2-su-stobjs*) (fn2-su-setup 2 *fn2-run-page-size* ,@*fn2-su-stobjs*))
         ((unless (eq code :ok)) (mv nil ,@stobjs))
         (fn2-run-loads (fn2-run-loads-init (fn2-run-cursors-rows fn2-run-cursors) fn2-run-loads))
         (fn2-checkpoint-summary-leases (fn2-checkpoint-summary-leases-init (fn2-run-cursors-rows fn2-run-cursors) fn2-checkpoint-summary-leases))
         (empty (fn2-sealer-checkpoint-work-p fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases))
         ((mv code ,@*fn2-su-stobjs*)
          (fn2-su-load 8 *fn2-su-groups* (list (fn2-su-batch 0 1 100)) 0 '(1) nil ,@*fn2-su-stobjs*))
         ((unless (eq code :ok)) (mv nil ,@stobjs))
         (wanted (fn2-sealer-checkpoint-work-p fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases))
         (fn2-seals (fn2-seals-set-source-receipt 0 1 fn2-seals))
         (receipt-blocked (not (fn2-sealer-checkpoint-work-p fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases)))
         (fn2-seals (fn2-seals-put 0 (source-receipt 0) (phase *fn2-seal-phase-build*)))
         (active-blocked (not (fn2-sealer-checkpoint-work-p fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases)))
         (fn2-seals (fn2-seals-put 0 (phase *fn2-seal-phase-idle*) (prefix-page-live 1)))
         (loan-blocked (not (fn2-sealer-checkpoint-work-p fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases))))
     (mv (and (not empty) wanted receipt-blocked active-blocked loan-blocked) ,@stobjs)))
   (defun fn2-scrq-control ()
    (declare (xargs :verify-guards nil))
    (fn2-run-with-local ,stobjs
     (mv-let (good ,@stobjs) (fn2-scrq-lower ,@stobjs) (mv good ,@stobjs))))
   (assert-event (fn2-scrq-control)))))
(fn2-scrq-events)
