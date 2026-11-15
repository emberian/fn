; A fresh ordinary prefix delegates output to the canonical checkpoint writer.
; Existing prefixes keep their original observer and drain before HELD.
(in-package "ACL2")
(include-book "sealer-physical-loader")
(include-book "checkpoint-predecessors-state")
(fn2-book-layer :c)

(defun fn2-sealer-checkpoint-work-p
 (fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases)
 :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
             (fn2-pool-wfp fn2-pool) (fn2-run-loads-wfp fn2-run-loads) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases))))
 (and (< 0 (fn2-seals-rows fn2-seals))
      (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-idle*)
      (equal (fn2-seals-held 0 fn2-seals) 0)
      (equal (fn2-seals-source-receipt 0 fn2-seals) 0)
      (fn2-sealer-loader-free-p fn2-seals fn2-run-loads fn2-checkpoint-summary-leases)
      (let* ((rows (fn2-overlays-rows fn2-overlays))
             (o (fn2-seal-pick rows 0 rows fn2-overlays)))
       (or (and (< o rows) (posp (fn2-overlays-count o fn2-overlays)))
           (<= 2 (mv-nth 1 (fn2-seal-compact-target fn2-run-installed fn2-pool)))))))

; The postpublication continuation checks the actual adopted generation and
; original retirement terminal, rather than treating a wake as completion.
(defun fn2-sealer-checkpoint-resumed-p
 (old-tag fn2-seals fn2-run-loads fn2-checkpoint-summary-leases fn2-checkpoint-summary
          fn2-checkpoint-predecessor-control fn2-csnapshot fn2-c-source-control)
 (declare (xargs :stobjs (fn2-seals fn2-run-loads fn2-checkpoint-summary-leases fn2-checkpoint-summary
 fn2-checkpoint-predecessor-control fn2-csnapshot fn2-c-source-control)
 :guard (and (natp old-tag) (fn2-seals-wfp fn2-seals) (fn2-run-loads-wfp fn2-run-loads)
 (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
 (fn2-checkpoint-predecessor-control-wfp fn2-checkpoint-predecessor-control)
 (fn2-csnapshot-wfp fn2-csnapshot) (fn2-c-source-control-wfp fn2-c-source-control))))
 (and (< 0 (fn2-seals-rows fn2-seals)) (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
      (< 0 (fn2-checkpoint-predecessor-control-rows fn2-checkpoint-predecessor-control))
      (< 0 (fn2-csnapshot-rows fn2-csnapshot)) (< 0 (fn2-c-source-control-rows fn2-c-source-control))
      (= (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-idle*) (= (fn2-seals-held 0 fn2-seals) 0)
      (= (fn2-seals-source-receipt 0 fn2-seals) 0)
      (fn2-sealer-loader-free-p fn2-seals fn2-run-loads fn2-checkpoint-summary-leases)
      (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*)
      (= (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-idle*)
      (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)
      (< old-tag (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary))
      (= (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control) *fn2-checkpoint-predecessor-phase-done*)
      (= (fn2-checkpoint-summary-generation 0 fn2-checkpoint-summary) (fn2-checkpoint-predecessor-control-token 0 fn2-checkpoint-predecessor-control))
      (= (fn2-checkpoint-summary-candidate 0 fn2-checkpoint-summary) (fn2-checkpoint-predecessor-control-candidate 0 fn2-checkpoint-predecessor-control))
      (= (fn2-checkpoint-summary-owner-kind 0 fn2-checkpoint-summary) (fn2-checkpoint-predecessor-control-owner-kind 0 fn2-checkpoint-predecessor-control))
      (= (fn2-checkpoint-summary-owner-slot 0 fn2-checkpoint-summary) (fn2-checkpoint-predecessor-control-owner-slot 0 fn2-checkpoint-predecessor-control))
      (= (fn2-checkpoint-summary-owner-gen 0 fn2-checkpoint-summary) (fn2-checkpoint-predecessor-control-owner-gen 0 fn2-checkpoint-predecessor-control))
      (= (fn2-checkpoint-summary-cut-commit 0 fn2-checkpoint-summary) (fn2-checkpoint-predecessor-control-cut-commit 0 fn2-checkpoint-predecessor-control))
      (= (fn2-checkpoint-summary-cut-event 0 fn2-checkpoint-summary) (fn2-checkpoint-predecessor-control-cut-event 0 fn2-checkpoint-predecessor-control))
      (= (fn2-checkpoint-predecessor-control-completed-originals 0 fn2-checkpoint-predecessor-control)
         (fn2-checkpoint-predecessor-control-count 0 fn2-checkpoint-predecessor-control))))
