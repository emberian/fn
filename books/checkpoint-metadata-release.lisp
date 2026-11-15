; Release volatile root1 working storage only after the actual publisher's
; final fence result, for the same installed candidate and retained builder.
; This does not release allocator retention edges or authorize FREE.
(in-package "ACL2")
(include-book "checkpoint-working-release")
(include-book "checkpoint-source-loader")
(include-book "checkpoint-publication")
(fn2-book-layer :c)

; Shared physical working-lease cleanup. Callers establish publication or
; preconstruction-abort permission; this helper checks exact retained ownership.




(defun fn2-checkpoint-root1-release (budget kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest
                                    fn2-checkpoint-build fn2-checkpoints fn2-checkpoint-publication fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest fn2-checkpoint-build
                          fn2-checkpoints fn2-checkpoint-publication fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases)
  :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-windows-wfp fn2-checkpoint-windows)
              (fn2-checkpoint-metadata-manifest-wfp fn2-checkpoint-metadata-manifest) (fn2-checkpoint-build-wfp fn2-checkpoint-build)
              (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)
              (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control)
              (fn2-checkpoint-future-wfp fn2-checkpoint-future) (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases))))
 (b* (((unless (and (natp budget) (< 0 budget)))
       (mv :yield fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows))
      ((unless (and (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
                    (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
                    (< 0 (fn2-checkpoint-metadata-manifest-rows fn2-checkpoint-metadata-manifest))
                    (< 0 (fn2-checkpoint-build-rows fn2-checkpoint-build))
                    (< 0 (fn2-checkpoint-publication-rows fn2-checkpoint-publication))
                    (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-complete*)
                    (fn2-checkpoint-source-reader-detachedp fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases)
                    (equal kind (fn2-checkpoint-root1-owner-kind 0 fn2-checkpoint-root1))
                    (equal owner (fn2-checkpoint-root1-owner-slot 0 fn2-checkpoint-root1))
                    (equal gen (fn2-checkpoint-root1-owner-gen 0 fn2-checkpoint-root1))
                    (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-ready*)
                    (equal (fn2-checkpoint-build-snapshot-token 0 fn2-checkpoint-build) (fn2-checkpoint-root1-token 0 fn2-checkpoint-root1))
                    (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication) *fn2-checkpoint-publication-phase-complete*)))
       (mv :pending fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows))
      (c (fn2-checkpoint-build-candidate 0 fn2-checkpoint-build))
      ((unless (and (fn2-checkpoint-builder-claimp c (fn2-checkpoint-root1-token 0 fn2-checkpoint-root1) kind owner gen fn2-checkpoints)
                    (equal c (fn2-checkpoint-publication-candidate 0 fn2-checkpoint-publication))
                    (equal (fn2-checkpoint-build-checkpoint 0 fn2-checkpoint-build) (fn2-checkpoints-checkpoint c fn2-checkpoints))
                    (posp (fn2-checkpoints-installation-commit c fn2-checkpoints))
                    (member (fn2-checkpoints-state c fn2-checkpoints)
                     (list *fn2-checkpoint-state-installed* *fn2-checkpoint-state-promoting* *fn2-checkpoint-state-promoted*))))
       (mv :candidate fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows))
      ((unless (and (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
                     (equal (fn2-checkpoint-publication-bundle-released 0 fn2-checkpoint-publication) 1)
                     (equal c (fn2-checkpoint-future-candidate 0 fn2-checkpoint-future))
                     (equal (fn2-checkpoint-root1-token 0 fn2-checkpoint-root1) (fn2-checkpoint-future-token 0 fn2-checkpoint-future))
                     (equal kind (fn2-checkpoint-future-owner-kind 0 fn2-checkpoint-future))
                     (equal owner (fn2-checkpoint-future-owner-slot 0 fn2-checkpoint-future))
                     (equal gen (fn2-checkpoint-future-owner-gen 0 fn2-checkpoint-future))))
       (mv :candidate fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows)))
  (fn2-checkpoint-working-release-step budget c kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows)))

(fn2-checkpoint-root1-preserves fn2-checkpoint-root1-release
 (budget kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata-manifest fn2-checkpoint-build fn2-checkpoints fn2-checkpoint-publication fn2-pool fn2-control fn2-checkpoint-future fn2-checkpoint-future-windows fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases)
 :hyps ((fn2-checkpoint-futurep fn2-checkpoint-future) (fn2-checkpoint-future-wfp fn2-checkpoint-future)
        (fn2-checkpoint-future-windowsp fn2-checkpoint-future-windows) (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-windows-wfp fn2-checkpoint-windows)
        (fn2-checkpoint-metadata-manifest-wfp fn2-checkpoint-metadata-manifest) (fn2-checkpoint-build-wfp fn2-checkpoint-build)
        (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-publication-wfp fn2-checkpoint-publication)
        (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control) (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases))
  :specs (("-FUTURE-TYPE" fn2-checkpoint-futurep 6) ("-FUTURE-WFP" fn2-checkpoint-future-wfp 6)
         ("-FUTURE-ROWS" fn2-checkpoint-future-rows 6 :frame fn2-checkpoint-future)
         ("-FUTURE-WINDOWS-TYPE" fn2-checkpoint-future-windowsp 7) ("-FUTURE-WINDOWS-WFP" fn2-checkpoint-future-windows-wfp 7)
         ("-FUTURE-WINDOWS-ROWS" fn2-checkpoint-future-windows-rows 7 :frame fn2-checkpoint-future-windows)
("-CHECKPOINT-ROOT1-TYPE" fn2-checkpoint-root1p 1) ("-CHECKPOINT-ROOT1-WFP" fn2-checkpoint-root1-wfp 1)
         ("-CHECKPOINT-ROOT1-ROWS" fn2-checkpoint-root1-rows 1 :frame fn2-checkpoint-root1)
         ("-CHECKPOINT-WINDOWS-TYPE" fn2-checkpoint-windowsp 2) ("-CHECKPOINT-WINDOWS-WFP" fn2-checkpoint-windows-wfp 2)
         ("-CHECKPOINT-WINDOWS-ROWS" fn2-checkpoint-windows-rows 2 :frame fn2-checkpoint-windows)
         ("-MANIFEST-TYPE" fn2-checkpoint-metadata-manifestp 3) ("-MANIFEST-WFP" fn2-checkpoint-metadata-manifest-wfp 3)
         ("-MANIFEST-ROWS" fn2-checkpoint-metadata-manifest-rows 3 :frame fn2-checkpoint-metadata-manifest)
         ("-POOL-TYPE" fn2-poolp 4) ("-POOL-WFP" fn2-pool-wfp 4) ("-POOL-ROWS" fn2-pool-rows 4 :frame fn2-pool)
         ("-POOL-DATA" fn2-pool-data-length 4 :frame fn2-pool)
         ("-CONTROL-TYPE" fn2-controlp 5) ("-CONTROL-WFP" fn2-control-wfp 5) ("-CONTROL-ROWS" fn2-control-rows 5 :frame fn2-control)))
(defcost fn2-checkpoint-root1-release-op :child fn2-checkpoint-root1-release :answers t
 :tables (fn2-core-checkpoint-root1 fn2-core-checkpoint-windows fn2-core-checkpoint-metadata-manifest fn2-core-checkpoint-build
           fn2-core-checkpoints fn2-core-checkpoint-publication fn2-core-pool fn2-core-control fn2-core-checkpoint-future fn2-core-checkpoint-future-windows fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary-leases)
 :doc "After the actual same-candidate publication fence, release one owned future or root1 window; aggregate completion covers all working windows, never allocator retention.")
