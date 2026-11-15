; Actual same-SIM multi-generation publication support. This helper observes
; canonical typed promotion/rebase/reopen and ordinary master cleanup; it
; never sets APPLIED, bank, authority, phase, protection or persistence state.
; Complete runtime master/compactor/bank providers are prerequisites. Source
; only: no whole two-cut or DELETE execution claim is made by this book.
(in-package "ACL2")
(include-book "checkpoint-live-network-prefix-support")
(include-book "../books/checkpoint-cbase-identity")

(defun fn2-clt-completed-p (checkpoint fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (and (posp checkpoint) (fn2-ccp-live-complete-p t 0 fn2-core)
  (stobj-let ((fn2-checkpoint-summary (fn2-core-checkpoint-summary fn2-core))
              (fn2-checkpoint-summary-authority (fn2-core-checkpoint-summary-authority fn2-core))
              (fn2-checkpoint-cbase-holds (fn2-core-checkpoint-cbase-holds fn2-core))
              (fn2-checkpoints (fn2-core-checkpoints fn2-core))
              (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
              (fn2-checkpoint-bytes (fn2-core-checkpoint-bytes fn2-core))
              (fn2-csnapshot (fn2-core-csnapshot fn2-core))
              (fn2-extents (fn2-core-extents fn2-core))
              (fn2-c-source-control (fn2-core-c-source-control fn2-core))) (complete)
   (and (< 1 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
        (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)
        (= (fn2-checkpoint-summary-checkpoint 0 fn2-checkpoint-summary) checkpoint)
        (posp (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary))
        (= (fn2-checkpoint-summary-phase 1 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-idle*)
        (fn2-checkpoint-cbase-row-promised-p 0 fn2-checkpoint-summary fn2-checkpoint-cbase-holds)
        (fn2-checkpoint-summary-authority-row-complete-p 0 fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
        (= (fn2-checkpoint-summary-authority-checkpoint 0 fn2-checkpoint-summary-authority) checkpoint)
        (= (fn2-checkpoint-summary-authority-catalog-tag 0 fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary))
        (= (fn2-checkpoint-summary-authority-phase 1 fn2-checkpoint-summary-authority) *fn2-checkpoint-summary-authority-phase-idle*)
        (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*)
        (= (fn2-alloc-freeze-phase fn2-extents) 0)
        (= (fn2-c-source-control-phase 0 fn2-c-source-control) *fn2-c-source-writer-phase-idle*)) complete)))

(defun fn2-clt-drive-complete (fuel checkpoint cap fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
 (cond ((fn2-clt-completed-p checkpoint fn2-core) (mv :complete fn2-core fn2-sim fn2-own))
       ((zp fuel) (mv :fuel fn2-core fn2-sim fn2-own))
       ((fn2-core-stopped-p fn2-core) (mv :failed fn2-core fn2-sim fn2-own))
       (t (b* (((mv code fn2-core fn2-sim fn2-own)
                (fn2-cln-pump nil cap fn2-core fn2-sim fn2-own)))
           (if (eq code :failed) (mv code fn2-core fn2-sim fn2-own)
            (fn2-clt-drive-complete (- fuel 1) checkpoint cap fn2-core fn2-sim fn2-own))))))

; Begin only at the actual successfully fenced producer pause. Expected
; checkpoint is read here, never supplied as proof of a completed catalog.
(defun fn2-clt-complete-held (fuel cap fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((unless (and (fn2-clc-published-held-p fn2-core) (fn2-clc-full-live-source-p fn2-core)))
       (mv :not-held 0 0 fn2-core fn2-sim fn2-own))
      (checkpoint
       (stobj-let ((fn2-checkpoint-publication (fn2-core-checkpoint-publication fn2-core))) (checkpoint)
        (fn2-checkpoint-publication-base-checkpoint 0 fn2-checkpoint-publication) checkpoint))
      ((mv completed fn2-core fn2-sim fn2-own)
       (fn2-clt-drive-complete fuel checkpoint cap fn2-core fn2-sim fn2-own))
      (tag (if (eq completed :complete)
            (stobj-let ((fn2-checkpoint-summary (fn2-core-checkpoint-summary fn2-core))) (tag)
             (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) tag) 0)))
  (mv completed checkpoint tag fn2-core fn2-sim fn2-own)))

; Reusable first catalog constructor. Caller may now start FETCH/META, perform
; an actual supported mutation, and call clc-prefix-to-held for the second cut.
; A DELETE producer is not present in current served FNCT/authority codecs;
; do not substitute group-counts :withdraw or direct C-row mutation for it.
(defun fn2-clt-first-catalog (fuel cap uid consumer op article fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((mv held cursor position nonce fn2-core fn2-sim fn2-own)
       (fn2-cln-prefix-to-held cap uid consumer op article fn2-core fn2-sim fn2-own))
      ((unless (eq held :held)) (mv held cursor position nonce 0 0 fn2-core fn2-sim fn2-own))
      ((mv complete checkpoint tag fn2-core fn2-sim fn2-own)
       (fn2-clt-complete-held fuel cap fn2-core fn2-sim fn2-own)))
  (mv complete cursor position nonce checkpoint tag fn2-core fn2-sim fn2-own)))

; The interval between first-catalog and this call belongs to the fixture's
; actual producer/scheduler (for example APPEND plus a captured FETCH). This
; helper does not invent a mutation or assume that a withdrawn row drops data.
(defun fn2-clt-next-held (checkpoint tag fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((unless (and (fn2-clt-completed-p checkpoint fn2-core)
                   (stobj-let ((fn2-checkpoint-summary (fn2-core-checkpoint-summary fn2-core))) (same)
                    (= (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) tag) same)))
       (mv :previous 0 fn2-core fn2-sim fn2-own))
      ((mv held fn2-core fn2-sim fn2-own) (fn2-clc-prefix-to-held fn2-core fn2-sim fn2-own))
      ((unless (eq held :held)) (mv held 0 fn2-core fn2-sim fn2-own))
      (next (stobj-let ((fn2-checkpoint-publication (fn2-core-checkpoint-publication fn2-core))) (next)
              (fn2-checkpoint-publication-base-checkpoint 0 fn2-checkpoint-publication) next)))
  (mv (if (and (< checkpoint next) (fn2-clc-full-live-source-p fn2-core)) :held :lineage)
      next fn2-core fn2-sim fn2-own)))
