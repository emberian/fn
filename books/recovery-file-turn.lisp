; Actual early executor receipt: selected compiled role slot, not service state.
; No source record or body budget is accepted from the native caller.
(in-package "ACL2")
(include-book "runtime-operation-source")
(include-book "allocation-turn-slots")

(defun fn-owner-recovery-file-turn-begin
 (path fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :guard (fn-aec-pool-statep fn-page-read-pool)))
 (if (not (fn-owner-runtime-operation-binding-currentp fn-page-read-pool state))
     (mv :recovery-operation-unavailable nil 0 fn-allocation-turn-slots fn-page-read-pool)
  (mv-let (source-word family)
   (fn-owner-runtime-operation-source :recovery-file-issue fn-page-read-pool state)
   (declare (ignore family))
   (mv-let (slot-word slot) (fn-runtime-operation-compiled-slot :recovery-file-issue)
    (if (not (and (eq source-word :runtime-operation-available)
                   (eq slot-word :compiled-operation-source)
                   (natp slot) (fn-ats-slotp slot fn-allocation-turn-slots)
                   (eq (fn-ats-kindsi slot fn-allocation-turn-slots) :recovery-file-issue)))
        (mv :recovery-operation-unavailable nil 0 fn-allocation-turn-slots fn-page-read-pool)
     (mv-let (word nonce fn-allocation-turn-slots fn-page-read-pool)
      (fn-ats-enter-internal slot :recovery-file-issue fn-allocation-turn-slots fn-page-read-pool)
      (if (not (eq word :gate-owned))
          (mv word slot nonce fn-allocation-turn-slots fn-page-read-pool)
       ; The source phase runs under actual prepaid Qgate; missing path/body
       ; source retains the issued phase2 receipt for its sole outer cleanup.
       (mv-let (body-word body)
        (fn-owner-runtime-operation-body-cost :recovery-file-issue path nil fn-page-read-pool state)
        (if (not (eq body-word :runtime-operation-available))
            (mv :recovery-body-source-unavailable slot nonce fn-allocation-turn-slots fn-page-read-pool)
         (mv-let (paid fn-allocation-turn-slots fn-page-read-pool)
          (fn-ats-prepay-body-internal slot nonce body fn-allocation-turn-slots fn-page-read-pool)
          (mv paid slot nonce fn-allocation-turn-slots fn-page-read-pool)))))))))))
