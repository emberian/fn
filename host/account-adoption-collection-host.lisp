; Actual same-turn pooled promoter of the registered durable E output. No
; supplied selection/graph, native :durable atom or semantic-ready tuple.
(in-package "ACL2")
(include-book "account-durable-completion-host")

(defun fn-owner-account-adoption-collect
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard t))
 (mv-let (word token output)
  (fn-owner-account-adoption-durable-output state)
  (let* ((current (fn-owner-account-turn-current state))
         (issued (fn-cp-nth 1 current)) (source (fn-cp-nth 5 current)))
   (if (not (and (eq word :account-durable-produced)
                  (fn-cado-receipt-coordinatep token)
                  (fn-cado-receipt-coordinatep issued) (equal token issued)
                  (fn-owner-account-turn-current-bodyp :operation-select source
                         slot nonce fn-allocation-turn-slots fn-page-read-pool state)))
       (mv :recovery-required :account-durable-output-unavailable
           fn-allocation-turn-slots fn-page-read-pool state)
    (mv-let (promoted fn-page-read-pool state)
      (fn-owner-account-turn-produced output fn-page-read-pool state)
     (if (not (eq promoted :account-turn-promoted))
         (mv :recovery-required :account-durable-promotion
             fn-allocation-turn-slots fn-page-read-pool state)
      ; Getter supplied the actual once-collected result, not a reexecution.
      (mv (fn-cp-nth 0 (fn-cp-nth 2 output))
          (fn-cp-nth 1 (fn-cp-nth 2 output))
          fn-allocation-turn-slots fn-page-read-pool state)))))))
