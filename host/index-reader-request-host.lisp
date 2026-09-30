; Include at the owner bridge after its actual STATE/source accessors.
; No owner-host include here: owner-host owns the serialized producer caller.
(in-package "ACL2")
(logic)
(include-book "../books/index-reader-request")
(include-book "index-connection-repin-prepare-host")

; Token-only consumer of the actual registered range control. The callee
; validates the exact active query/payload claim before borrowing its plan.
; FUEL pays all directory traversals; STATE is preserved by this consumer.
(defun fn-owner-index-reader-request-render-install
 (token fuel fn-mio$c fn-render-holder state)
 (declare (xargs :stobjs (fn-mio$c fn-render-holder state)
                 :guard (natp fuel)))
 (mv-let (word left fn-mio$c fn-render-holder)
   (fn-irr-render-install token fuel fn-mio$c fn-render-holder)
   (mv word left fn-mio$c fn-render-holder state)))

; Core-generated response projection from the SAME admitted registered
; request. The owner decides current account/configuration authority; this
; consumer validates retained source/query lifetime, not mutable policy.
(defun fn-owner-index-reader-request-response
 (token fuel fn-mio$c state)
 (declare (xargs :stobjs (fn-mio$c state) :guard (natp fuel)))
 (mv-let (word step disposition-token left)
   (fn-irr-response-read token fuel fn-mio$c)
   (mv word step disposition-token left fn-mio$c state)))

; INTERNAL only for the actual zero-prefix source-boundary action. NEW is
; projected from its registered reservation, not accepted from a host plan.
; The whole parse/offer/query/dispatch/commit allowance precedes this call.
(defun fn-owner-index-reader-request-offer-source
 (token fuel fn-mio$c state)
 (declare (xargs :stobjs (fn-mio$c state) :mode :program))
 (mv-let (identity id old new needed fn-mio$c)
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
   (identity id old new needed)
   (let* ((receipt (fn-ibp-request-pending fn-index-backing))
          (request (fn-irr-receipt-request receipt))
          (nonce (fn-omk-at 2 receipt))
          (ordinal (fn-omk-at 3 receipt))
          (generation (fn-irq-receipt-request-generation receipt)))
    (mv (and (posp nonce) (natp ordinal) (posp generation)
             (equal token (fn-irq-candidate-token nonce ordinal generation)))
        (fn-omk-at 1 request) (fn-irr-request-holder request)
        (fn-omk-at 1 (fn-ibp-connection-pending fn-index-backing))
        (* 13 (+ 1 (fn-ibp-slot-depth fn-index-backing)))))
   (mv identity id old new needed fn-mio$c))
  (if (not (and identity (natp fuel) (<= needed fuel)))
      ; Already inside the serialized parsed action: never save/replay RC.
      (mv :recovery-required nil fuel fn-mio$c state)
    (mv-let (prepared pin left fn-mio$c state)
     (fn-owner-index-connection-repin-prepare id old new fuel fn-mio$c state)
     (if (not (and (eq prepared :captured) (natp left)))
         (mv prepared nil left fn-mio$c state)
       (mv-let (owned remaining fn-mio$c)
        (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
         (owned remaining fn-index-backing)
         (fn-irr-request-offer-source (fn-omk-at 1 token) left fn-index-backing)
         (mv owned remaining fn-mio$c))
        (mv (if (eq owned :owned) :offer-ready owned) pin remaining fn-mio$c state)))))))

; INTERNAL producer-only boundary, included after owner STATE/credits/exposure
; definitions. The actual caller derives RC from current STATE under the same
; serialized gate, after source+construction admission, and calls this without
; yielding. An earlier captured OC/RC is never passed as authority here.
(defun fn-owner-index-reader-request-complete
 (token rc fuel fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state) :mode :program))
 (let ((current-oc (fn-owner-ocfg state)))
  (mv-let (word left fn-mio$c fn-page-read-pool)
   (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (word left fn-index-backing fn-page-read-pool)
    (let* ((receipt (fn-ibp-request-pending fn-index-backing))
           (request (fn-irr-receipt-request receipt))
           (nonce (fn-omk-at 2 receipt))
           (ordinal (fn-omk-at 3 receipt))
           (generation (fn-irq-receipt-request-generation receipt)))
     (if (not (and (posp nonce) (natp ordinal) (posp generation)
                   (equal token (fn-irq-candidate-token nonce ordinal generation))))
         (mv :stale fuel fn-index-backing fn-page-read-pool)
       (mv-let (prepared fn-index-backing)
        (fn-irr-request-complete-read nonce current-oc rc fn-index-backing)
        (if (eq prepared :read-offer-ready)
            (fn-irr-request-finish-source nonce fuel fn-index-backing fn-page-read-pool)
          (mv prepared fuel fn-index-backing fn-page-read-pool)))))
    (mv word left fn-mio$c fn-page-read-pool))
   (if (not (fn-irq-ready-phasep word))
       ; Replays project the persisted step/disposition, never reinstall STATE.
       (mv-let (persisted step disposition-token fn-mio$c)
        (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
         (persisted step disposition-token)
         (let ((receipt (fn-ibp-request-pending fn-index-backing)))
          (if (and (eq word :observed) (fn-irr-receipt-committedp receipt))
           (mv (fn-omk-at 7 receipt) (fn-irr-receipt-step receipt)
               (fn-irr-receipt-replacement receipt))
           (mv word nil nil)))
         (mv persisted step disposition-token fn-mio$c))
        (mv persisted step disposition-token left fn-mio$c fn-page-read-pool state))
     (let* ((result (car rc))
            (effects (fn-own-tls-result-effects result))
            (consumed (fn-own-tls-result-consumed result)))
      (mv-let (id fn-mio$c)
       (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
        (id)
        (fn-omk-at 1 (fn-irr-receipt-request
                       (fn-ibp-request-pending fn-index-backing)))
        (mv id fn-mio$c))
       (let* ((state (fn-owner-put-credits (cdr rc) state))
              (state (fn-owner-install-ocfg (fn-own-tls-result-owner result) state))
              (state (fn-owner-exposure-observe id effects consumed state))
              (step (fn-splan-step-make effects
                      (fn-served-closingp effects) (fn-served-starttlsp effects)
                      (fn-served-submission effects) consumed
                      (fn-olog-served-refusal-lines (fn-owner-core state) id effects)
                      (f-get-global 'fn-owner-exposure-close state))))
        (mv-let (committed disposition-token fn-mio$c)
         (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
          (committed disposition-token fn-index-backing)
          (mv-let (committed fn-index-backing)
           (fn-irq-commit-current (fn-omk-at 1 token) step fn-index-backing)
           (mv committed
               (fn-irr-receipt-replacement (fn-ibp-request-pending fn-index-backing))
               fn-index-backing))
          (mv committed disposition-token fn-mio$c))
         (mv (if (fn-irq-committed-phasep committed) committed :recovery-required)
             (if (fn-irq-committed-phasep committed) step nil)
             disposition-token left fn-mio$c fn-page-read-pool state)))))))))
