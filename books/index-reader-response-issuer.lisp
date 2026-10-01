; Episode-qualified response -> actual registered IRQ custody.
; INTERNAL source-only constructor: installed runtime demand and publication
; authority remain caller admission obligations. This never reinstalls STATE.
(in-package "ACL2")
(include-book "index-reader-receiver-issuer")

(defun fn-irq-reserve-response-request
 (id holder pin publication demand episode
  fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing
                         fn-page-read-pool) :guard t :verify-guards nil))
 (mv-let (observed source pre-oc rc step)
  (fn-owner-rx-turn-response-result episode fn-rx-provider fn-receiver-turn
                                   fn-page-read-pool)
  (declare (ignore rc step))
  (if (not (eq observed :response-result))
      (mv :unavailable-response nil fn-index-backing fn-page-read-pool)
   (mv-let (word nonce fn-index-backing fn-page-read-pool)
    (fn-irq-reserve-request id holder pin publication pre-oc nil nil demand
                           fn-index-backing fn-page-read-pool)
    (if (not (eq word :reserved))
        (mv word nonce fn-index-backing fn-page-read-pool)
     (let* ((receipt (fn-ibp-request-pending fn-index-backing))
            (request (fn-irr-receipt-request receipt))
            (with-input
             (list (fn-omk-at 0 request) (fn-omk-at 1 request)
                   (fn-omk-at 2 request) (fn-omk-at 3 request)
                   (fn-omk-at 4 request) (fn-omk-at 5 request)
                   (fn-omk-at 6 request) (fn-omk-at 7 request)
                   (fn-omk-at 8 request) source))
            (fn-index-backing
             (update-fn-ibp-request-pending
              (fn-irr-receipt-keep receipt with-input :reserved
                                   (fn-omk-at 9 receipt)) fn-index-backing))
            (ordinal (fn-omk-at 3 receipt))
            (generation (fn-irq-receipt-request-generation receipt)))
      (if (not (and (posp nonce) (natp ordinal) (posp generation)))
          (mv :recovery-required nonce fn-index-backing fn-page-read-pool)
       (mv-let (actor-word fn-index-backing)
        (fn-ira-pending-bind (fn-irq-candidate-token nonce ordinal generation)
                            fn-index-backing)
        (if (not (eq actor-word :actor-retained))
            (mv :recovery-required nonce fn-index-backing fn-page-read-pool)
         ; Phase-dependent actor field5 holds this issued episode until the
         ; actual commit replaces it with the same episode's step reference.
         (let* ((current (fn-ibp-request-pending fn-index-backing))
                (actor (fn-ira-receipt-root current))
                (bound-actor
                 (list (fn-omk-at 0 actor) (fn-omk-at 1 actor)
                       (fn-omk-at 2 actor) (fn-omk-at 3 actor)
                       (fn-omk-at 4 actor) (list :response-episode episode)))
                (fn-index-backing
                 (update-fn-ibp-request-pending
                  (list (fn-omk-at 0 current) (fn-omk-at 1 current)
                        (fn-omk-at 2 current) (fn-omk-at 3 current)
                        (fn-omk-at 4 current) (fn-omk-at 5 current)
                        (fn-omk-at 6 current) (fn-omk-at 7 current)
                        (fn-omk-at 8 current) (fn-omk-at 9 current) bound-actor)
                  fn-index-backing)))
          (mv :reserved nonce fn-index-backing fn-page-read-pool)))))))))))

; Only the real query-reference transfer reaching :source-owned permits this
; adoption. The actual response root, not a supplied RC/step, is the source.
(defun fn-irq-adopt-recorded-response
 (token episode fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing
                         fn-page-read-pool) :guard t :verify-guards nil))
 (mv-let (observed source pre-oc rc step)
  (fn-owner-rx-turn-response-result episode fn-rx-provider fn-receiver-turn
                                   fn-page-read-pool)
  (let* ((receipt (fn-ibp-request-pending fn-index-backing))
         (request (fn-irr-receipt-request receipt))
         (nonce (fn-omk-at 2 receipt))
         (ordinal (fn-omk-at 3 receipt))
         (generation (fn-irq-receipt-request-generation receipt)))
   (if (not (and (eq observed :response-result)
                  (posp nonce) (natp ordinal) (posp generation)
                  (equal token (fn-irq-candidate-token nonce ordinal generation))
                  (eq (fn-omk-at 7 receipt) :source-owned)
                  (equal (fn-omk-at 5 (fn-ira-receipt-root receipt))
                         (list :response-episode episode))
                  (equal source (fn-irr-request-input-source request))
                  (consp rc) (not (fn-own-tls-result-repinned (car rc)))))
       (mv :unavailable-response fn-index-backing)
    (mv-let (word fn-index-backing)
     (fn-irr-request-complete-read nonce pre-oc rc fn-index-backing)
     (if (not (eq word :read-ready))
         (mv :recovery-required fn-index-backing)
      (mv-let (committed fn-index-backing)
       (fn-irq-commit-current nonce step fn-index-backing)
       (if (not (eq committed :committed))
           (mv :recovery-required fn-index-backing)
        (fn-ira-pending-commit-response token fn-index-backing)))))))))
