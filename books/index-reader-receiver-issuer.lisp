; Actual filled RX turn -> registered request association. This is INTERNAL:
; the serialized owner supplies the actual turn/provider, never a source tuple.
; The full request constructor demand includes BOTH the kernel reservation
; constructors and these receipt/request rebuilds; installed adequacy is open.
(in-package "ACL2")
(include-book "index-query-slot-issuer")
(include-book "receiver-turn-controller")
(include-book "index-reader-actor")

(defun fn-irq-reserve-receiver-request
 (id holder pin publication pre-oc rc effects demand ticket
     fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing
                         fn-page-read-pool) :guard t :verify-guards nil))
 ; Read the real live filled turn BEFORE PRS admission. This retained pointer
 ; is borrowed from that SAME turn; it neither transfers nor releases custody.
 (let ((source (fn-owner-rx-turn-consumer-source
                ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)))
  (if (not source)
      (mv :unavailable-input nil fn-index-backing fn-page-read-pool)
    (mv-let (word nonce fn-index-backing fn-page-read-pool)
     (fn-irq-reserve-request id holder pin publication pre-oc rc effects demand
                            fn-index-backing fn-page-read-pool)
     (if (not (eq word :reserved))
         (mv word nonce fn-index-backing fn-page-read-pool)
       (let* ((receipt (fn-ibp-request-pending fn-index-backing))
              (request (fn-omk-at 6 receipt))
              (with-input
               (list (fn-omk-at 0 request) (fn-omk-at 1 request)
                     (fn-omk-at 2 request) (fn-omk-at 3 request)
                     (fn-omk-at 4 request) (fn-omk-at 5 request)
                     (fn-omk-at 6 request) (fn-omk-at 7 request)
                     (fn-omk-at 8 request) source))
              (fn-index-backing
               (update-fn-ibp-request-pending
                (list (fn-omk-at 0 receipt) (fn-omk-at 1 receipt)
                      (fn-omk-at 2 receipt) (fn-omk-at 3 receipt)
                      (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
                      with-input (fn-omk-at 7 receipt)
                      (fn-omk-at 8 receipt) (fn-omk-at 9 receipt) (fn-omk-at 10 receipt))
                fn-index-backing)))
        (let* ((current (fn-ibp-request-pending fn-index-backing))
               (ordinal (fn-omk-at 3 current))
               (generation (fn-irq-receipt-request-generation current)))
         (if (not (and (posp nonce) (natp ordinal) (posp generation)))
             (mv :recovery-required nonce fn-index-backing fn-page-read-pool)
          (mv-let (actor-word fn-index-backing)
           (fn-ira-pending-bind (fn-irq-candidate-token nonce ordinal generation)
                                fn-index-backing)
           (mv (if (eq actor-word :actor-retained) word :recovery-required)
               nonce fn-index-backing fn-page-read-pool))))))))))
(verify-guards fn-irq-reserve-receiver-request)
