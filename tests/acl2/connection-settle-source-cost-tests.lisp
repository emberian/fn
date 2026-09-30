(in-package "ACL2")
(include-book "../../books/connection-settle-source-cost")
; The actual source issuer supplies this identity. Replaying settlement after a
; definite charged abort cannot refund the spent coordinate or reconstruct a row.
(defthm icsct-issued-abort-then-settle-complete
 (let* ((budget '(1000 1000 1000 1000 1000)) (baseline '(100 0 0 0 0))
        (grant '(40 0 0 0 1))
        (backing (update-fn-ibp-pool-capacity 1 (create-fn-index-backing)))
        (pool (fn-owner-page-read-keep-ledger
               (fn-prl-build budget '(0 0 0 0 1) 1 nil baseline) (create-fn-page-read-pool)))
        (reserved (fn-icr-reserve 42 grant backing pool))
        (token (mv-nth 1 reserved))
        (aborted (fn-icr-abort token 8 (mv-nth 2 reserved) (mv-nth 3 reserved)))
        (before-backing (mv-nth 2 aborted)) (before-pool (mv-nth 3 aborted))
        (result (fn-icr-settle token 8 before-backing before-pool))
        (seen (fn-icsc-settle token 8 before-backing before-pool)))
  (and (fn-index-backingp backing) (fn-page-read-poolp pool) (natp 8)
       (equal (mv-nth 0 reserved) :reserved) (equal token '(:connection-holder 2 1 0))
       (equal (mv-nth 0 aborted) :released)
       (not (fn-ibp-connection-pending before-backing))
       (equal (fn-owner-page-read-ledger before-pool)
              (fn-prl-build budget '(0 0 0 0 2) 2 nil baseline))
       (equal result (list :unavailable 8 before-backing before-pool))
       (equal seen (list :unavailable 8 before-backing before-pool
                  (list nil 0 '((:add (1 0)) (:multiply (4 1)))
                    (list (list :unpriced-call 'fn-ibp-connection-read
                           (list token 8) (list :unavailable nil 8))))))))
 :rule-classes nil)
; A real, already-issued charged receipt prevents settlement before its
; operation protocol is ready. Every output and retained effect is unchanged.
(defthm icsct-issued-charged-settle-refuses-complete
 (let* ((backing (update-fn-ibp-pool-capacity 1 (create-fn-index-backing)))
        (pool (fn-owner-page-read-keep-ledger
               (fn-prl-build '(1000 1000 1000 1000 1000) '(0 0 0 0 0) 0 nil '(100 0 0 0 0))
               (create-fn-page-read-pool)))
        (reserved (fn-icr-reserve 42 '(40 0 0 0 1) backing pool))
        (token (mv-nth 1 reserved)) (after-backing (mv-nth 2 reserved))
        (after-pool (mv-nth 3 reserved)))
  (and (fn-index-backingp backing) (fn-page-read-poolp pool) (natp 8)
       (equal (mv-nth 0 reserved) :reserved) (fn-ich-tokenp token)
       (equal (fn-omk-at 6 (fn-ibp-connection-pending after-backing)) :charged)
       (equal (fn-icr-settle token 8 after-backing after-pool)
              (list :busy 8 after-backing after-pool))
       (equal (fn-icsc-settle token 8 after-backing after-pool)
              (list :busy 8 after-backing after-pool (list nil 0 nil nil)))))
 :rule-classes nil)
; This is the exact successful registered-abort prefix: retain abort intent,
; run the source close operation, retain abort-ready, then settle. The token is
; issued by PRS; no host joined/alias flag is an input. The complete parent abort
; result agrees with the observed suffix and the literal released provider.
(defthm icsct-issued-registered-settle-complete
 (let* ((budget '(1000 1000 1000 1000 1000)) (baseline '(100 0 0 0 0))
        (grant '(40 0 0 0 1))
        (segment (update-fn-ich-segment-id 1 (create-fn-ibp-connection-segment)))
        (node (fn-ibp-node-children-put 'fn-ibp-connection-segment segment (create-fn-ibp-node)))
        (backing (update-fn-ibp-registry node
                   (update-fn-ibp-pool-capacity 1 (create-fn-index-backing))))
        (pool (fn-owner-page-read-keep-ledger
               (fn-prl-build budget '(0 0 0 0 1) 1 nil baseline) (create-fn-page-read-pool)))
        (reserved (fn-icr-reserve 42 grant backing pool))
        (token (mv-nth 1 reserved))
        (registered (fn-icr-register token 1 (mv-nth 2 reserved)))
        (receipt (fn-ibp-connection-pending (mv-nth 2 registered)))
        (intent (update-fn-ibp-connection-pending
                  (fn-icr-keep-phase receipt :abort-intent (fn-omk-at 7 receipt))
                  (mv-nth 2 registered)))
        (closed (fn-ibp-connection-event token :close 42 nil 8 intent))
        (ready (update-fn-ibp-connection-pending
                 (fn-icr-keep-phase receipt :abort-ready (fn-omk-at 7 receipt))
                 (mv-nth 3 closed)))
        (paid-pool (mv-nth 3 reserved))
        (result (fn-icr-settle token 7 ready paid-pool))
        (seen (fn-icsc-settle token 7 ready paid-pool))
        (released-segment
          (update-fn-ich-rowsi 0 (list :connection-holder token nil nil :released nil 0) segment))
        (expected-backing
          (update-fn-ibp-connection-free '(0)
           (update-fn-ibp-connection-pending nil
            (update-fn-ibp-registry
             (fn-ibp-node-children-put 'fn-ibp-connection-segment released-segment
                                      (fn-ibp-registry ready))
             (mv-nth 2 registered)))))
        (expected-pool (fn-owner-page-read-keep-ledger
                        (fn-prl-build budget '(0 0 0 0 2) 2 nil baseline) pool)))
  (and (fn-index-backingp backing) (fn-page-read-poolp pool) (natp 7)
       (equal (mv-nth 0 reserved) :reserved) (equal token '(:connection-holder 2 1 0))
       (equal (mv-nth 0 registered) :registered) (equal (mv-nth 1 registered) 0)
       (equal (mv-nth 0 closed) :closing) (equal (mv-nth 2 closed) 7)
       (equal (fn-omk-at 6 (fn-ibp-connection-pending ready)) :abort-ready)
       (equal result (list :released 4 expected-backing expected-pool))
       (equal (fn-icr-abort token 8 (mv-nth 2 registered) paid-pool) result)
       (equal (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen)) result)
       (equal (fn-atsc-cells (mv-nth 4 seen)) 24)
       (equal (fn-atsc-ops (mv-nth 4 seen))
        '((:add (1 0)) (:multiply (4 1)) (:subtract (1 1))
          (:multiply (64 0)) (:add (0 0))
          (:subtract (40 40)) (:subtract (0 0)) (:subtract (0 0)) (:subtract (0 0))))))
 :rule-classes nil)
