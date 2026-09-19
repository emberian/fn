; The relay crash argument and what fn-relay-invp buys (wave 2, packet B).
;
; Keystones (cite these, not the -by-definition lemmas):
;   fn-relay-crash-recover-preserves-invp
;   fn-relay-forwarding-receipt-has-durable-onward-obligation
;   fn-relay-crash-recover-never-yields-a-promise-alone
;   fn-relay-receipt-kind-is-archived-or-forwarding
(in-package "ACL2")
(include-book "relay-invariants")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))
; The relay proofs open the receiver definitions; enable them here, locally.
(local (in-theory (enable fn-bp-receiver-vocabulary)))

; Crash then replay over both journals: the receiver's pending intent goes to
; either outcome; the sender restarts and recovers its fenced intent to either
; result.  The invariant survives every combination.
(defthm fn-relay-crash-recover-preserves-invp
  (implies (fn-relay-invp rs)
           (fn-relay-invp (fn-relay-crash-recover rs receiver-outcome sender-result)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-invp-sender-step
                            (event (fn-bp-restart-event)))
                 (:instance fn-relay-invp-sender-step
                            (rs (fn-relay-make-state
                                 (fn-relay-store rs) (fn-relay-receiver rs)
                                 (fn-bp-result-state
                                  (fn-bp-step (fn-relay-sender rs)
                                              (fn-bp-restart-event)))
                                 (fn-relay-terms rs) (fn-relay-undertakings rs)))
                            (event (fn-bp-storage-recover-event
                                    (fn-bp-pending-txid
                                     (fn-bp-state-pending
                                      (fn-bp-result-state
                                       (fn-bp-step (fn-relay-sender rs)
                                                   (fn-bp-restart-event)))))
                                    (fn-bp-pending-generation
                                     (fn-bp-state-pending
                                      (fn-bp-result-state
                                       (fn-bp-step (fn-relay-sender rs)
                                                   (fn-bp-restart-event)))))
                                    sender-result)))
                 (:instance fn-relay-commit-receipt-preserves-invp
                            (rs (fn-relay-make-state
                                 (fn-relay-store rs) (fn-relay-receiver rs)
                                 (if (consp (fn-bp-state-pending
                                             (fn-bp-result-state
                                              (fn-bp-step (fn-relay-sender rs)
                                                          (fn-bp-restart-event)))))
                                     (fn-bp-result-state
                                      (fn-bp-step
                                       (fn-bp-result-state
                                        (fn-bp-step (fn-relay-sender rs)
                                                    (fn-bp-restart-event)))
                                       (fn-bp-storage-recover-event
                                        (fn-bp-pending-txid
                                         (fn-bp-state-pending
                                          (fn-bp-result-state
                                           (fn-bp-step (fn-relay-sender rs)
                                                       (fn-bp-restart-event)))))
                                        (fn-bp-pending-generation
                                         (fn-bp-state-pending
                                          (fn-bp-result-state
                                           (fn-bp-step (fn-relay-sender rs)
                                                       (fn-bp-restart-event)))))
                                        sender-result)))
                                   (fn-bp-result-state
                                    (fn-bp-step (fn-relay-sender rs)
                                                (fn-bp-restart-event))))
                                 (fn-relay-terms rs) (fn-relay-undertakings rs)))
                            (upstream (fn-bpr-context-work-id
                                       (fn-bpr-receipt-entry-context
                                        (fn-bpr-state-pending (fn-relay-receiver rs)))))
                            (receipt-id (fn-bpa-receipt-id
                                         (fn-bpr-receipt-entry-receipt
                                          (fn-bpr-state-pending (fn-relay-receiver rs)))))
                            (outcome receiver-outcome)))
           :in-theory (e/d (fn-relay-crash-recover fn-relay-commit-receipt)
                           (fn-relay-invp fn-relay-statep fn-bp-step
                                          fn-bp-result-state fn-bpr-commit-receipt
                                          fn-bp-state-pending fn-bp-pending-txid
                                          fn-bp-pending-generation
                                          fn-bp-restart-event
                                          fn-bp-storage-recover-event
                                          fn-bpr-state-pending
                                          fn-bpr-receipt-entry-context
                                          fn-bpr-receipt-entry-receipt
                                          fn-bpr-context-work-id fn-bpa-receipt-id
                                          fn-relay-invp-sender-step
                                          fn-relay-commit-receipt-preserves-invp)))))

; -----------------------------------------------------------------------------
; What the invariant buys

(defthm fn-relay-find-receipt-backed
  (implies (and (fn-relay-entries-backedp entries node terms u works)
                (consp (fn-bpr-find-receipt upstream entries)))
           (fn-relay-entry-backedp (fn-bpr-find-receipt upstream entries)
                                   node terms u works))
  :hints (("Goal" :induct (fn-bpr-find-receipt upstream entries)
           :in-theory (e/d (fn-bpr-find-receipt fn-relay-entries-backedp)
                           (fn-relay-entry-backedp)))))

; No :forwarding receipt without a durable onward obligation: the recorded
; onward work is present in the sender's durable works, bound to the node's
; committed binding, and the content the context names is durably bound.
(defthm fn-relay-forwarding-receipt-has-durable-onward-obligation
  (implies (and (fn-relay-invp rs)
                (equal (car (fn-relay-receipt rs upstream)) :forwarding))
           (let* ((entry (fn-bpr-find-receipt
                          upstream (fn-bpr-state-receipts (fn-relay-receiver rs))))
                  (ctx (fn-bpr-receipt-entry-context entry))
                  (u (fn-relay-find-undertaking (fn-bpr-context-work-id ctx)
                                                (fn-relay-undertakings rs)))
                  (work (fn-bp-find-work (fn-relay-undertaking-onward u)
                                         (fn-bp-state-works (fn-relay-sender rs)))))
             (and (consp u)
                  (consp work)
                  (fn-bp-work-boundp (fn-relay-node rs) work)
                  (fn-relay-content-durablep (fn-relay-node rs) ctx))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-statep-components)
                 (:instance fn-bp-binding-state-implies-works-boundp
                            (s (fn-relay-sender rs)))
                 (:instance fn-relay-find-receipt-backed
                            (entries (fn-bpr-state-receipts (fn-relay-receiver rs)))
                            (node (fn-relay-node rs))
                            (terms (fn-relay-terms rs))
                            (u (fn-relay-undertakings rs))
                            (works (fn-bp-state-works (fn-relay-sender rs))))
                 (:instance fn-bp-find-work-boundp
                            (node (fn-relay-node rs))
                            (works (fn-bp-state-works (fn-relay-sender rs)))
                            (id (fn-relay-undertaking-onward
                                 (fn-relay-find-undertaking
                                  (fn-bpr-context-work-id
                                   (fn-bpr-receipt-entry-context
                                    (fn-bpr-find-receipt
                                     upstream
                                     (fn-bpr-state-receipts (fn-relay-receiver rs)))))
                                  (fn-relay-undertakings rs))))))
           :in-theory (e/d (fn-relay-invp fn-relay-receipt fn-relay-entry-backedp
                                          fn-relay-node)
                           (fn-relay-statep fn-bp-statep fn-bp-binding-statep
                                            fn-relay-entries-backedp
                                            fn-relay-undertakings-backedp
                                            fn-relay-terms-tablep
                                            fn-relay-undertaking-listp
                                            fn-relay-content-durablep
                                            fn-relay-terms-kind
                                            fn-relay-find-undertaking
                                            fn-bpr-find-receipt fn-bp-find-work
                                            fn-bp-work-boundp fn-bp-works-boundp
                                            fn-relay-statep-components
                                            fn-relay-find-receipt-backed
                                            fn-bp-find-work-boundp)))))

; The enqueue-then-crash gap: whatever the two journals recover to, a
; forwarding promise in the recovered relay has its obligation.
(defthm fn-relay-crash-recover-never-yields-a-promise-alone
  (implies (and (fn-relay-invp rs)
                (equal (car (fn-relay-receipt
                             (fn-relay-crash-recover rs receiver-outcome sender-result)
                             upstream))
                       :forwarding))
           (let* ((recovered (fn-relay-crash-recover rs receiver-outcome sender-result))
                  (entry (fn-bpr-find-receipt
                          upstream (fn-bpr-state-receipts (fn-relay-receiver recovered))))
                  (ctx (fn-bpr-receipt-entry-context entry))
                  (u (fn-relay-find-undertaking (fn-bpr-context-work-id ctx)
                                                (fn-relay-undertakings recovered)))
                  (work (fn-bp-find-work (fn-relay-undertaking-onward u)
                                         (fn-bp-state-works (fn-relay-sender recovered)))))
             (and (consp u)
                  (consp work)
                  (fn-bp-work-boundp (fn-relay-node recovered) work)
                  (fn-relay-content-durablep (fn-relay-node recovered) ctx))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-crash-recover-preserves-invp)
                 (:instance fn-relay-forwarding-receipt-has-durable-onward-obligation
                            (rs (fn-relay-crash-recover rs receiver-outcome
                                                        sender-result))))
           :in-theory (disable fn-relay-invp fn-relay-crash-recover
                               fn-relay-receipt fn-relay-node
                               fn-relay-crash-recover-preserves-invp
                               fn-relay-forwarding-receipt-has-durable-onward-obligation))))

; Archival acceptance and forwarding undertaking are the only receipt kinds
; the relay commits; destination-application acceptance is not among them.
(defthm fn-relay-receipt-kind-is-archived-or-forwarding
  (implies (and (fn-relay-invp rs)
                (consp (fn-relay-receipt rs upstream)))
           (fn-relay-kindp (car (fn-relay-receipt rs upstream))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-relay-find-receipt-backed
                            (entries (fn-bpr-state-receipts (fn-relay-receiver rs)))
                            (node (fn-relay-node rs))
                            (terms (fn-relay-terms rs))
                            (u (fn-relay-undertakings rs))
                            (works (fn-bp-state-works (fn-relay-sender rs)))))
           :in-theory (e/d (fn-relay-invp fn-relay-receipt fn-relay-entry-backedp)
                           (fn-relay-statep fn-relay-entries-backedp
                                            fn-relay-undertakings-backedp
                                            fn-relay-content-durablep
                                            fn-relay-terms-kind
                                            fn-relay-find-undertaking
                                            fn-bpr-find-receipt fn-bp-find-work
                                            fn-relay-find-receipt-backed)))))

; The two refusals that separate the kinds, by definition of fn-relay-undertake.
(defthm fn-relay-forwarding-without-undertaking-is-refused-by-definition
  (implies (and (equal (fn-relay-terms-kind
                        (fn-bpr-context-terms-id
                         (fn-bpr-find-context
                          upstream (fn-bpr-state-contexts (fn-relay-receiver rs))))
                        (fn-relay-terms rs))
                       :forwarding)
                (not (consp (fn-relay-find-undertaking upstream
                                                       (fn-relay-undertakings rs)))))
           (equal (fn-relay-undertake rs upstream receipt-id auth)
                  (list nil rs)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-relay-undertake)
                                  (fn-relay-statep fn-bpr-find-context
                                                   fn-relay-terms-kind
                                                   fn-relay-find-undertaking
                                                   fn-relay-content-durablep
                                                   fn-relay-onward-presentp
                                                   fn-bpr-prepare-receipt)))))

(defthm fn-relay-archived-receipt-needs-no-undertaking-by-definition
  (implies (and (fn-relay-statep rs)
                (consp (fn-bpr-find-context
                        upstream (fn-bpr-state-contexts (fn-relay-receiver rs))))
                (equal (fn-relay-terms-kind
                        (fn-bpr-context-terms-id
                         (fn-bpr-find-context
                          upstream (fn-bpr-state-contexts (fn-relay-receiver rs))))
                        (fn-relay-terms rs))
                       :archived)
                (fn-relay-content-durablep
                 (fn-relay-node rs)
                 (fn-bpr-find-context
                  upstream (fn-bpr-state-contexts (fn-relay-receiver rs))))
                (not (equal (fn-bpr-prepare-receipt (fn-relay-receiver rs)
                                                    upstream receipt-id auth)
                            (fn-relay-receiver rs))))
           (equal (car (fn-relay-undertake rs upstream receipt-id auth))
                  :archived))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-relay-undertake)
                                  (fn-relay-statep fn-bpr-find-context
                                                   fn-relay-terms-kind
                                                   fn-relay-find-undertaking
                                                   fn-relay-content-durablep
                                                   fn-relay-onward-presentp
                                                   fn-bpr-prepare-receipt)))))
