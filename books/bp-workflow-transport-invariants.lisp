(in-package "ACL2")
(include-book "bp-workflow-invariants")
(local (in-theory (disable
 fn-bp-nth
 fn-bp-config-schema
 fn-bp-config-local-eid
 fn-bp-config-peer-eid
 fn-bp-config-policy-id
 fn-bp-config-authority
 fn-bp-config-lifetime
 fn-bp-config-incarnation
 fn-bp-config-auth-context
 fn-bp-make-config
 fn-bp-configp
 fn-bp-attempt-id
 fn-bp-attempt-generation
 fn-bp-attempt-status
 fn-bp-attempt-lifetime
 fn-bp-transport-statusp
 fn-bp-retryable-statusp
 fn-bp-make-attempt
 fn-bp-attemptp
 fn-bp-receipt-id
 fn-bp-receipt-work-id
 fn-bp-receipt-subject
 fn-bp-receipt-issuer
 fn-bp-receipt-peer-eid
 fn-bp-receipt-policy-id
 fn-bp-receipt-incarnation
 fn-bp-receipt-auth-context
 fn-bp-receipt-terms-id
 fn-bp-make-receipt
 fn-bp-receiptp
 fn-bp-receipt-listp
 fn-bp-work-id
 fn-bp-work-msgid
 fn-bp-work-subject
 fn-bp-work-archive-id
 fn-bp-work-obligation-id
 fn-bp-work-peer-eid
 fn-bp-work-policy-id
 fn-bp-work-incarnation
 fn-bp-work-auth-context
 fn-bp-work-terms-id
 fn-bp-work-next-generation
 fn-bp-work-attempt
 fn-bp-work-receipt
 fn-bp-make-work
 fn-bp-workp
 fn-bp-work-listp
 fn-bp-find-work
 fn-bp-find-work-by-msgid
 fn-bp-replace-work
 fn-bp-work-outstandingp
 fn-bp-work-retryablep
 fn-bp-authorized-receiptp
 fn-bp-work-with-attempt
 fn-bp-work-with-receipt
 fn-bp-work-with-status
 fn-bp-pending-kind
 fn-bp-pending-txid
 fn-bp-pending-generation
 fn-bp-pending-work
 fn-bp-pending-receipt
 fn-bp-make-pending
 fn-bp-pendingp
 fn-bp-make-tx-key
 fn-bp-tx-keyp
 fn-bp-tx-key-listp
 fn-bp-state-node
 fn-bp-state-config
 fn-bp-state-works
 fn-bp-state-receipts
 fn-bp-state-pending
 fn-bp-state-fenced
 fn-bp-state-used-txs
 fn-bp-make-state
 fn-bp-statep
 fn-bp-initial-state
 fn-bp-pending-matchesp
 fn-bp-work-boundp
 fn-bp-works-boundp
 fn-bp-prepare-enqueue
 fn-bp-prepare-attempt
 fn-bp-prepare-receipt
 fn-bp-apply-pending
 fn-bp-effect-for-pending
 fn-bp-make-result
 fn-bp-result-state
 fn-bp-result-effects
 fn-bp-complete
 fn-bp-recovery-pending
 fn-bp-recover
 fn-bp-transport-transition-okp
 fn-bp-observe-transport
 fn-bp-request-retry
 fn-bp-restart-work
 fn-bp-restart-works
 fn-bp-restart
 fn-bp-event-kind
 fn-bp-enqueue-prepare-event
 fn-bp-attempt-prepare-event
 fn-bp-receipt-prepare-event
 fn-bp-storage-complete-event
 fn-bp-storage-recover-event
 fn-bp-transport-event
 fn-bp-no-contact-event
 fn-bp-retry-request-event
 fn-bp-restart-event
 fn-bp-eventp
 fn-bp-step
 fn-bp-trace)))
(set-prover-step-limit 3000000)

(defthm fn-bph-id-with-status
 (equal (fn-bp-work-id (fn-bp-work-with-status work status)) (fn-bp-work-id work))
 :hints (("Goal" :in-theory (enable fn-bp-work-with-status fn-bp-work-with-attempt
   fn-bp-make-work fn-bp-work-id fn-bp-nth))))
(defthm fn-bph-receipt-with-status
 (equal (fn-bp-work-receipt (fn-bp-work-with-status work status)) (fn-bp-work-receipt work))
 :hints (("Goal" :in-theory (enable fn-bp-work-with-status fn-bp-work-with-attempt
   fn-bp-make-work fn-bp-work-receipt fn-bp-nth))))
(defthm fn-bph-receipt-nil
 (equal (fn-bp-work-receipt nil) nil)
 :hints (("Goal" :in-theory (enable fn-bp-work-receipt fn-bp-nth))))
(defthm fn-bph-find-id
 (implies (consp (fn-bp-find-work id works))
  (equal (fn-bp-work-id (fn-bp-find-work id works)) id))
 :hints (("Goal" :induct (fn-bp-find-work id works)
   :in-theory (enable fn-bp-find-work))))
(defthm fn-bph-attempt-implies-work-consp
 (implies (consp (fn-bp-work-attempt work)) (consp work))
 :hints (("Goal" :in-theory (enable fn-bp-work-attempt fn-bp-nth))))
(defthm fn-bph-replace-preserves-receipt
 (implies (equal (fn-bp-work-receipt work)
                 (fn-bp-work-receipt (fn-bp-find-work (fn-bp-work-id work) works)))
  (equal (fn-bp-work-receipt (fn-bp-find-work id (fn-bp-replace-work work works)))
         (fn-bp-work-receipt (fn-bp-find-work id works))))
 :hints (("Goal" :induct (fn-bp-replace-work work works)
   :in-theory (enable fn-bp-replace-work fn-bp-find-work))))
(defthm fn-bph-replace-status-preserves-receipt
 (implies (consp (fn-bp-find-work target works))
  (equal (fn-bp-work-receipt
          (fn-bp-find-work id (fn-bp-replace-work
           (fn-bp-work-with-status (fn-bp-find-work target works) status) works)))
         (fn-bp-work-receipt (fn-bp-find-work id works)))))
(defthm fn-bph-state-works-make
 (equal (fn-bp-state-works (fn-bp-make-state node config works receipts pending fenced used)) works)
 :hints (("Goal" :in-theory (enable fn-bp-state-works fn-bp-make-state fn-bp-nth))))
(defthm fn-bph-result-state-make
 (equal (fn-bp-result-state (fn-bp-make-result s effects)) s)
 :hints (("Goal" :in-theory (enable fn-bp-result-state fn-bp-make-result fn-bp-nth))))
(defthm fn-bph-observe-preserves-receipt
 (equal (fn-bp-work-receipt
          (fn-bp-find-work id (fn-bp-state-works
           (fn-bp-observe-transport s target attempt generation status))))
        (fn-bp-work-receipt (fn-bp-find-work id (fn-bp-state-works s))))
 :hints (("Goal" :in-theory (enable fn-bp-observe-transport))))
(defthm fn-bph-retry-preserves-receipt
 (equal (fn-bp-work-receipt
          (fn-bp-find-work id (fn-bp-state-works
           (fn-bp-request-retry s target attempt generation policy))))
        (fn-bp-work-receipt (fn-bp-find-work id (fn-bp-state-works s))))
 :hints (("Goal" :in-theory (enable fn-bp-request-retry))))
(defthm fn-bph-restart-work-id
 (equal (fn-bp-work-id (fn-bp-restart-work work)) (fn-bp-work-id work))
 :hints (("Goal" :in-theory (enable fn-bp-restart-work))))
(defthm fn-bph-restart-work-receipt
 (equal (fn-bp-work-receipt (fn-bp-restart-work work)) (fn-bp-work-receipt work))
 :hints (("Goal" :in-theory (enable fn-bp-restart-work))))
(defthm fn-bph-restart-works-receipt
 (equal (fn-bp-work-receipt (fn-bp-find-work id (fn-bp-restart-works works)))
        (fn-bp-work-receipt (fn-bp-find-work id works)))
 :hints (("Goal" :induct (fn-bp-restart-works works)
   :in-theory (enable fn-bp-restart-works fn-bp-find-work))))
(defthm fn-bph-restart-preserves-receipt
 (equal (fn-bp-work-receipt
          (fn-bp-find-work id (fn-bp-state-works (fn-bp-restart s))))
        (fn-bp-work-receipt (fn-bp-find-work id (fn-bp-state-works s))))
 :hints (("Goal" :in-theory (enable fn-bp-restart))))
(defun fn-bp-transport-eventp (event)
  (declare (xargs :guard t))
  (member-equal (fn-bp-event-kind event)
                '(:transport :no-contact :retry-request :restart)))

(defun fn-bp-transport-tracep (events)
  (declare (xargs :guard t))
  (if (consp events)
      (and (fn-bp-transport-eventp (car events))
           (fn-bp-transport-tracep (cdr events)))
    (null events)))

(defthm fn-bp-transport-step-preserves-receipt
  (implies (fn-bp-transport-eventp event)
           (equal (fn-bp-work-receipt
                   (fn-bp-find-work
                    id (fn-bp-state-works
                        (fn-bp-result-state (fn-bp-step s event)))))
                  (fn-bp-work-receipt
                   (fn-bp-find-work id (fn-bp-state-works s)))))
  :hints (("Goal" :in-theory (enable fn-bp-step fn-bp-transport-eventp))))

(defthm fn-bp-transport-trace-preserves-receipt
  (implies (fn-bp-transport-tracep events)
           (equal (fn-bp-work-receipt
                   (fn-bp-find-work id
                                    (fn-bp-state-works
                                     (fn-bp-trace s events))))
                  (fn-bp-work-receipt
                   (fn-bp-find-work id (fn-bp-state-works s)))))
  :hints (("Goal" :induct (fn-bp-trace s events)
           :in-theory (enable fn-bp-trace fn-bp-transport-tracep))))

; Additional refusal and retry properties.
(defthm fn-bph-status-with-status
  (equal (fn-bp-attempt-status
          (fn-bp-work-attempt (fn-bp-work-with-status work status)))
         status)
  :hints (("Goal" :in-theory
           (enable fn-bp-work-with-status fn-bp-work-with-attempt
                   fn-bp-make-work fn-bp-make-attempt fn-bp-work-attempt
                   fn-bp-attempt-status fn-bp-nth))))

(defthm fn-bph-outstanding-with-status
  (implies (fn-bp-workp config work)
           (equal (fn-bp-work-outstandingp
                   (fn-bp-work-with-status work status))
                  (fn-bp-work-outstandingp work)))
  :hints (("Goal" :in-theory
           (enable fn-bp-workp fn-bp-work-outstandingp
                   fn-bp-work-with-status fn-bp-work-with-attempt
                   fn-bp-make-work fn-bp-make-attempt fn-bp-work-receipt
                   fn-bp-nth))))

(defthm fn-bp-stale-transport-is-no-op
  (implies (let ((attempt (fn-bp-work-attempt
                           (fn-bp-find-work work-id
                                            (fn-bp-state-works s)))))
             (or (not (consp attempt))
                 (not (equal attempt-id (fn-bp-attempt-id attempt)))
                 (not (equal generation
                             (fn-bp-attempt-generation attempt)))))
           (equal (fn-bp-observe-transport
                   s work-id attempt-id generation status)
                  s))
  :hints (("Goal" :in-theory (enable fn-bp-observe-transport))))

(defthm fn-bp-unchecked-receipt-is-no-op
  (equal (fn-bp-prepare-receipt s txid generation receipt nil) s)
  :hints (("Goal" :in-theory (enable fn-bp-prepare-receipt))))

(defthm fn-bp-fenced-complete-is-no-op
  (implies (fn-bp-state-fenced s)
           (equal (fn-bp-complete s txid generation outcome)
                  (fn-bp-make-result s nil)))
  :hints (("Goal" :in-theory (enable fn-bp-complete))))

(defthm fn-bp-expired-is-retryable
  (implies (and (fn-bp-workp config work)
                (consp (fn-bp-work-attempt work))
                (fn-bp-work-outstandingp work))
           (fn-bp-work-retryablep
            (fn-bp-work-with-status work :expired)))
  :hints (("Goal" :in-theory (enable fn-bp-work-retryablep
                                      fn-bp-retryable-statusp))))

(defthm fn-bp-no-contact-is-retryable
  (implies (and (fn-bp-workp config work)
                (consp (fn-bp-work-attempt work))
                (fn-bp-work-outstandingp work))
           (fn-bp-work-retryablep
            (fn-bp-work-with-status work :no-contact)))
  :hints (("Goal" :in-theory (enable fn-bp-work-retryablep
                                      fn-bp-retryable-statusp))))

(defthm fn-bp-policy-retry-status-is-retryable
  (implies (and (fn-bp-workp config work)
                (consp (fn-bp-work-attempt work))
                (fn-bp-work-outstandingp work))
           (fn-bp-work-retryablep
            (fn-bp-work-with-status work :unknown)))
  :hints (("Goal" :in-theory (enable fn-bp-work-retryablep
                                      fn-bp-retryable-statusp))))
