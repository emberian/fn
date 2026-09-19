; Executable BPv7 durable-outbox workflow scenarios.
(in-package "ACL2")
(include-book "../../books/bp-workflow-transport-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bp-groups* '("fn.letters"))
(defconst *bp-payload* '(72 105 13 10))
(defconst *bp-node-empty* (fn-node-initial-state *bp-groups* 16))
(defconst *bp-node-prepared*
  (fn-node-prepare *bp-node-empty* 9 "<bp@example.invalid>" *bp-payload*
                   *bp-groups* "archive-bp" "subject-bp" "release-bp" 4))
(defconst *bp-node-committed*
  (fn-node-complete *bp-node-prepared* 0 9 :durable))
(defconst *bp-config*
  (fn-bp-make-config "dtn://home/fn" "dtn://peer/fn" "policy-1"
                     "receipt-authority" 1000 "home-incarnation-1"
                     "authorization-context-1"))
(defconst *bp-empty* (fn-bp-initial-state *bp-node-committed* *bp-config*))

(assert-event (fn-bp-statep *bp-empty*))
(assert-event (equal (fn-bp-state-node *bp-empty*) *bp-node-committed*))

; Enqueue is a separate durable transaction after local article acceptance.
(defconst *bp-enqueue-pending*
  (fn-bp-prepare-enqueue *bp-empty* 10 0 "work-1" "<bp@example.invalid>"
                         "forward-1" "policy-1" "terms-1"))
(assert-event (consp (fn-bp-state-pending *bp-enqueue-pending*)))
(assert-event
 (fn-ag-member (fn-bp-make-tx-key 10 0)
               (fn-bp-state-used-txs *bp-enqueue-pending*)))
(defconst *bp-enqueue-result* (fn-bp-complete *bp-enqueue-pending* 10 0 :durable))
(defconst *bp-enqueued* (fn-bp-result-state *bp-enqueue-result*))
(assert-event (equal (fn-bp-result-effects *bp-enqueue-result*)
                     '((:enqueue-ack "work-1"))))
(assert-event (fn-bp-work-outstandingp
               (fn-bp-find-work "work-1" (fn-bp-state-works *bp-enqueued*))))

; A known abort consumes the pair.  Reusing it cannot create a new pending
; attempt, and replaying its old durable completion cannot emit :submit.
(defconst *bp-attempt-abort-pending*
  (fn-bp-prepare-attempt *bp-enqueued* 11 0 "work-1" "attempt-abort"))
(defconst *bp-attempt-aborted*
  (fn-bp-result-state
   (fn-bp-complete *bp-attempt-abort-pending* 11 0 :aborted)))
(assert-event
 (fn-ag-member (fn-bp-make-tx-key 11 0)
               (fn-bp-state-used-txs *bp-attempt-aborted*)))
(assert-event
 (equal (fn-bp-prepare-attempt *bp-attempt-aborted* 11 0
                               "work-1" "attempt-reuse")
        *bp-attempt-aborted*))
(assert-event
 (equal (fn-bp-result-effects
         (fn-bp-complete *bp-attempt-aborted* 11 0 :durable))
        nil))

; A fresh durable attempt intent is the only point that emits the BPA submit
; effect.  A BPA API reply and delivery remain transport observations only.
(defconst *bp-attempt-pending*
  (fn-bp-prepare-attempt *bp-attempt-aborted* 12 0 "work-1" "attempt-0"))
(defconst *bp-attempt-result*
  (fn-bp-complete *bp-attempt-pending* 12 0 :durable))
(defconst *bp-attempted* (fn-bp-result-state *bp-attempt-result*))
(assert-event (equal (fn-bp-result-effects *bp-attempt-result*)
                     '((:submit "work-1" "attempt-0" 0
                                "dtn://home/fn" "dtn://peer/fn" 1000))))
(defconst *bp-submit-replied*
  (fn-bp-observe-transport *bp-attempted* "work-1" "attempt-0" 0
                           :bpa-submit-replied))
(defconst *bp-delivered*
  (fn-bp-observe-transport *bp-submit-replied* "work-1" "attempt-0" 0
                           :delivered))
(assert-event (fn-bp-work-outstandingp
               (fn-bp-find-work "work-1" (fn-bp-state-works *bp-delivered*))))
(assert-event (equal (fn-bp-state-receipts *bp-delivered*) nil))

; A policy retry keeps delivered-without-application-receipt live.  Stale
; generation observations cannot mutate the fresh attempt.
(defconst *bp-retryable*
  (fn-bp-request-retry *bp-delivered* "work-1" "attempt-0" 0 "policy-1"))
(assert-event (fn-bp-work-retryablep
               (fn-bp-find-work "work-1" (fn-bp-state-works *bp-retryable*))))
(defconst *bp-uncertain-pending*
  (fn-bp-prepare-attempt *bp-retryable* 13 0 "work-1" "attempt-1"))
(defconst *bp-uncertain-result*
  (fn-bp-complete *bp-uncertain-pending* 13 0 :indeterminate))
(defconst *bp-uncertain* (fn-bp-result-state *bp-uncertain-result*))
(assert-event (equal (fn-bp-state-fenced *bp-uncertain*) t))
(assert-event
 (equal (fn-bp-complete *bp-uncertain* 13 0 :durable)
        (fn-bp-make-result *bp-uncertain* nil)))
(assert-event (equal (fn-bp-state-fenced (fn-bp-restart *bp-uncertain*)) t))
(defconst *bp-recovered-attempt-result*
  (fn-bp-recover *bp-uncertain* 13 0 :committed))
(defconst *bp-recovered-attempt*
  (fn-bp-result-state *bp-recovered-attempt-result*))
(assert-event (equal (fn-bp-result-effects *bp-recovered-attempt-result*) nil))
(assert-event (equal (fn-bp-attempt-status
                      (fn-bp-work-attempt
                       (fn-bp-find-work
                        "work-1" (fn-bp-state-works *bp-recovered-attempt*))))
                     :unknown))
(assert-event
 (equal (fn-bp-observe-transport *bp-recovered-attempt*
                                 "work-1" "attempt-0" 0 :expired)
        *bp-recovered-attempt*))

; Receipt admission requires an explicit A-POLICY decision and an exact match
; to the durable work/config context.  Its uncertain publication is fenced and
; resolved only by recovery.
(defconst *bp-receipt*
  (fn-bp-make-receipt "receipt-1" "work-1" "subject-bp"
                      "receipt-authority" "dtn://peer/fn" "policy-1"
                      "home-incarnation-1" "authorization-context-1"
                      "terms-1"))
(assert-event
 (equal (fn-bp-prepare-receipt *bp-recovered-attempt* 14 0 *bp-receipt* nil)
        *bp-recovered-attempt*))
(defconst *bp-receipt-pending*
  (fn-bp-prepare-receipt *bp-recovered-attempt* 14 0 *bp-receipt* t))
(defconst *bp-receipt-uncertain*
  (fn-bp-result-state
   (fn-bp-complete *bp-receipt-pending* 14 0 :indeterminate)))
(assert-event
 (equal (fn-bp-complete *bp-receipt-uncertain* 14 0 :durable)
        (fn-bp-make-result *bp-receipt-uncertain* nil)))
(defconst *bp-receipt-recovered-result*
  (fn-bp-recover *bp-receipt-uncertain* 14 0 :committed))
(defconst *bp-receipted* (fn-bp-result-state *bp-receipt-recovered-result*))
(assert-event (equal (fn-bp-result-effects *bp-receipt-recovered-result*)
                     '((:receipt-ack "receipt-1"))))
(assert-event (equal (fn-bp-work-receipt
                      (fn-bp-find-work "work-1"
                                       (fn-bp-state-works *bp-receipted*)))
                     *bp-receipt*))
(assert-event (equal (fn-bp-state-node *bp-receipted*) *bp-node-committed*))

; An arbitrary finite mixed trace remains in the recognized state domain and
; cannot alter the already accepted node/article/archive state.
(defconst *bp-mixed-events*
  (list (fn-bp-transport-event "work-1" "attempt-1" 1 :expired)
        (fn-bp-no-contact-event "work-1" "attempt-1" 1)
        (fn-bp-restart-event)
        '(:malformed)
        (fn-bp-storage-complete-event 11 0 :durable)))
(defconst *bp-mixed-result* (fn-bp-trace *bp-receipted* *bp-mixed-events*))
(assert-event (fn-bp-statep *bp-mixed-result*))
(assert-event (equal (fn-bp-state-node *bp-mixed-result*) *bp-node-committed*))
(assert-event (equal (fn-bp-work-receipt
                      (fn-bp-find-work "work-1"
                                       (fn-bp-state-works *bp-mixed-result*)))
                     *bp-receipt*))

; ---------------------------------------------------------------------------
; F11: a transport observation never moves an attempt backward in its
; lifecycle (fn-bp-observe-transport-never-moves-status-backward,
; fn-bp-observe-transport-never-returns-to-intent).  Witnesses branch from the
; live attempt-0 after its BPA reply.
(defconst *bp-accepted*
  (fn-bp-observe-transport *bp-submit-replied* "work-1" "attempt-0" 0
                           :bpa-accepted))
(defun fn-bpt-status (s)
  (fn-bp-attempt-status
   (fn-bp-work-attempt (fn-bp-find-work "work-1" (fn-bp-state-works s)))))
(assert-event (equal (fn-bpt-status *bp-accepted*) :bpa-accepted))
; The defect: an accepted attempt regressing to :intent was admitted.  Refused.
(assert-event
 (equal (fn-bp-observe-transport *bp-accepted* "work-1" "attempt-0" 0 :intent)
        *bp-accepted*))
(must-fail (assert-event (fn-bp-transport-transition-okp :bpa-accepted :intent)))
; Any backward step is refused, not only the step to :intent.
(defconst *bp-forwarded*
  (fn-bp-observe-transport *bp-accepted* "work-1" "attempt-0" 0 :forwarded))
(assert-event (equal (fn-bpt-status *bp-forwarded*) :forwarded))
(assert-event
 (equal (fn-bp-observe-transport *bp-forwarded* "work-1" "attempt-0" 0
                                 :bpa-submit-replied)
        *bp-forwarded*))
(assert-event
 (equal (fn-bp-observe-transport *bp-forwarded* "work-1" "attempt-0" 0
                                 :bpa-accepted)
        *bp-forwarded*))
(must-fail (assert-event (fn-bp-transport-transition-okp :forwarded :attempted)))
; The relation is not "refuse everything": forward steps are accepted and a
; repeated observation is a no-op.
(assert-event
 (equal (fn-bpt-status (fn-bp-observe-transport *bp-forwarded* "work-1"
                                                "attempt-0" 0 :delivered))
        :delivered))
(assert-event
 (equal (fn-bp-observe-transport *bp-forwarded* "work-1" "attempt-0" 0
                                 :forwarded)
        *bp-forwarded*))
(assert-event (fn-bp-transport-transition-okp :bpa-accepted :forwarded))
(assert-event (< (fn-bp-status-rank :bpa-accepted) (fn-bp-status-rank :forwarded)))
; :delivered leaves only through policy retry; a retryable status leaves only
; through a new attempt.  Both were already refused and remain refused.
(assert-event
 (equal (fn-bp-observe-transport *bp-delivered* "work-1" "attempt-0" 0 :expired)
        *bp-delivered*))
(assert-event (equal (fn-bpt-status *bp-retryable*) :unknown))
(assert-event
 (equal (fn-bp-observe-transport *bp-retryable* "work-1" "attempt-0" 0
                                 :delivered)
        *bp-retryable*))
(must-fail (assert-event (fn-bp-transport-transition-okp :delivered :expired)))
(must-fail (assert-event (fn-bp-transport-transition-okp :unknown :delivered)))
; The rank conclusion, executed on a refused and on an accepted observation.
(assert-event
 (<= (fn-bp-status-rank (fn-bpt-status *bp-accepted*))
     (fn-bp-status-rank
      (fn-bpt-status (fn-bp-observe-transport *bp-accepted* "work-1"
                                              "attempt-0" 0 :intent)))))
(assert-event
 (<= (fn-bp-status-rank (fn-bpt-status *bp-accepted*))
     (fn-bp-status-rank (fn-bpt-status *bp-forwarded*))))

; ---------------------------------------------------------------------------
; D8: :submit leaves fn-bp-step only from the :durable completion of the
; pending attempt intent (fn-bp-step-submit-requires-matching-durable-
; attempt-completion).  *bp-attempt-pending* holds the intent without an
; outcome: prepared, and in the host's terms persisted but not yet durable.
(defun fn-bpt-submitp (effects)
  (and (consp effects) (equal (fn-bp-nth 0 (car effects)) :submit)))
(assert-event (fn-bpt-submitp (fn-bp-result-effects *bp-attempt-result*)))
(assert-event (equal (len (fn-bp-result-effects *bp-attempt-result*)) 1))
; The pending intent alone yields no :submit under any other event.
(assert-event
 (not (fn-bpt-submitp
       (fn-bp-result-effects
        (fn-bp-step *bp-attempt-pending*
                    (fn-bp-storage-complete-event 12 0 :aborted))))))
(assert-event
 (not (fn-bpt-submitp
       (fn-bp-result-effects
        (fn-bp-step *bp-attempt-pending*
                    (fn-bp-storage-complete-event 12 0 :indeterminate))))))
(assert-event
 (not (fn-bpt-submitp
       (fn-bp-result-effects
        (fn-bp-step *bp-attempt-pending*
                    (fn-bp-storage-complete-event 99 0 :durable))))))
(assert-event
 (not (fn-bpt-submitp
       (fn-bp-result-effects
        (fn-bp-step *bp-attempt-pending*
                    (fn-bp-transport-event "work-1" "attempt-0" 0
                                           :delivered))))))
(assert-event
 (not (fn-bpt-submitp
       (fn-bp-result-effects
        (fn-bp-step *bp-attempt-pending* (fn-bp-restart-event))))))
; After a restart the fenced intent found committed installs :unknown and
; still emits no :submit: the attempt has to be retried under policy.
(must-fail
 (assert-event
  (fn-bpt-submitp
   (fn-bp-result-effects
    (fn-bp-step (fn-bp-restart *bp-attempt-pending*)
                (fn-bp-storage-recover-event 12 0 :committed))))))
; Teeth for the hypothesis (equal (fn-bp-nth 0 e) :submit): an :enqueue-ack
; is emitted from a pending :enqueue, so the conclusion's pending kind fails.
(assert-event (member-equal '(:enqueue-ack "work-1")
                            (fn-bp-result-effects *bp-enqueue-result*)))
(must-fail
 (assert-event
  (equal (fn-bp-pending-kind (fn-bp-state-pending *bp-enqueue-pending*))
         :attempt)))
; Teeth for the membership hypothesis: the initial state emits nothing, and
; its conclusion (a pending intent) fails.
(assert-event
 (equal (fn-bp-result-effects
         (fn-bp-step *bp-empty* (fn-bp-storage-complete-event 12 0 :durable)))
        nil))
(must-fail (assert-event (consp (fn-bp-state-pending *bp-empty*))))
