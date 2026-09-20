; fn: invariants of the durable contact/retry scheduler (C2-06).
;
; Safety and conditional progress are stated separately and never share a
; hypothesis.  Nothing below the "Conditional progress" rule mentions
; A-FAIRNESS; FLR-004 forbids a safety property that depends on a contact
; schedule, and books/assumptions.lisp says the same in the A-FAIRNESS comment.
;
; A simulation is not the liveness theorem.  tests/acl2/scheduler-tests.lisp
; runs the starvation trace and the aging trace; the theorems here quantify
; over arbitrary finite observation traces and arbitrary workflow states.

(in-package "ACL2")
(include-book "scheduler")
(include-book "assumptions")
(include-book "bp-workflow-invariants")

; This book is the scheduler cluster's property book, so it opens the cluster's
; own definitions (`fn-sched-vocabulary', exported by books/scheduler) locally.
; It also opens `fn-clock-vocabulary' (deputy board 2026-09-19 bp: clock's
; recognizers, readings and `fn-clock-expiry-decision' are withdrawn on
; include), which the expiry theorems read.  Nothing else is re-enabled: the
; records stay opaque here as everywhere.
(local (in-theory (enable fn-sched-vocabulary fn-clock-vocabulary)))

; -----------------------------------------------------------------------------
; Queue and state preservation
;
; Every transition keeps the queue a queue of items, the promotion queue a list
; of strings, and the state a state.  `fn-sched-admit' is the only transition
; that lengthens the queue, and it refuses at the configured bound.

(defthm fn-sched-find-returns-its-id
  (implies (consp (fn-sched-find id q))
           (equal (fn-sched-item-work-id (fn-sched-find id q)) id)))

(defthm fn-sched-find-is-a-member
  (implies (consp (fn-sched-find id q))
           (member-equal (fn-sched-find id q) q)))

(defthm fn-sched-eligible-is-consp
  (implies (fn-sched-eligiblep item wf) (consp item))
  :rule-classes :forward-chaining)

(defthm fn-sched-itemp-of-bump
  (implies (fn-sched-itemp item)
           (fn-sched-itemp (fn-sched-bump-item item wf sel limit)))
  :hints (("Goal" :in-theory (disable fn-sched-eligiblep))))

(defthm fn-sched-item-listp-of-bump-queue
  (implies (fn-sched-item-listp q)
           (fn-sched-item-listp (fn-sched-bump-queue q wf sel limit)))
  :hints (("Goal" :in-theory (disable fn-sched-bump-item))))

(defthm fn-sched-itemp-of-mark-expired
  (implies (fn-sched-itemp item)
           (fn-sched-itemp (fn-sched-mark-expired item))))

(defthm fn-sched-item-listp-of-expire-queue
  (implies (fn-sched-item-listp q)
           (fn-sched-item-listp (fn-sched-expire-queue id q)))
  :hints (("Goal" :in-theory (disable fn-sched-mark-expired))))

(defthm fn-sched-item-listp-of-append
  (implies (and (fn-sched-item-listp a) (fn-sched-item-listp b))
           (fn-sched-item-listp (append a b))))

(defthm fn-sched-statep-of-admit
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-admit ss id class size)))
  :hints (("Goal" :in-theory (disable fn-sched-queuedp))))

(defthm fn-sched-statep-of-open
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-open ss contact))))

(defthm fn-sched-statep-of-close
  (implies (fn-sched-statep ss) (fn-sched-statep (fn-sched-close ss))))

(defthm fn-sched-statep-of-restart
  (implies (fn-sched-statep ss) (fn-sched-statep (fn-sched-restart ss))))

(defthm fn-sched-statep-of-observe-expiry
  (implies (fn-sched-statep ss)
           (fn-sched-statep
            (fn-sched-observe-expiry ss id ct lt anchor obs)))
  :hints (("Goal" :in-theory (disable fn-sched-expire-queue
                                      fn-clock-expiry-decision))))

(defthm fn-sched-statep-of-with-tick
  (implies (fn-sched-statep ss) (fn-sched-statep (fn-sched-with-tick ss))))

(defthm fn-sched-statep-of-pass-over
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-pass-over ss wf)))
  :hints (("Goal" :in-theory (e/d (fn-sched-pass-over)
                                  (fn-sched-bump-queue fn-sched-next-aged
                                   fn-sched-string-listp
                                   fn-sched-item-listp)))))

(defthm fn-sched-statep-of-take
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-take ss wf selected)))
  :hints (("Goal" :in-theory (e/d (fn-sched-take)
                                  (fn-sched-bump-queue fn-sched-next-aged
                                   fn-sched-string-listp
                                   fn-sched-item-listp)))))

(defthm fn-sched-statep-of-with-decisions
  (implies (and (fn-sched-statep ss) (true-listp d))
           (fn-sched-statep (fn-sched-with-decisions ss d))))

(defthm fn-sched-true-listp-of-record-decision
  (implies (fn-sched-statep ss)
           (true-listp (fn-sched-record-decision ss wf selected attempt-id))))

(defthm fn-sched-statep-of-tick-step
  (implies (fn-sched-statep ss)
           (fn-sched-statep
            (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))))
  :hints (("Goal" :in-theory (e/d (fn-sched-tick-step)
                                  (fn-sched-take fn-sched-pass-over
                                   fn-sched-with-tick fn-sched-with-decisions
                                   fn-sched-record-decision fn-sched-selection
                                   fn-sched-drive-attempt
                                   fn-sched-submit-for-idp
                                   fn-sched-statep fn-sched-string-listp
                                   fn-sched-item-listp)))))

; KEYSTONE.  State preservation over one arbitrary observation.
(defthm fn-sched-step-preserves-state
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-result-ss (fn-sched-step ss wf event))))
  :hints (("Goal" :in-theory (e/d (fn-sched-step)
                                  (fn-sched-admit fn-sched-open fn-sched-close
                                   fn-sched-restart fn-sched-observe-expiry
                                   fn-sched-tick-step fn-sched-with-tick
                                   fn-sched-contact-holdsp fn-bp-nth
                                   fn-sched-statep fn-sched-string-listp
                                   fn-sched-item-listp)))))

; KEYSTONE.  State preservation over an arbitrary finite observation trace.
(defthm fn-sched-trace-preserves-state
  (implies (fn-sched-statep ss)
           (fn-sched-statep (fn-sched-result-ss (fn-sched-trace ss wf events))))
  :hints (("Goal" :induct (fn-sched-trace ss wf events)
           :in-theory (e/d (fn-sched-trace)
                           (fn-sched-step fn-sched-statep
                            fn-sched-string-listp fn-sched-item-listp)))))

; -----------------------------------------------------------------------------
; Queue preservation.  A queued work-id is never dropped, by any observation.

(defthm fn-sched-bump-queue-preserves-queued
  (implies (fn-sched-queuedp id q)
           (fn-sched-queuedp id (fn-sched-bump-queue q wf sel limit)))
  :hints (("Goal" :in-theory (disable fn-sched-eligiblep))))

; With the item record opaque, `fn-sched-find' can no longer see through a
; marked item: this is the footprint of `fn-sched-mark-expired' in accessor
; vocabulary.  Proof vocabulary, withdrawn at export.
(defthm fn-sched-mark-expired-keeps-the-fields
  (and (equal (fn-sched-item-work-id (fn-sched-mark-expired item))
              (fn-sched-item-work-id item))
       (equal (fn-sched-item-class (fn-sched-mark-expired item))
              (fn-sched-item-class item))
       (equal (fn-sched-item-size (fn-sched-mark-expired item))
              (fn-sched-item-size item))
       (equal (fn-sched-item-seq (fn-sched-mark-expired item))
              (fn-sched-item-seq item))
       (equal (fn-sched-item-passes (fn-sched-mark-expired item))
              (fn-sched-item-passes item))
       (equal (fn-sched-item-agedp (fn-sched-mark-expired item))
              (fn-sched-item-agedp item))
       (equal (fn-sched-item-expiredp (fn-sched-mark-expired item)) t)))

(defthm fn-sched-expire-queue-preserves-queued
  (implies (fn-sched-queuedp id q)
           (fn-sched-queuedp id (fn-sched-expire-queue other q)))
  :hints (("Goal" :in-theory (disable fn-sched-mark-expired))))

(defthm fn-sched-append-preserves-queued
  (implies (fn-sched-queuedp id q)
           (fn-sched-queuedp id (append q more))))

(defthm fn-sched-admit-preserves-queued
  (implies (fn-sched-queuedp id (fn-sched-queue ss))
           (fn-sched-queuedp id (fn-sched-queue (fn-sched-admit ss w c s))))
  :hints (("Goal" :in-theory (disable fn-sched-queuedp fn-sched-find))))

; KEYSTONE.  No observation, including expiry and contact loss, removes a work
; from the scheduler's queue.
(defthm fn-sched-step-preserves-queued
  (implies (fn-sched-queuedp id (fn-sched-queue ss))
           (fn-sched-queuedp
            id (fn-sched-queue (fn-sched-result-ss (fn-sched-step ss wf event)))))
  :hints (("Goal" :in-theory
           (e/d (fn-sched-step fn-sched-tick-step fn-sched-open fn-sched-close
                 fn-sched-restart fn-sched-observe-expiry fn-sched-with-tick
                 fn-sched-pass-over fn-sched-take fn-sched-with-decisions)
                (fn-sched-admit fn-sched-bump-queue fn-sched-expire-queue
                 fn-sched-queuedp fn-sched-find fn-sched-next-aged
                 fn-sched-selection fn-sched-drive-attempt
                 fn-sched-record-decision fn-sched-submit-for-idp
                 fn-sched-contact-holdsp fn-clock-expiry-decision fn-bp-nth)))))

(defthm fn-sched-trace-preserves-queued
  (implies (fn-sched-queuedp id (fn-sched-queue ss))
           (fn-sched-queuedp
            id (fn-sched-queue
                (fn-sched-result-ss (fn-sched-trace ss wf events)))))
  :hints (("Goal" :induct (fn-sched-trace ss wf events)
           :in-theory (e/d (fn-sched-trace) (fn-sched-step fn-sched-queuedp)))))

; -----------------------------------------------------------------------------
; Expiry and contact loss never touch the workflow
;
; The scheduler returns the sender's workflow state itself.  Works, attempts,
; receipts, the pending intent, the fence and the node the pins live in are
; therefore identical, not merely equivalent.  `fn-clock-expiry-decision' is
; the only reader of a clock observation, and its `:uncertain' and `:live'
; answers do not even reach the queue.

; KEYSTONE.  Only a contact tick and a relayed transport observation can move
; the workflow at all.  Admission, contact open and close, expiry and restart
; return the sender's workflow state itself.
(defthm fn-sched-only-a-tick-or-a-relay-touches-the-workflow
  (implies (and (not (equal (fn-bp-nth 0 event) :tick))
                (not (equal (fn-bp-nth 0 event) :transport)))
           (equal (fn-sched-result-wf (fn-sched-step ss wf event)) wf))
  :hints (("Goal" :in-theory (e/d (fn-sched-step)
                                  (fn-sched-admit fn-sched-open fn-sched-close
                                   fn-sched-restart fn-sched-observe-expiry
                                   fn-sched-tick-step fn-sched-with-tick
                                   fn-sched-contact-holdsp fn-bp-nth)))))

; KEYSTONE.  The relayed transport observation is `fn-bp-step' itself: the
; scheduler adds no transition of its own and emits no effect.
(defthm fn-sched-transport-relay-is-fn-bp-step
  (and (equal (fn-sched-result-wf
               (fn-sched-step ss wf (fn-sched-transport-event w a g status)))
              (fn-bp-result-state
               (fn-bp-step wf (fn-bp-transport-event w a g status))))
       (equal (fn-sched-result-ss
               (fn-sched-step ss wf (fn-sched-transport-event w a g status)))
              ss)
       (equal (fn-sched-result-effects
               (fn-sched-step ss wf (fn-sched-transport-event w a g status)))
              nil))
  :hints (("Goal" :in-theory (e/d (fn-sched-step fn-sched-transport-event
                                   fn-bp-nth)
                                  (fn-bp-step fn-bp-transport-event
                                   fn-bp-result-state)))))

; KEYSTONE.  An expiry observation releases nothing.  The node carrying the
; archive and forward pins, the works, the receipts and the fence all come back
; unchanged, whatever the clock said.
(defthm fn-sched-expiry-preserves-workflow
  (equal (fn-sched-result-wf
          (fn-sched-step ss wf (fn-sched-expiry-event id ct lt anchor obs)))
         wf)
  :hints (("Goal" :in-theory (e/d (fn-sched-step fn-sched-expiry-event
                                   fn-bp-nth)
                                  (fn-sched-observe-expiry)))))

(defthm fn-sched-expiry-preserves-node-and-pins
  (and (equal (fn-bp-state-node
               (fn-sched-result-wf
                (fn-sched-step ss wf (fn-sched-expiry-event id ct lt a obs))))
              (fn-bp-state-node wf))
       (equal (fn-bp-state-works
               (fn-sched-result-wf
                (fn-sched-step ss wf (fn-sched-expiry-event id ct lt a obs))))
              (fn-bp-state-works wf))
       (equal (fn-bp-state-receipts
               (fn-sched-result-wf
                (fn-sched-step ss wf (fn-sched-expiry-event id ct lt a obs))))
              (fn-bp-state-receipts wf)))
  :hints (("Goal" :in-theory (disable fn-bp-state-node fn-bp-state-works
                                      fn-bp-state-receipts))))

; KEYSTONE.  Contact loss releases nothing either, and it does not discard the
; queue: it clears the open contact and the contact's retry budget only.
(defthm fn-sched-contact-loss-preserves-queue-and-workflow
  (and (equal (fn-sched-result-wf
               (fn-sched-step ss wf (fn-sched-close-event)))
              wf)
       (equal (fn-sched-queue
               (fn-sched-result-ss (fn-sched-step ss wf (fn-sched-close-event))))
              (fn-sched-queue ss))
       (equal (fn-sched-aged
               (fn-sched-result-ss (fn-sched-step ss wf (fn-sched-close-event))))
              (fn-sched-aged ss)))
  :hints (("Goal" :in-theory (e/d (fn-sched-step fn-sched-close-event
                                   fn-sched-close fn-bp-nth)
                                  nil))))

; An expiry mark is not an eligibility test the workflow can see: the work it
; names stays exactly as retryable, or not, as the workflow already had it.
(defthm fn-sched-expiry-does-not-change-work-retryability
  (equal (fn-bp-work-retryablep
          (fn-bp-find-work
           id (fn-bp-state-works
               (fn-sched-result-wf
                (fn-sched-step ss wf (fn-sched-expiry-event w ct lt a obs))))))
         (fn-bp-work-retryablep
          (fn-bp-find-work id (fn-bp-state-works wf))))
  :hints (("Goal" :in-theory (disable fn-bp-work-retryablep fn-bp-find-work
                                      fn-bp-state-works))))

; -----------------------------------------------------------------------------
; Every selected attempt is a durable intent
;
; `fn-bp-step-submit-requires-matching-durable-attempt-completion'
; (books/bp-workflow-invariants.lisp) is the workhorse: a `:submit' leaves
; `fn-bp-step' only from the `:durable' branch of `fn-bp-complete', only when
; the pre-state holds an unfenced pending `:attempt' intent whose transaction
; pair the completion names.  What is added here is that the scheduler's tick
; emits nothing else: its effect list is the effect list of that very
; `fn-bp-step' call, on the state that `fn-bp-prepare-attempt' produced.

(defthm fn-sched-tick-effects-are-the-driven-workflow-effects
  (or (equal (fn-sched-result-effects (fn-sched-tick-step ss wf attempt-id))
             nil)
      (equal (fn-sched-result-effects (fn-sched-tick-step ss wf attempt-id))
             (fn-bp-result-effects
              (fn-sched-drive-attempt
               wf (fn-sched-next-tx ss)
               (fn-sched-item-work-id (fn-sched-selection ss wf))
               attempt-id))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-sched-tick-step)
                (fn-sched-selection fn-sched-drive-attempt fn-sched-take
                 fn-sched-pass-over fn-sched-with-tick fn-sched-with-decisions
                 fn-sched-record-decision fn-sched-submit-for-idp
                 fn-sched-admissiblep fn-bp-result-effects
                 fn-bp-result-state)))))

; KEYSTONE.  Durable intent before submission, lifted to the scheduler.  If a
; contact tick emits a `:submit', then the workflow state the scheduler drove
; held an unfenced pending `:attempt' intent at the scheduler's own transaction
; id, and the effect names that intent's work, attempt id and attempt
; generation and nothing the scheduler chose.
(defthm fn-sched-selected-submit-is-a-workflow-submit
  (implies
   (member-equal e (fn-sched-result-effects
                    (fn-sched-tick-step ss wf attempt-id)))
   (let* ((sel (fn-sched-selection ss wf))
          (s1 (fn-bp-result-state
               (fn-bp-step wf (fn-bp-attempt-prepare-event
                               (fn-sched-next-tx ss) 0
                               (fn-sched-item-work-id sel) attempt-id))))
          (pending (fn-bp-state-pending s1)))
     (and (equal (fn-bp-nth 0 e) :submit)
          (fn-bp-statep s1)
          (not (fn-bp-state-fenced s1))
          (consp pending)
          (equal (fn-bp-pending-kind pending) :attempt)
          (equal (fn-bp-pending-txid pending) (fn-sched-next-tx ss))
          (equal (fn-bp-pending-generation pending) 0)
          (equal e
                 (list :submit
                       (fn-bp-work-id (fn-bp-pending-work pending))
                       (fn-bp-attempt-id
                        (fn-bp-work-attempt (fn-bp-pending-work pending)))
                       (fn-bp-attempt-generation
                        (fn-bp-work-attempt (fn-bp-pending-work pending)))
                       (fn-bp-config-local-eid (fn-bp-state-config s1))
                       (fn-bp-config-peer-eid (fn-bp-state-config s1))
                       (fn-bp-attempt-lifetime
                        (fn-bp-work-attempt (fn-bp-pending-work pending))))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance fn-bp-step-submit-requires-matching-durable-attempt-completion
                     (s (fn-bp-result-state
                         (fn-bp-step wf (fn-bp-attempt-prepare-event
                                         (fn-sched-next-tx ss) 0
                                         (fn-sched-item-work-id
                                          (fn-sched-selection ss wf))
                                         attempt-id))))
                     (event (fn-bp-storage-complete-event
                             (fn-sched-next-tx ss) 0 :durable))))
    :in-theory
    (e/d (fn-sched-tick-step fn-sched-drive-attempt fn-sched-submit-for-idp
          fn-sched-submit-effectp fn-bp-storage-complete-event
          fn-bp-event-kind fn-bp-nth member-equal)
         (fn-sched-selection fn-sched-take fn-sched-pass-over
          fn-sched-with-tick fn-sched-with-decisions fn-sched-record-decision
          fn-sched-admissiblep fn-bp-step fn-bp-statep fn-bp-state-pending
          fn-bp-state-fenced fn-bp-pending-kind fn-bp-pending-txid
          fn-bp-pending-generation fn-bp-pending-work fn-bp-work-id
          fn-bp-work-attempt fn-bp-attempt-id fn-bp-attempt-generation
          fn-bp-attempt-lifetime fn-bp-state-config fn-bp-config-local-eid
          fn-bp-config-peer-eid fn-bp-result-state fn-bp-result-effects)))))

; A tick that the workflow refuses changes nothing at all: no retry is charged,
; no decision is recorded and the workflow is returned itself.  This is what
; keeps "retries bounded per contact" from being an accounting fiction.
(defthm fn-sched-refused-submit-is-a-no-op
  (implies (and (consp (fn-sched-selection ss wf))
                (not (fn-sched-submit-for-idp
                      (fn-sched-item-work-id (fn-sched-selection ss wf))
                      (fn-bp-result-effects
                       (fn-sched-drive-attempt
                        wf (fn-sched-next-tx ss)
                        (fn-sched-item-work-id (fn-sched-selection ss wf))
                        attempt-id))))
                (fn-sched-admissiblep ss))
           (and (equal (fn-sched-result-ss
                        (fn-sched-tick-step ss wf attempt-id))
                       ss)
                (equal (fn-sched-result-wf
                        (fn-sched-tick-step ss wf attempt-id))
                       wf)
                (equal (fn-sched-result-effects
                        (fn-sched-tick-step ss wf attempt-id))
                       nil)))
  :hints (("Goal" :in-theory
           (e/d (fn-sched-tick-step)
                (fn-sched-selection fn-sched-drive-attempt fn-sched-take
                 fn-sched-pass-over fn-sched-with-tick fn-sched-with-decisions
                 fn-sched-record-decision fn-sched-submit-for-idp
                 fn-sched-admissiblep fn-bp-result-effects
                 fn-bp-result-state)))))

; Retries are charged one per selected attempt and never exceed the contact's
; configured bound, because an inadmissible tick selects nothing.
(defthm fn-sched-retries-stay-within-the-contact-bound
  (implies (and (fn-sched-statep ss)
                (<= (fn-sched-retries ss)
                    (fn-sched-retry-bound (fn-sched-conf ss))))
           (<= (fn-sched-retries
                (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id)))
               (fn-sched-retry-bound (fn-sched-conf ss))))
  :hints (("Goal" :in-theory
           (e/d (fn-sched-tick-step fn-sched-take fn-sched-pass-over
                 fn-sched-with-tick fn-sched-with-decisions
                 fn-sched-admissiblep)
                (fn-sched-selection fn-sched-drive-attempt fn-sched-bump-queue
                 fn-sched-next-aged fn-sched-record-decision
                 fn-sched-submit-for-idp fn-bp-result-effects
                 fn-bp-result-state)))))

; The host calls `fn-sched-selection', then the journal's durable attempt, then
; `fn-sched-take'.  This is the equation that makes `fn-sched-tick-step' --- the
; subject of the submit theorem above --- the composition of the three
; functions `host/scheduler-host.lisp' calls (`fn-sched-host-selection',
; `fn-sched-host-decision-octets' plus the journal's attempt, and
; `fn-sched-host-commit').
(defthm fn-sched-tick-step-is-select-drive-take
  (implies (and (fn-sched-admissiblep ss)
                (consp (fn-sched-selection ss wf))
                (fn-sched-drive-okp ss wf attempt-id))
           (and (equal (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))
                       (fn-sched-with-decisions
                        (fn-sched-take ss wf (fn-sched-selection ss wf))
                        (fn-sched-record-decision
                         ss wf (fn-sched-selection ss wf) attempt-id)))
                (equal (fn-sched-result-wf (fn-sched-tick-step ss wf attempt-id))
                       (fn-bp-result-state
                        (fn-sched-drive-attempt
                         wf (fn-sched-next-tx ss)
                         (fn-sched-item-work-id (fn-sched-selection ss wf))
                         attempt-id)))))
  :hints (("Goal" :in-theory
           (e/d (fn-sched-tick-step fn-sched-drive-okp)
                (fn-sched-selection fn-sched-drive-attempt fn-sched-take
                 fn-sched-with-decisions fn-sched-record-decision
                 fn-sched-submit-for-idp fn-sched-admissiblep
                 fn-bp-result-effects fn-bp-result-state)))))

; -----------------------------------------------------------------------------
; The aging bound
;
; The promotion queue is drained from the head.  The measure is the position of
; a work-id in it: appending promotions at the tail cannot move it, and every
; admissible tick either selects it or removes at least the entry in front.

(defthm fn-sched-pos-is-natural
  (natp (fn-sched-pos x lst))
  :rule-classes :type-prescription)

(defthm fn-sched-pos-of-cons-other
  (implies (not (equal x a))
           (equal (fn-sched-pos x (cons a lst))
                  (+ 1 (fn-sched-pos x lst)))))

(defthm fn-sched-pos-bounded-by-len
  (<= (fn-sched-pos x lst) (len lst))
  :rule-classes :linear)

(defthm fn-sched-pos-of-append-when-member
  (implies (member-equal x a)
           (equal (fn-sched-pos x (append a b)) (fn-sched-pos x a))))

(defthm fn-sched-aged-advance-keeps-eligible-member
  (implies (and (member-equal w aged)
                (fn-sched-eligiblep (fn-sched-find w queue) wf))
           (member-equal w (fn-sched-aged-advance aged queue wf)))
  :hints (("Goal" :in-theory (disable fn-sched-eligiblep fn-sched-find))))

; The promotion queue is drained from the head: a member that is not the head
; is a member of the tail.  With `fn-sched-aged-advance' held closed this is
; the only way the goal of `fn-sched-promotion-position-decreases' reaches the
; `cdr' the tick appends its promotions to.
; `:rule-classes nil': as a rewrite it backchains from `(member-equal w (cdr x))'
; to `(member-equal w x)' and matches itself on every nested `cdr', which sent
; `fn-sched-promotion-position-decreases' into an unbounded induction descent
; (certify-20260920T011543Z-94761).  Cited by `:use' at its one instance.
(defthm fn-sched-member-of-cdr-when-not-the-car
  (implies (and (member-equal w lst) (not (equal w (car lst))))
           (member-equal w (cdr lst)))
  :rule-classes nil)

(defthm fn-sched-member-of-append-left
  (implies (member-equal w a) (member-equal w (append a b))))

; The consp consequence, as its own rule: in the deep case split of
; `fn-sched-promotion-position-decreases' the `:use' hypothesis has already been
; rewritten away, and the branch closes only if this fires there.
(defthm fn-sched-aged-advance-consp-when-an-eligible-member-exists
  (implies (and (member-equal w aged)
                (fn-sched-eligiblep (fn-sched-find w queue) wf))
           (consp (fn-sched-aged-advance aged queue wf)))
  :hints (("Goal" :use fn-sched-aged-advance-keeps-eligible-member
           :in-theory (disable fn-sched-eligiblep fn-sched-find
                               fn-sched-aged-advance))))

(defthm fn-sched-aged-advance-head-is-eligible
  (implies (consp (fn-sched-aged-advance aged queue wf))
           (fn-sched-eligiblep
            (fn-sched-find (car (fn-sched-aged-advance aged queue wf)) queue)
            wf))
  :hints (("Goal" :in-theory (disable fn-sched-eligiblep fn-sched-find))))

(defthm fn-sched-pos-of-aged-advance
  (implies (fn-sched-eligiblep (fn-sched-find w queue) wf)
           (<= (fn-sched-pos w (fn-sched-aged-advance aged queue wf))
               (fn-sched-pos w aged)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-sched-eligiblep fn-sched-find))))

; The head of the advanced promotion queue is exactly what selection takes,
; whenever the promotion queue is not empty.
(defthm fn-sched-selection-is-the-promotion-head
  (implies (and (fn-sched-admissiblep ss)
                (consp (fn-sched-aged-advance (fn-sched-aged ss)
                                              (fn-sched-queue ss) wf)))
           (equal (fn-sched-item-work-id (fn-sched-selection ss wf))
                  (car (fn-sched-aged-advance (fn-sched-aged ss)
                                              (fn-sched-queue ss) wf))))
  :hints (("Goal" :in-theory (e/d (fn-sched-selection)
                                  (fn-sched-aged-advance fn-sched-admissiblep
                                   fn-sched-eligiblep fn-sched-priority-pick))
           :use ((:instance fn-sched-find-returns-its-id
                            (id (car (fn-sched-aged-advance
                                      (fn-sched-aged ss)
                                      (fn-sched-queue ss) wf)))
                            (q (fn-sched-queue ss)))
                 (:instance fn-sched-aged-advance-head-is-eligible
                            (aged (fn-sched-aged ss))
                            (queue (fn-sched-queue ss)))
                 ; the opaque item no longer yields `consp' by type reasoning
                 (:instance fn-sched-eligible-is-consp
                            (item (fn-sched-find
                                   (car (fn-sched-aged-advance
                                         (fn-sched-aged ss)
                                         (fn-sched-queue ss) wf))
                                   (fn-sched-queue ss))))))))

; And it is a queue item, not nil: with the item record opaque this no longer
; follows from the work-id equality above.
(defthm fn-sched-selection-is-consp-when-the-promotion-queue-is-not-empty
  (implies (and (fn-sched-admissiblep ss)
                (consp (fn-sched-aged-advance (fn-sched-aged ss)
                                              (fn-sched-queue ss) wf)))
           (consp (fn-sched-selection ss wf)))
  :hints (("Goal" :in-theory (e/d (fn-sched-selection)
                                  (fn-sched-aged-advance fn-sched-admissiblep
                                   fn-sched-eligiblep fn-sched-priority-pick
                                   fn-sched-find))
           :use ((:instance fn-sched-aged-advance-head-is-eligible
                            (aged (fn-sched-aged ss))
                            (queue (fn-sched-queue ss)))
                 (:instance fn-sched-eligible-is-consp
                            (item (fn-sched-find
                                   (car (fn-sched-aged-advance
                                         (fn-sched-aged ss)
                                         (fn-sched-queue ss) wf))
                                   (fn-sched-queue ss))))))))

; The member half of the keystone below, isolated: inside the keystone's own
; case split this goal sat two hundred levels deep and the prover descended
; without end (certify-20260920T011543Z-94761, -20260920T014616Z-7729).
; Proved here with the tick, the advance and the promotions all closed.
(defthm fn-sched-next-aged-keeps-a-non-selected-eligible-member
  (implies (and (member-equal w (fn-sched-aged ss))
                (fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)
                (not (equal w selected-id)))
           (member-equal w (fn-sched-next-aged ss wf selected-id)))
  :hints (("Goal" :in-theory (e/d (fn-sched-next-aged)
                                  (fn-sched-aged-advance fn-sched-promotions
                                   fn-sched-eligiblep fn-sched-find))
           :use ((:instance fn-sched-aged-advance-keeps-eligible-member
                            (aged (fn-sched-aged ss))
                            (queue (fn-sched-queue ss)))
                 (:instance fn-sched-member-of-cdr-when-not-the-car
                            (lst (fn-sched-aged-advance (fn-sched-aged ss)
                                                        (fn-sched-queue ss)
                                                        wf)))))))

; KEYSTONE.  One admissible tick either selects a promoted work or moves it
; strictly closer to the head of the promotion queue.
(defthm fn-sched-promotion-position-decreases
  (implies (and (fn-sched-admissiblep ss)
                (fn-sched-drive-okp ss wf attempt-id)
                (member-equal w (fn-sched-aged ss))
                (fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)
                (not (fn-sched-submit-for-idp
                      w (fn-sched-result-effects
                         (fn-sched-tick-step ss wf attempt-id)))))
           (and (member-equal
                 w (fn-sched-aged
                    (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))))
                (< (fn-sched-pos
                    w (fn-sched-aged
                       (fn-sched-result-ss
                        (fn-sched-tick-step ss wf attempt-id))))
                   (fn-sched-pos w (fn-sched-aged ss)))))
  :hints (("Goal" :in-theory
           (e/d (fn-sched-tick-step fn-sched-take fn-sched-with-decisions
                 fn-sched-next-aged fn-sched-drive-okp)
                (fn-sched-aged-advance fn-sched-eligiblep fn-sched-find
                 fn-sched-admissiblep fn-sched-promotions fn-sched-bump-queue
                 fn-sched-drive-attempt fn-sched-record-decision
                 fn-sched-selection fn-bp-result-effects fn-bp-result-state))
           :cases ((equal w (fn-sched-item-work-id (fn-sched-selection ss wf))))
           :use ((:instance fn-sched-selection-is-the-promotion-head)
                 (:instance
                  fn-sched-selection-is-consp-when-the-promotion-queue-is-not-empty)
                 (:instance fn-sched-aged-advance-keeps-eligible-member
                            (aged (fn-sched-aged ss))
                            (queue (fn-sched-queue ss)))
                 (:instance fn-sched-pos-of-aged-advance
                            (aged (fn-sched-aged ss))
                            (queue (fn-sched-queue ss)))
                 (:instance
                  fn-sched-next-aged-keeps-a-non-selected-eligible-member
                  (selected-id (fn-sched-item-work-id
                                (fn-sched-selection ss wf))))))))

; KEYSTONE.  A promoted work that stays eligible is selected within one more
; tick than its position in the promotion queue.
(defthm fn-sched-promoted-work-is-selected-within-its-position
  (implies (and (member-equal w (fn-sched-aged ss))
                (fn-sched-contact-runp ss wf n attempt-id)
                (fn-sched-eligible-runp ss wf n attempt-id w)
                (< (fn-sched-pos w (fn-sched-aged ss)) n))
           (fn-sched-selected-withinp ss wf n attempt-id w))
  :hints (("Goal"
           :induct (fn-sched-selected-withinp ss wf n attempt-id w)
           :in-theory (e/d (fn-sched-contact-runp fn-sched-eligible-runp
                            fn-sched-selected-withinp fn-sched-eligible-idp)
                           (fn-sched-tick-step fn-sched-pos fn-sched-eligiblep
                            fn-sched-find fn-sched-admissiblep
                            fn-sched-drive-okp fn-sched-submit-for-idp)))))

; KEYSTONE.  The aging bound with N a function of configuration.  A work that
; has reached the promotion queue, while the promotion queue fits inside the
; configured queue bound, is selected within `queue-bound' + 1 admissible
; contact ticks on which it stays eligible.  Priority inversion is bounded;
; the deterministic order cannot postpone it further.
(defthm fn-sched-aging-bound
  (implies (and (fn-sched-aged-fitsp ss)
                (member-equal w (fn-sched-aged ss))
                (fn-sched-contact-runp ss wf n attempt-id)
                (fn-sched-eligible-runp ss wf n attempt-id w)
                (< (nfix (fn-sched-queue-bound (fn-sched-conf ss))) n))
           (fn-sched-selected-withinp ss wf n attempt-id w))
  :hints (("Goal" :in-theory (e/d (fn-sched-aged-fitsp)
                                  (fn-sched-pos fn-sched-contact-runp
                                   fn-sched-eligible-runp
                                   fn-sched-selected-withinp))
           :use ((:instance fn-sched-promoted-work-is-selected-within-its-position)
                 (:instance fn-sched-pos-bounded-by-len
                            (x w) (lst (fn-sched-aged ss)))))))

; The promotion half of the L + Q horizon, at one tick: an eligible work that
; is passed over on the tick at which its pass count reaches the configured
; aging limit enters the promotion queue on that tick.
(defthm fn-sched-passed-over-work-reaches-the-promotion-queue
  (implies (and (fn-sched-admissiblep ss)
                (fn-sched-drive-okp ss wf attempt-id)
                (consp (fn-sched-selection ss wf))
                (not (equal (fn-sched-item-work-id (fn-sched-selection ss wf))
                            w))
                (fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)
                (member-equal (fn-sched-find w (fn-sched-queue ss))
                              (fn-sched-queue ss))
                (not (fn-sched-item-agedp (fn-sched-find w (fn-sched-queue ss))))
                (<= (nfix (fn-sched-aging-limit (fn-sched-conf ss)))
                    (+ 1 (nfix (fn-sched-item-passes
                                (fn-sched-find w (fn-sched-queue ss)))))))
           (member-equal
            w (fn-sched-aged
               (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id)))))
  :hints (("Goal" :in-theory
           (e/d (fn-sched-tick-step fn-sched-take fn-sched-with-decisions
                 fn-sched-next-aged fn-sched-drive-okp)
                (fn-sched-aged-advance fn-sched-eligiblep fn-sched-find
                 fn-sched-admissiblep fn-sched-bump-queue
                 fn-sched-drive-attempt fn-sched-record-decision
                 fn-sched-selection fn-bp-result-effects fn-bp-result-state))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Conditional progress
;
; Everything above is safety and takes no fairness hypothesis.  The theorem
; below is the only one that mentions A-FAIRNESS, and it is conditional on all
; four of the hypotheses C3-03 names:
;
;   contacts recur      `fn-assume-fairness-contact-index' is a natural number
;                       of steps (books/assumptions.lisp), so the horizon the
;                       schedule must cover is finite;
;   capacity suffices   `fn-sched-contact-runp' -- each tick is admissible (a
;                       contact is open, the retry budget is not spent) and the
;                       durable store accepts the intent the scheduler prepares;
;   the peer accepts    `fn-sched-eligible-runp' -- the work is not closed by a
;                       receipt and is not expired at any of those ticks;
;   the work is queued  it has reached the promotion queue and the promotion
;                       queue fits the configured bound.
;
; Drop any one and the conclusion fails; tests/acl2/scheduler-tests.lisp has
; the must-fail case for each.  This is not the simulation in
; tests/test_scheduler.py, which runs one trace.

(defthm fn-sched-conditional-progress-under-a-fairness
  (implies (and (fn-sched-aged-fitsp ss)
                (member-equal w (fn-sched-aged ss))
                (equal n (+ 1
                            (nfix (fn-sched-queue-bound (fn-sched-conf ss)))
                            (fn-assume-fairness-contact-index route schedule)))
                (fn-sched-contact-runp ss wf n attempt-id)
                (fn-sched-eligible-runp ss wf n attempt-id w))
           (fn-sched-selected-withinp ss wf n attempt-id w))
  :hints (("Goal"
           :use ((:instance fn-sched-aging-bound)
                 (:instance fn-assume-fairness-contact-index-is-finite))
           :in-theory (e/d nil
                           (fn-sched-aging-bound fn-sched-aged-fitsp
                            fn-sched-pos fn-sched-contact-runp
                            fn-sched-eligible-runp fn-sched-selected-withinp
                            fn-assume-fairness-contact-index
                            fn-sched-queue-bound fn-sched-conf)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md §2)
;
; The keystones above and the small arithmetic facts about `fn-sched-pos' (the
; list-recursive position function the aging proofs induct on) leave this book
; enabled.  Everything else here is proof vocabulary for the aging bound; it is
; withdrawn under one name so that a book above re-opens exactly it.

(deftheory fn-sched-invariants-vocabulary
  '(fn-sched-find-returns-its-id fn-sched-find-is-a-member
    fn-sched-itemp-of-bump fn-sched-item-listp-of-bump-queue
    fn-sched-itemp-of-mark-expired fn-sched-item-listp-of-expire-queue
    fn-sched-mark-expired-keeps-the-fields
    fn-sched-item-listp-of-append
    fn-sched-statep-of-admit fn-sched-statep-of-open fn-sched-statep-of-close
    fn-sched-statep-of-restart fn-sched-statep-of-observe-expiry
    fn-sched-statep-of-with-tick fn-sched-statep-of-pass-over
    fn-sched-statep-of-take fn-sched-statep-of-with-decisions
    fn-sched-true-listp-of-record-decision fn-sched-statep-of-tick-step
    fn-sched-bump-queue-preserves-queued fn-sched-expire-queue-preserves-queued
    fn-sched-append-preserves-queued fn-sched-admit-preserves-queued
    fn-sched-member-of-append-left
    fn-sched-next-aged-keeps-a-non-selected-eligible-member
    fn-sched-aged-advance-keeps-eligible-member
    fn-sched-aged-advance-consp-when-an-eligible-member-exists
    fn-sched-aged-advance-head-is-eligible fn-sched-pos-of-aged-advance
    fn-sched-pos-of-cons-other fn-sched-pos-of-append-when-member
    fn-sched-selection-is-the-promotion-head
    fn-sched-selection-is-consp-when-the-promotion-queue-is-not-empty
    fn-sched-promotion-position-decreases
    fn-sched-promoted-work-is-selected-within-its-position))

(in-theory (disable fn-sched-invariants-vocabulary))
