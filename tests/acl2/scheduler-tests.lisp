; Witnesses, teeth and the starvation counterexample for the contact scheduler.
;
; The counterexample is a trace, not a story: `*sched-starvation-trace*' is run
; under both policies below.  Under the stated unfair policy (deterministic
; priority with no aging, `fn-sched-unfair-step') the large article is never
; submitted; under the aging policy (`fn-sched-step') the same trace submits it
; on the third contact tick.  A simulation is not the liveness theorem --- the
; theorem is `fn-sched-aging-bound' in books/scheduler-invariants.lisp; this is
; the reachable witness that its hypotheses are satisfiable.

(in-package "ACL2")
(include-book "../../books/scheduler-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable sender: two durable works bound to two accepted articles.

(defconst *sched-groups* '("fn.letters"))
(defconst *sched-payload-small* '(72 105 13 10))
(defconst *sched-payload-big* '(76 111 110 103 13 10))
(defconst *sched-node-0* (fn-node-initial-state *sched-groups* 16))
(defconst *sched-node-1*
  (fn-node-complete
   (fn-node-prepare *sched-node-0* 9 "<small@fn.invalid>" *sched-payload-small*
                    *sched-groups* "archive-small" "subject-small"
                    "release-small" 4)
   0 9 :durable))
(defconst *sched-node-2*
  (fn-node-complete
   (fn-node-prepare *sched-node-1* 10 "<big@fn.invalid>" *sched-payload-big*
                    *sched-groups* "archive-big" "subject-big" "release-big" 4)
   1 10 :durable))

(defconst *sched-config*
  (fn-bp-make-config "dtn://home/fn" "dtn://peer/fn" "policy-1"
                     "receipt-authority" 1000 "home-incarnation-1"
                     "authorization-context-1"))

(defconst *sched-wf-0* (fn-bp-initial-state *sched-node-2* *sched-config*))
(defconst *sched-wf-1*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue *sched-wf-0* 10 0 "work-small" "<small@fn.invalid>"
                           "forward-small" "policy-1" "terms-1")
    10 0 :durable)))
(defconst *sched-wf*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue *sched-wf-1* 11 0 "work-big" "<big@fn.invalid>"
                           "forward-big" "policy-1" "terms-1")
    11 0 :durable)))

(assert-event (fn-bp-statep *sched-wf*))
(assert-event (fn-bp-work-retryablep
               (fn-bp-find-work "work-small" (fn-bp-state-works *sched-wf*))))
(assert-event (fn-bp-work-retryablep
               (fn-bp-find-work "work-big" (fn-bp-state-works *sched-wf*))))

; -----------------------------------------------------------------------------
; A reachable scheduler: queue bound 4, aging limit 2, retry bound 16.

(defconst *sched-conf* (fn-sched-config 4 2 16))
(assert-event (fn-sched-configp *sched-conf*))

(defconst *sched-ss-0* (fn-sched-initial-state *sched-conf* 1000))
(defconst *sched-ss-1*
  (fn-sched-admit (fn-sched-admit *sched-ss-0* "work-small" :article 10)
                  "work-big" :article 1000))
(defconst *sched-contact* (fn-sched-contact "dtn://peer/fn" 0 100000))
(defconst *sched-ss* (fn-sched-open *sched-ss-1* *sched-contact*))

(assert-event (fn-sched-statep *sched-ss*))
(assert-event (fn-sched-contactp *sched-contact*))
(assert-event (fn-sched-admissiblep *sched-ss*))
(assert-event (fn-sched-aged-fitsp *sched-ss*))
(assert-event (equal (len (fn-sched-queue *sched-ss*)) 2))

; The queue bound refuses the fifth admission rather than dropping work.
(defconst *sched-ss-full*
  (fn-sched-admit
   (fn-sched-admit (fn-sched-admit *sched-ss* "w3" :article 1) "w4" :article 1)
   "w5" :article 1))
(assert-event (equal (len (fn-sched-queue *sched-ss-full*)) 4))
(assert-event (not (fn-sched-queuedp "w5" (fn-sched-queue *sched-ss-full*))))
(assert-event (fn-sched-queuedp "work-big" (fn-sched-queue *sched-ss-full*)))

; -----------------------------------------------------------------------------
; Deterministic priority, separated on each of its three keys.

(defconst *sched-item-receipt* (fn-sched-item "r" :receipt 5000 9 0 nil nil))
(defconst *sched-item-small* (fn-sched-item "s" :article 10 3 0 nil nil))
(defconst *sched-item-big* (fn-sched-item "b" :article 1000 0 0 nil nil))
(defconst *sched-item-twin* (fn-sched-item "t" :article 10 7 0 nil nil))

; A receipt wins although it is the largest and the newest: class first.
(assert-event (fn-sched-betterp *sched-item-receipt* *sched-item-big*))
(assert-event (not (fn-sched-betterp *sched-item-big* *sched-item-receipt*)))
; Between two articles, size decides although the large one is older.
(assert-event (fn-sched-betterp *sched-item-small* *sched-item-big*))
; Between two articles of one size, admission order decides.
(assert-event (fn-sched-betterp *sched-item-small* *sched-item-twin*))
(assert-event (not (fn-sched-betterp *sched-item-twin* *sched-item-small*)))

; The order is a strict order on the witnesses: no item beats itself.
(assert-event (not (fn-sched-betterp *sched-item-small* *sched-item-small*)))

; Selection on the reachable state picks the small article, not the large one.
(assert-event (equal (fn-sched-item-work-id (fn-sched-selection *sched-ss* *sched-wf*))
                     "work-small"))
(assert-event (equal (fn-sched-selection-reason *sched-ss* *sched-wf*) :priority))

; -----------------------------------------------------------------------------
; The starvation trace
;
; Three contact ticks.  Between them the small article's attempt is observed
; `:no-contact', which is what a missed contact window actually reports, and
; which makes it retryable again.  Nothing in the trace is about the large
; article at all.

(defconst *sched-obs* (fn-clock-observation 1000 0 0 nil))
(assert-event (fn-clock-observationp *sched-obs*))
(assert-event (fn-sched-contact-holdsp *sched-contact* *sched-obs*))

(defconst *sched-starvation-trace*
  (list (fn-sched-tick-event "attempt:0" *sched-obs*)
        (fn-sched-transport-event "work-small" "attempt:0" 0 :no-contact)
        (fn-sched-tick-event "attempt:1" *sched-obs*)
        (fn-sched-transport-event "work-small" "attempt:1" 1 :no-contact)
        (fn-sched-tick-event "attempt:2" *sched-obs*)))

(assert-event (fn-sched-eventp-listp *sched-starvation-trace*))

; THE COUNTEREXAMPLE.  Under the stated unfair policy the large article is
; never submitted, while the small one is submitted at every tick.
(assert-event
 (not (fn-sched-unfair-submitted-in-trace *sched-ss* *sched-wf*
                                          *sched-starvation-trace* "work-big")))
(assert-event
 (fn-sched-unfair-submitted-in-trace *sched-ss* *sched-wf*
                                     *sched-starvation-trace* "work-small"))
(assert-event
 (null (fn-bp-work-attempt
        (fn-bp-find-work
         "work-big"
         (fn-bp-state-works
          (fn-sched-result-wf
           (fn-sched-unfair-trace *sched-ss* *sched-wf*
                                  *sched-starvation-trace*)))))))

; THE FIX.  The same trace under the aging policy submits the large article,
; on the tick after its pass count reaches the configured aging limit of two.
(assert-event
 (fn-sched-submitted-in-trace *sched-ss* *sched-wf* *sched-starvation-trace*
                              "work-big"))
(assert-event
 (consp (fn-bp-work-attempt
         (fn-bp-find-work
          "work-big"
          (fn-bp-state-works
           (fn-sched-result-wf
            (fn-sched-trace *sched-ss* *sched-wf* *sched-starvation-trace*)))))))

; And the promotion queue is what did it: after two passes the large article is
; in it, and the third tick's decision names `:aged', not `:priority'.
(defconst *sched-after-two*
  (fn-sched-trace *sched-ss* *sched-wf*
                  (list (fn-sched-tick-event "attempt:0" *sched-obs*)
                        (fn-sched-transport-event "work-small" "attempt:0" 0
                                                  :no-contact)
                        (fn-sched-tick-event "attempt:1" *sched-obs*))))
(assert-event
 (member-equal "work-big"
               (fn-sched-aged (fn-sched-result-ss *sched-after-two*))))
(assert-event
 (equal (fn-sched-selection-reason (fn-sched-result-ss *sched-after-two*)
                                   (fn-sched-result-wf *sched-after-two*))
        :aged))
(assert-event
 (fn-sched-aged-fitsp (fn-sched-result-ss *sched-after-two*)))

; The aging bound's hypotheses are satisfiable together, on that state.
(assert-event
 (fn-sched-contact-runp (fn-sched-result-ss *sched-after-two*)
                        (fn-sched-result-wf *sched-after-two*) 1 "attempt:2"))
(assert-event
 (fn-sched-eligible-runp (fn-sched-result-ss *sched-after-two*)
                         (fn-sched-result-wf *sched-after-two*) 1 "attempt:2"
                         "work-big"))
(assert-event
 (fn-sched-selected-withinp (fn-sched-result-ss *sched-after-two*)
                            (fn-sched-result-wf *sched-after-two*) 5
                            "attempt:2" "work-big"))

; -----------------------------------------------------------------------------
; The submit is the workflow's.  The effect emitted at the first tick is the
; one `fn-bp-complete' emitted for the durable attempt intent, octet for octet.

(defconst *sched-tick-1* (fn-sched-tick-step *sched-ss* *sched-wf* "attempt:0"))
(assert-event
 (equal (fn-sched-result-effects *sched-tick-1*)
        '((:submit "work-small" "attempt:0" 0 "dtn://home/fn" "dtn://peer/fn"
                   1000))))
(assert-event
 (equal (fn-sched-result-effects *sched-tick-1*)
        (fn-bp-result-effects
         (fn-sched-drive-attempt *sched-wf* 1000 "work-small" "attempt:0"))))
(assert-event (equal (fn-sched-retries (fn-sched-result-ss *sched-tick-1*)) 1))
(assert-event (equal (len (fn-sched-decisions
                           (fn-sched-result-ss *sched-tick-1*))) 1))

; A fenced workflow refuses, and a refusal charges no retry and records no
; decision.  This is the reachable falsifying case for `fn-sched-drive-okp'.
(defconst *sched-wf-fenced*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-attempt *sched-wf* 12 0 "work-small" "attempt:x")
    12 0 :indeterminate)))
(assert-event (fn-bp-state-fenced *sched-wf-fenced*))
(assert-event
 (not (fn-sched-drive-okp *sched-ss* *sched-wf-fenced* "attempt:0")))
(assert-event
 (equal (fn-sched-result-effects
         (fn-sched-tick-step *sched-ss* *sched-wf-fenced* "attempt:0"))
        nil))
(assert-event
 (equal (fn-sched-retries
         (fn-sched-result-ss
          (fn-sched-tick-step *sched-ss* *sched-wf-fenced* "attempt:0")))
        0))

; -----------------------------------------------------------------------------
; Expiry: three outcomes, and none of them releases anything.

(defconst *sched-obs-wall* (fn-clock-observation 1000 1600000000000 5000 t))
(defconst *sched-expired-event*
  (fn-sched-expiry-event "work-big" 1599999000000 100000 nil *sched-obs-wall*))
(defconst *sched-live-event*
  (fn-sched-expiry-event "work-big" 1600000000000 100000 nil *sched-obs-wall*))
(defconst *sched-uncertain-event*
  (fn-sched-expiry-event "work-big" 0 100000 nil *sched-obs-wall*))

(assert-event (equal (fn-clock-expiry-decision 1599999000000 100000 nil
                                               *sched-obs-wall*) :expired))
(assert-event (equal (fn-clock-expiry-decision 1600000000000 100000 nil
                                               *sched-obs-wall*) :live))
(assert-event (equal (fn-clock-expiry-decision 0 100000 nil *sched-obs-wall*)
                     :uncertain))

; `:expired' marks the item and nothing else.  The work, its retryability and
; the node the pins live in are identical objects afterwards.
(defconst *sched-expired*
  (fn-sched-step *sched-ss* *sched-wf* *sched-expired-event*))
(assert-event
 (fn-sched-item-expiredp
  (fn-sched-find "work-big"
                 (fn-sched-queue (fn-sched-result-ss *sched-expired*)))))
(assert-event (equal (fn-sched-result-wf *sched-expired*) *sched-wf*))
(assert-event (fn-bp-work-retryablep
               (fn-bp-find-work "work-big"
                                (fn-bp-state-works
                                 (fn-sched-result-wf *sched-expired*)))))
(assert-event (fn-sched-queuedp "work-big"
                                (fn-sched-queue
                                 (fn-sched-result-ss *sched-expired*))))
; An expired item is passed over by selection; the small one still runs.
(assert-event
 (equal (fn-sched-item-work-id
         (fn-sched-selection (fn-sched-result-ss *sched-expired*) *sched-wf*))
        "work-small"))

; `:uncertain' is not permission: the item stays schedulable.
(defconst *sched-uncertain*
  (fn-sched-step *sched-ss* *sched-wf* *sched-uncertain-event*))
(assert-event
 (not (fn-sched-item-expiredp
       (fn-sched-find "work-big"
                      (fn-sched-queue (fn-sched-result-ss *sched-uncertain*))))))
(defconst *sched-live*
  (fn-sched-step *sched-ss* *sched-wf* *sched-live-event*))
(assert-event
 (not (fn-sched-item-expiredp
       (fn-sched-find "work-big"
                      (fn-sched-queue (fn-sched-result-ss *sched-live*))))))

; Contact loss keeps the queue and the promotion queue and clears the budget.
(defconst *sched-closed* (fn-sched-step *sched-ss* *sched-wf*
                                        (fn-sched-close-event)))
(assert-event (equal (fn-sched-queue (fn-sched-result-ss *sched-closed*))
                     (fn-sched-queue *sched-ss*)))
(assert-event (not (fn-sched-admissiblep (fn-sched-result-ss *sched-closed*))))
(assert-event (equal (fn-sched-result-wf *sched-closed*) *sched-wf*))
(assert-event (null (fn-sched-selection (fn-sched-result-ss *sched-closed*)
                                        *sched-wf*)))

; A restart moves the generation and nothing else about the queue.
(defconst *sched-restarted*
  (fn-sched-step *sched-ss* *sched-wf* (fn-sched-restart-event)))
(assert-event (equal (fn-sched-generation
                      (fn-sched-result-ss *sched-restarted*)) 1))
(assert-event (equal (fn-sched-queue (fn-sched-result-ss *sched-restarted*))
                     (fn-sched-queue *sched-ss*)))
; Ordinary observations leave the generation alone: it is stable.
(assert-event (equal (fn-sched-generation (fn-sched-result-ss *sched-expired*))
                     0))
(assert-event (equal (fn-sched-generation (fn-sched-result-ss *sched-tick-1*))
                     0))

; -----------------------------------------------------------------------------
; The durable decision record

(defconst *sched-decision*
  (fn-sched-decision 0 0 "dtn://peer/fn" "work-small" "attempt:0" 0 :priority 0))
(assert-event (fn-sched-decision-recordp *sched-decision*))
(assert-event (fn-cbor-octet-listp (fn-sched-decision-protected *sched-decision*)))
; A reason the specification does not name is not a decision record.
(assert-event
 (not (fn-sched-decision-recordp
       (fn-sched-decision 0 0 "dtn://peer/fn" "work-small" "attempt:0" 0
                          :because-i-said-so 0))))
; Neither is one with a text field where a natural belongs.
(assert-event
 (not (fn-sched-decision-recordp
       (fn-sched-decision "zero" 0 "dtn://peer/fn" "work-small" "attempt:0" 0
                          :priority 0))))

; -----------------------------------------------------------------------------
; Teeth.  One `must-fail' per hypothesis of each keystone.

; fn-sched-step-preserves-state
(must-fail
 (defthm sched-teeth-step-needs-statep
   (fn-sched-statep (fn-sched-result-ss (fn-sched-step ss wf event)))))

; fn-sched-trace-preserves-state
(must-fail
 (defthm sched-teeth-trace-needs-statep
   (fn-sched-statep (fn-sched-result-ss (fn-sched-trace ss wf events)))))

; fn-sched-step-preserves-queued
(must-fail
 (defthm sched-teeth-queued-needs-queued
   (fn-sched-queuedp
    id (fn-sched-queue (fn-sched-result-ss (fn-sched-step ss wf event))))))

; fn-sched-only-a-tick-or-a-relay-touches-the-workflow, hypothesis one
(must-fail
 (defthm sched-teeth-workflow-needs-not-tick
   (implies (not (equal (fn-bp-nth 0 event) :transport))
            (equal (fn-sched-result-wf (fn-sched-step ss wf event)) wf))))

; the same theorem, hypothesis two
(must-fail
 (defthm sched-teeth-workflow-needs-not-transport
   (implies (not (equal (fn-bp-nth 0 event) :tick))
            (equal (fn-sched-result-wf (fn-sched-step ss wf event)) wf))))

; fn-sched-promotion-position-decreases, hypothesis by hypothesis
(must-fail
 (defthm sched-teeth-position-needs-admissible
   (implies (and (fn-sched-drive-okp ss wf attempt-id)
                 (member-equal w (fn-sched-aged ss))
                 (fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)
                 (not (fn-sched-submit-for-idp
                       w (fn-sched-result-effects
                          (fn-sched-tick-step ss wf attempt-id)))))
            (< (fn-sched-pos
                w (fn-sched-aged
                   (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))))
               (fn-sched-pos w (fn-sched-aged ss))))))

(must-fail
 (defthm sched-teeth-position-needs-drive-ok
   (implies (and (fn-sched-admissiblep ss)
                 (member-equal w (fn-sched-aged ss))
                 (fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)
                 (not (fn-sched-submit-for-idp
                       w (fn-sched-result-effects
                          (fn-sched-tick-step ss wf attempt-id)))))
            (< (fn-sched-pos
                w (fn-sched-aged
                   (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))))
               (fn-sched-pos w (fn-sched-aged ss))))))

(must-fail
 (defthm sched-teeth-position-needs-membership
   (implies (and (fn-sched-admissiblep ss)
                 (fn-sched-drive-okp ss wf attempt-id)
                 (fn-sched-eligiblep (fn-sched-find w (fn-sched-queue ss)) wf)
                 (not (fn-sched-submit-for-idp
                       w (fn-sched-result-effects
                          (fn-sched-tick-step ss wf attempt-id)))))
            (< (fn-sched-pos
                w (fn-sched-aged
                   (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))))
               (fn-sched-pos w (fn-sched-aged ss))))))

(must-fail
 (defthm sched-teeth-position-needs-eligibility
   (implies (and (fn-sched-admissiblep ss)
                 (fn-sched-drive-okp ss wf attempt-id)
                 (member-equal w (fn-sched-aged ss))
                 (not (fn-sched-submit-for-idp
                       w (fn-sched-result-effects
                          (fn-sched-tick-step ss wf attempt-id)))))
            (< (fn-sched-pos
                w (fn-sched-aged
                   (fn-sched-result-ss (fn-sched-tick-step ss wf attempt-id))))
               (fn-sched-pos w (fn-sched-aged ss))))))

; fn-sched-aging-bound: the promotion queue must fit the configured bound
(must-fail
 (defthm sched-teeth-aging-needs-fitsp
   (implies (and (member-equal w (fn-sched-aged ss))
                 (fn-sched-contact-runp ss wf n attempt-id)
                 (fn-sched-eligible-runp ss wf n attempt-id w)
                 (< (nfix (fn-sched-queue-bound (fn-sched-conf ss))) n))
            (fn-sched-selected-withinp ss wf n attempt-id w))))

; the work must have reached the promotion queue
(must-fail
 (defthm sched-teeth-aging-needs-promotion
   (implies (and (fn-sched-aged-fitsp ss)
                 (fn-sched-contact-runp ss wf n attempt-id)
                 (fn-sched-eligible-runp ss wf n attempt-id w)
                 (< (nfix (fn-sched-queue-bound (fn-sched-conf ss))) n))
            (fn-sched-selected-withinp ss wf n attempt-id w))))

; the contacts must recur for long enough
(must-fail
 (defthm sched-teeth-aging-needs-horizon
   (implies (and (fn-sched-aged-fitsp ss)
                 (member-equal w (fn-sched-aged ss))
                 (fn-sched-contact-runp ss wf n attempt-id)
                 (fn-sched-eligible-runp ss wf n attempt-id w))
            (fn-sched-selected-withinp ss wf n attempt-id w))))

; the work must stay eligible
(must-fail
 (defthm sched-teeth-aging-needs-eligibility
   (implies (and (fn-sched-aged-fitsp ss)
                 (member-equal w (fn-sched-aged ss))
                 (fn-sched-contact-runp ss wf n attempt-id)
                 (< (nfix (fn-sched-queue-bound (fn-sched-conf ss))) n))
            (fn-sched-selected-withinp ss wf n attempt-id w))))

; capacity must suffice at every tick of the run
(must-fail
 (defthm sched-teeth-aging-needs-capacity
   (implies (and (fn-sched-aged-fitsp ss)
                 (member-equal w (fn-sched-aged ss))
                 (fn-sched-eligible-runp ss wf n attempt-id w)
                 (< (nfix (fn-sched-queue-bound (fn-sched-conf ss))) n))
            (fn-sched-selected-withinp ss wf n attempt-id w))))

; conditional progress: without A-FAIRNESS's finite contact index the horizon
; is not a number and the conclusion does not follow.
(must-fail
 (defthm sched-teeth-progress-needs-a-fairness
   (implies (and (fn-sched-aged-fitsp ss)
                 (member-equal w (fn-sched-aged ss))
                 (fn-sched-contact-runp ss wf n attempt-id)
                 (fn-sched-eligible-runp ss wf n attempt-id w)
                 (equal n (fn-assume-fairness-contact-index route schedule)))
            (fn-sched-selected-withinp ss wf n attempt-id w))))
