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
; Teeth.  One CONCRETE violating value per hypothesis of each keystone
; (docs/proof-style.md §5).  A general negated `must-fail' says only that the
; prover found no proof; each assertion below is a counterexample, evaluated.

; A forged state: right tag, right length, promotion queue not a list of
; strings.  Reachable by no transition, which is the point.
(defconst *sched-teeth-forged*
  (fn-sched-state 0 *sched-conf* nil '(7) nil 0 0 1000 nil))
(assert-event (not (fn-sched-statep *sched-teeth-forged*)))

; fn-sched-step-preserves-state / fn-sched-trace-preserves-state, hypothesis
; (fn-sched-statep ss).
(assert-event
 (not (fn-sched-statep
       (fn-sched-result-ss
        (fn-sched-step *sched-teeth-forged* *sched-wf*
                       (fn-sched-admit-event "work-new" :article 8))))))
(assert-event
 (not (fn-sched-statep
       (fn-sched-result-ss
        (fn-sched-trace *sched-teeth-forged* *sched-wf*
                        (list (fn-sched-admit-event "work-new" :article 8)))))))

; fn-sched-step-preserves-queued, hypothesis (fn-sched-queuedp id ...): a
; work-id that was never admitted is not queued after the step either.
(assert-event (not (fn-sched-queuedp "work-absent" (fn-sched-queue *sched-ss*))))
(assert-event
 (not (fn-sched-queuedp
       "work-absent"
       (fn-sched-queue (fn-sched-result-ss
                        (fn-sched-step *sched-ss* *sched-wf*
                                       (fn-sched-close-event)))))))

; fn-sched-only-a-tick-or-a-relay-touches-the-workflow, hypothesis one: the
; tick it excludes does move the workflow.
(assert-event
 (not (equal (fn-sched-result-wf
              (fn-sched-step *sched-ss* *sched-wf*
                             (fn-sched-tick-event "attempt:0" *sched-obs*)))
             *sched-wf*)))

; the same theorem, hypothesis two: the relayed transport observation it
; excludes does move the workflow.
(defconst *sched-wf-after-tick-1* (fn-sched-result-wf *sched-tick-1*))
(assert-event
 (not (equal (fn-sched-result-wf
              (fn-sched-step *sched-ss* *sched-wf-after-tick-1*
                             (fn-sched-transport-event "work-small" "attempt:0"
                                                       0 :no-contact)))
             *sched-wf-after-tick-1*)))

; -----------------------------------------------------------------------------
; The promoted state: "work-big" sits at the head of the promotion queue.

(defconst *sched-promoted* (fn-sched-result-ss *sched-after-two*))
(defconst *sched-promoted-wf* (fn-sched-result-wf *sched-after-two*))
(assert-event (member-equal "work-big" (fn-sched-aged *sched-promoted*)))
(assert-event (fn-sched-admissiblep *sched-promoted*))

; fn-sched-promotion-position-decreases, hypothesis (fn-sched-admissiblep ss):
; with the contact closed the tick moves nothing, so the position does not fall.
(defconst *sched-promoted-closed* (fn-sched-close *sched-promoted*))
(assert-event (not (fn-sched-admissiblep *sched-promoted-closed*)))
(assert-event (member-equal "work-big" (fn-sched-aged *sched-promoted-closed*)))
(assert-event
 (fn-sched-eligiblep (fn-sched-find "work-big"
                                    (fn-sched-queue *sched-promoted-closed*))
                     *sched-promoted-wf*))
(assert-event
 (not (fn-sched-submit-for-idp
       "work-big"
       (fn-sched-result-effects
        (fn-sched-tick-step *sched-promoted-closed* *sched-promoted-wf*
                            "attempt:9")))))
(assert-event
 (not (< (fn-sched-pos
          "work-big"
          (fn-sched-aged
           (fn-sched-result-ss
            (fn-sched-tick-step *sched-promoted-closed* *sched-promoted-wf*
                                "attempt:9"))))
         (fn-sched-pos "work-big" (fn-sched-aged *sched-promoted-closed*)))))

; the same theorem, hypothesis (fn-sched-drive-okp ...): a fenced workflow
; refuses, the tick is a no-op, and the position does not fall.
(defconst *sched-promoted-wf-fenced*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-attempt *sched-promoted-wf* 12 0 "work-small" "attempt:x")
    12 0 :indeterminate)))
(assert-event (fn-bp-state-fenced *sched-promoted-wf-fenced*))
(assert-event
 (not (fn-sched-drive-okp *sched-promoted* *sched-promoted-wf-fenced*
                          "attempt:9")))
(assert-event
 (not (< (fn-sched-pos
          "work-big"
          (fn-sched-aged
           (fn-sched-result-ss
            (fn-sched-tick-step *sched-promoted* *sched-promoted-wf-fenced*
                                "attempt:9"))))
         (fn-sched-pos "work-big" (fn-sched-aged *sched-promoted*)))))

; the same theorem, hypothesis (member-equal w (fn-sched-aged ss)): on the
; initial open state the promotion queue is empty, "work-big" is eligible and
; is not selected, and its position (zero in an empty queue) does not fall.
(assert-event (not (member-equal "work-big" (fn-sched-aged *sched-ss*))))
(assert-event
 (not (fn-sched-submit-for-idp
       "work-big"
       (fn-sched-result-effects
        (fn-sched-tick-step *sched-ss* *sched-wf* "attempt:0")))))
(assert-event
 (not (< (fn-sched-pos
          "work-big"
          (fn-sched-aged
           (fn-sched-result-ss
            (fn-sched-tick-step *sched-ss* *sched-wf* "attempt:0"))))
         (fn-sched-pos "work-big" (fn-sched-aged *sched-ss*)))))

; the same theorem, hypothesis (fn-sched-eligiblep (fn-sched-find w ...) wf):
; an expired item is dropped from the promotion queue rather than advanced.
(defconst *sched-promoted-expired*
  (fn-sched-result-ss
   (fn-sched-step *sched-promoted* *sched-promoted-wf* *sched-expired-event*)))
(assert-event (member-equal "work-big" (fn-sched-aged *sched-promoted-expired*)))
(assert-event
 (not (fn-sched-eligiblep
       (fn-sched-find "work-big" (fn-sched-queue *sched-promoted-expired*))
       *sched-promoted-wf*)))
(assert-event
 (not (< (fn-sched-pos
          "work-big"
          (fn-sched-aged
           (fn-sched-result-ss
            (fn-sched-tick-step *sched-promoted-expired* *sched-promoted-wf*
                                "attempt:9"))))
         (fn-sched-pos "work-big" (fn-sched-aged *sched-promoted-expired*)))))

; -----------------------------------------------------------------------------
; fn-sched-aging-bound, hypothesis by hypothesis.

; the horizon must exceed the configured queue bound: at n = 0 nothing is
; selected, and every other hypothesis holds.
(assert-event (fn-sched-aged-fitsp *sched-promoted*))
(assert-event (fn-sched-contact-runp *sched-promoted* *sched-promoted-wf* 0
                                     "attempt:2"))
(assert-event (fn-sched-eligible-runp *sched-promoted* *sched-promoted-wf* 0
                                      "attempt:2" "work-big"))
(assert-event (not (fn-sched-selected-withinp *sched-promoted*
                                              *sched-promoted-wf* 0
                                              "attempt:2" "work-big")))

; capacity must suffice: with the contact closed no tick of the run is
; admissible and the work is never selected, over a horizon past the bound.
(assert-event
 (not (fn-sched-contact-runp *sched-promoted-closed* *sched-promoted-wf* 5
                             "attempt:9")))
(assert-event
 (not (fn-sched-selected-withinp *sched-promoted-closed* *sched-promoted-wf* 5
                                 "attempt:9" "work-big")))

; the work must stay eligible: the expired item is never selected, over the
; same horizon.
(assert-event
 (not (fn-sched-eligible-runp *sched-promoted-expired* *sched-promoted-wf* 5
                              "attempt:9" "work-big")))
(assert-event
 (not (fn-sched-selected-withinp *sched-promoted-expired* *sched-promoted-wf* 5
                                 "attempt:9" "work-big")))

; OPEN TEETH, recorded rather than faked (AGENTS.md: a claim earns its name).
;
;  * `(member-equal w (fn-sched-aged ss))' of `fn-sched-aging-bound'.  A
;    violating value needs a work that is eligible at every tick of a run past
;    the queue bound and still not selected, which under the aging policy
;    requires a promotion queue this lane cannot reach in ground evaluation.
;  * `(fn-sched-aged-fitsp ss)' of the same theorem.  A violating value needs a
;    promotion queue longer than the configured queue bound; no transition
;    builds one, which is exactly the invariant specs/scheduler.md leaves to
;    C3-03.  Until that invariant is a theorem the hypothesis has no reachable
;    counterexample and is not claimed to have one.

; -----------------------------------------------------------------------------
; fn-sched-conditional-progress-under-a-fairness: without A-FAIRNESS the
; horizon is not a natural number, and a non-numeric horizon selects nothing.
(assert-event (fn-sched-contact-runp *sched-promoted* *sched-promoted-wf*
                                     :no-finite-horizon "attempt:2"))
(assert-event (fn-sched-eligible-runp *sched-promoted* *sched-promoted-wf*
                                      :no-finite-horizon "attempt:2"
                                      "work-big"))
(assert-event (not (fn-sched-selected-withinp *sched-promoted*
                                              *sched-promoted-wf*
                                              :no-finite-horizon "attempt:2"
                                              "work-big")))
