; Executable witnesses for the joint workflow/node binding invariant.
(in-package "ACL2")
(include-book "../../books/bp-workflow-binding-invariants")

(defconst *bpb-groups* '("fn.letters"))
(defconst *bpb-node-empty* (fn-node-initial-state *bpb-groups* 16))
(defconst *bpb-node-prepared*
  (fn-node-prepare *bpb-node-empty* 17 "<bound@example.invalid>"
                   '(98 111 117 110 100 13 10) *bpb-groups*
                   "archive-bound" "subject-bound" "release-bound" 8))
(defconst *bpb-node*
  (fn-node-complete *bpb-node-prepared* 0 17 :durable))
(defconst *bpb-config*
  (fn-bp-make-config "dtn://home/fn" "dtn://peer/fn" "policy-bound"
                     "receipt-authority" 900 "incarnation-bound"
                     "auth-bound"))
(defconst *bpb-initial* (fn-bp-initial-state *bpb-node* *bpb-config*))

(assert-event (fn-bp-binding-statep *bpb-initial*))

; A successful enqueue preparation derives all binding fields from the actual
; accepted node record.  The stronger invariant covers the pending work before
; it enters the durable work list.
(defconst *bpb-enqueue-pending*
  (fn-bp-prepare-enqueue *bpb-initial* 30 1 "work-bound"
                         "<bound@example.invalid>" "forward-bound"
                         "policy-bound" "terms-bound"))
(assert-event (fn-bp-binding-statep *bpb-enqueue-pending*))
(assert-event
 (fn-bp-work-boundp
  (fn-bp-state-node *bpb-enqueue-pending*)
  (fn-bp-pending-work (fn-bp-state-pending *bpb-enqueue-pending*))))

(defconst *bpb-enqueued*
  (fn-bp-result-state
   (fn-bp-complete *bpb-enqueue-pending* 30 1 :durable)))
(defconst *bpb-attempt-pending*
  (fn-bp-prepare-attempt *bpb-enqueued* 31 1 "work-bound" "attempt-bound"))
(assert-event (fn-bp-binding-statep *bpb-attempt-pending*))

(defconst *bpb-attempted*
  (fn-bp-result-state
   (fn-bp-complete *bpb-attempt-pending* 31 1 :durable)))
(defconst *bpb-receipt*
  (fn-bp-make-receipt "receipt-bound" "work-bound" "subject-bound"
                      "receipt-authority" "dtn://peer/fn" "policy-bound"
                      "incarnation-bound" "auth-bound" "terms-bound"))
(defconst *bpb-receipt-pending*
  (fn-bp-prepare-receipt *bpb-attempted* 32 1 *bpb-receipt* t))
(assert-event (fn-bp-binding-statep *bpb-receipt-pending*))

; The dispatcher uses the production transitions.  This trace mixes restart,
; stale completion, malformed input, transport observation, policy retry, and
; an uncertain receipt decision recovered as committed.
(defconst *bpb-events*
  (list (fn-bp-storage-complete-event 32 1 :indeterminate)
        (fn-bp-restart-event)
        (fn-bp-storage-complete-event 32 1 :durable)
        '(:malformed-event)
        (fn-bp-storage-recover-event 32 1 :committed)
        (fn-bp-transport-event "work-bound" "attempt-bound" 0 :delivered)
        (fn-bp-retry-request-event "work-bound" "attempt-bound" 0
                                   "policy-bound")
        (fn-bp-no-contact-event "work-bound" "attempt-bound" 99)))
(defconst *bpb-final* (fn-bp-trace *bpb-receipt-pending* *bpb-events*))
(assert-event (fn-bp-binding-statep *bpb-final*))
(assert-event
 (fn-bp-works-boundp (fn-bp-state-node *bpb-final*)
                     (fn-bp-state-works *bpb-final*)))
(assert-event (equal (fn-bp-state-node *bpb-final*) *bpb-node*))
(assert-event
 (equal (fn-bp-work-archive-id
         (fn-bp-find-work "work-bound" (fn-bp-state-works *bpb-final*)))
        "archive-bound"))

; Nonvacuity/counterexample: the public structural state recognizer alone can
; contain a well-typed fabricated work.  It is rejected by the joint invariant.
(defconst *bpb-unbound-work*
  (fn-bp-make-work "fabricated-work" "<missing@example.invalid>"
                   "fabricated-subject" "fabricated-archive" "forward-bound"
                   "dtn://peer/fn" "policy-bound" "incarnation-bound"
                   "auth-bound" "terms-bound" 0 nil nil))
(defconst *bpb-structural-only*
  (fn-bp-make-state *bpb-node* *bpb-config*
                    (list *bpb-unbound-work*) nil nil nil nil))
(assert-event (fn-bp-statep *bpb-structural-only*))
(assert-event (not (fn-bp-binding-statep *bpb-structural-only*)))
(assert-event
 (not (fn-bp-works-boundp (fn-bp-state-node *bpb-structural-only*)
                          (fn-bp-state-works *bpb-structural-only*))))
