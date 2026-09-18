(in-package "ACL2")
(include-book "../../books/bp-workflow-records")
(defconst *bpr-groups* '("fn.test"))
(defconst *bpr-prepared* (fn-node-prepare (fn-node-initial-state *bpr-groups* 8)
  9 "<a@example.invalid>" '(65 13 10) *bpr-groups*
  "archive:a" "subject:a" "release:a" 1))
(defconst *bpr-node* (fn-node-complete *bpr-prepared* 0 9 :durable))
(defconst *bpr-config* '(:config "dtn://local/" "dtn://peer/" "policy:1"
  "dtn://issuer/" 3600 "inc:1" "auth:1"))
(defconst *bpr-enqueue* '(:enqueue 10 0 "work:a" "<a@example.invalid>"
  "subject:a" "archive:a" "forward:a" "dtn://peer/" "policy:1" "terms:1"))
(defconst *bpr-attempt* '(:attempt 11 0 "work:a" "attempt:1" 0
  "dtn://local/" "dtn://peer/" "policy:1" 3600))
(defconst *bpr-transport* '(:transport "work:a" "attempt:1" 0 :expired))
(defconst *bpr-image* (fn-bp-replay-journal *bpr-node*
  (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable)
        *bpr-attempt* '(:outcome 11 0 :ordinary :durable) *bpr-transport*)))
(assert-event (car *bpr-image*))
(assert-event (fn-bp-statep (fn-bp-journal-nth 1 *bpr-image*)))
(assert-event (equal (fn-bp-attempt-status
 (fn-bp-work-attempt (car (fn-bp-state-works (fn-bp-journal-nth 1 *bpr-image*)))))
 :expired))
; A conflicting immutable subject rejects the whole recovered image.
(assert-event (not (car (fn-bp-replay-journal *bpr-node*
 (list *bpr-config* (update-nth 5 "other" *bpr-enqueue*))))))
; Replaying the same enqueue twice is rejected rather than inventing a second ack.
(assert-event (not (car (fn-bp-replay-journal *bpr-node*
 (list *bpr-config* *bpr-enqueue* *bpr-enqueue*)))))
; A completion pair reserved by an earlier kind cannot complete a later intent.
(defconst *bpr-reused* (fn-bp-replay-journal *bpr-node*
 (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable)
       '(:attempt 10 0 "work:a" "attempt:old" 0
         "dtn://local/" "dtn://peer/" "policy:1" 3600)
       '(:outcome 10 0 :ordinary :durable))))
(assert-event (not (car *bpr-reused*)))
; Committed recovery of an attempt reconstructs uncertainty and emits no submit.
(defconst *bpr-recovered* (fn-bp-replay-journal *bpr-node*
 (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable)
       *bpr-attempt* '(:outcome 11 0 :recovery :committed))))
(assert-event (car *bpr-recovered*))
(assert-event (equal (fn-bp-journal-nth 2 *bpr-recovered*)
                     '((:enqueue-ack "work:a"))))
; A durable intent with no outcome is never treated as success after restart.
(defconst *bpr-lost-outcome* (fn-bp-replay-journal *bpr-node*
 (list *bpr-config* *bpr-enqueue*)))
(assert-event (car *bpr-lost-outcome*))
(assert-event (fn-bp-state-fenced (fn-bp-journal-nth 1 *bpr-lost-outcome*)))
(assert-event (equal (fn-bp-journal-nth 2 *bpr-lost-outcome*) nil))
; Abort consumes the pair, so a later attempt cannot reuse it.
(assert-event (not (car (fn-bp-replay-journal *bpr-node*
 (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :aborted)
       *bpr-enqueue* '(:outcome 10 0 :ordinary :durable))))))
; Expiry changes only retry state; the durable node/archive image is unchanged.
(assert-event (equal (fn-bp-state-node (fn-bp-journal-nth 1 *bpr-image*))
                     *bpr-node*))
(assert-event (fn-bp-work-retryablep
 (car (fn-bp-state-works (fn-bp-journal-nth 1 *bpr-image*)))))
; Delivery with a lost application receipt needs explicit policy retry.
(defconst *bpr-delivery-retry* (fn-bp-replay-journal *bpr-node*
 (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable)
       *bpr-attempt* '(:outcome 11 0 :ordinary :durable)
       '(:transport "work:a" "attempt:1" 0 :delivered)
       '(:retry-request "work:a" "attempt:1" 0 "policy:1"))))
(assert-event (car *bpr-delivery-retry*))
(assert-event (equal (fn-bp-attempt-status (fn-bp-work-attempt
 (car (fn-bp-state-works (fn-bp-journal-nth 1 *bpr-delivery-retry*))))) :unknown))
(assert-event (equal (fn-bp-state-node (fn-bp-journal-nth 1 *bpr-delivery-retry*))
                     *bpr-node*))
