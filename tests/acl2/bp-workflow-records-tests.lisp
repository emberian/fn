(in-package "ACL2")
(include-book "../../books/bp-workflow-records-invariants")
(include-book "std/testing/must-fail" :dir :system)
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


; ---------------------------------------------------------------------------
; D7 witness: one journal exercising every record kind and every outcome
; kind.  Replay succeeds; the recovered image is the trace of the initial
; state over the journal's denotation (fn-bp-replay-journal-is-trace-when-ok);
; the node is untouched; the replayed effects are the actionable trace effects.
(defconst *bpr-s0*
  (fn-bp-initial-state *bpr-node* (fn-bp-config-from-record *bpr-config*)))
(defconst *bpr-receipt*
  (fn-bp-make-receipt "receipt:1" "work:a" "subject:a" "dtn://issuer/"
                      "dtn://peer/" "policy:1" "inc:1" "auth:1" "terms:1"))
(defconst *bpr-receipt-intent-14*
  '(:receipt-intent 14 0 "receipt:1" "work:a" "subject:a" "dtn://issuer/"
    "dtn://peer/" "policy:1" "inc:1" "auth:1" "terms:1"))
(defconst *bpr-receipt-intent-15*
  '(:receipt-intent 15 0 "receipt:1" "work:a" "subject:a" "dtn://issuer/"
    "dtn://peer/" "policy:1" "inc:1" "auth:1" "terms:1"))
(defconst *bpr-all-kinds*
  (list *bpr-config*
        *bpr-enqueue*
        '(:outcome 10 0 :ordinary :durable)
        *bpr-attempt*
        '(:outcome 11 0 :ordinary :durable)
        '(:transport "work:a" "attempt:1" 0 :bpa-submit-replied)
        '(:transport "work:a" "attempt:1" 0 :forwarded)
        '(:transport "work:a" "attempt:1" 0 :delivered)
        '(:retry-request "work:a" "attempt:1" 0 "policy:1")
        '(:attempt 12 0 "work:a" "attempt:2" 1
          "dtn://local/" "dtn://peer/" "policy:1" 3600)
        '(:outcome 12 0 :ordinary :aborted)
        '(:attempt 13 0 "work:a" "attempt:3" 1
          "dtn://local/" "dtn://peer/" "policy:1" 3600)
        '(:outcome 13 0 :recovery :committed)
        *bpr-receipt-intent-14*
        '(:outcome 14 0 :recovery :absent)
        *bpr-receipt-intent-15*
        '(:outcome 15 0 :recovery :committed)))
(defun fn-bprt-kinds (records)
  (if (consp records) (cons (car (car records)) (fn-bprt-kinds (cdr records))) nil))
(defun fn-bprt-outcomes (records)
  (if (consp records)
      (if (equal (car (car records)) :outcome)
          (cons (list (fn-bp-journal-nth 3 (car records))
                      (fn-bp-journal-nth 4 (car records)))
                (fn-bprt-outcomes (cdr records)))
        (fn-bprt-outcomes (cdr records)))
    nil))
(assert-event
 (subsetp-equal '(:config :enqueue :outcome :attempt :transport
                  :retry-request :receipt-intent)
                (fn-bprt-kinds *bpr-all-kinds*)))
(assert-event
 (subsetp-equal '((:ordinary :durable) (:ordinary :aborted)
                  (:recovery :committed) (:recovery :absent))
                (fn-bprt-outcomes *bpr-all-kinds*)))
(defconst *bpr-all-image* (fn-bp-replay-journal *bpr-node* *bpr-all-kinds*))
(assert-event (car *bpr-all-image*))
(defconst *bpr-all-state* (fn-bp-journal-nth 1 *bpr-all-image*))
(assert-event (fn-bp-binding-statep *bpr-all-state*))
(assert-event (equal (fn-bp-state-node *bpr-all-state*) *bpr-node*))
(assert-event (not (fn-bp-state-fenced *bpr-all-state*)))
(assert-event
 (equal (fn-bp-work-receipt (car (fn-bp-state-works *bpr-all-state*)))
        *bpr-receipt*))
(assert-event
 (equal (fn-bp-attempt-id
         (fn-bp-work-attempt (car (fn-bp-state-works *bpr-all-state*))))
        "attempt:3"))
(assert-event
 (equal (fn-bp-journal-nth 2 *bpr-all-image*)
        '((:enqueue-ack "work:a")
          (:submit "work:a" "attempt:1" 0 "dtn://local/" "dtn://peer/" 3600)
          (:receipt-ack "receipt:1"))))
; The keystone, executed on the witness.
(defconst *bpr-all-denotation* (fn-bp-journal-denotation *bpr-all-kinds*))
(assert-event
 (equal *bpr-all-state* (fn-bp-trace *bpr-s0* *bpr-all-denotation*)))
(assert-event
 (equal (fn-bp-journal-nth 2 *bpr-all-image*)
        (fn-bp-actionable-effects
         (fn-bp-trace-effects *bpr-s0* *bpr-all-denotation*))))
; The denotation carries the crash-implied fences and the trailing restart;
; the unfiltered trace demands recovery at each fence and replay does not
; carry those demands because the next event resolves them.
(assert-event
 (member-equal (fn-bp-storage-complete-event 13 0 :indeterminate)
               *bpr-all-denotation*))
(assert-event
 (member-equal (fn-bp-storage-complete-event 14 0 :indeterminate)
               *bpr-all-denotation*))
(assert-event
 (equal (car (last *bpr-all-denotation*)) (fn-bp-restart-event)))
(assert-event
 (member-equal '(:recover-required 13 0)
               (fn-bp-trace-effects *bpr-s0* *bpr-all-denotation*)))
(assert-event
 (not (member-equal '(:recover-required 13 0)
                    (fn-bp-journal-nth 2 *bpr-all-image*))))

; Teeth (fn-bp-replay-journal-is-trace-when-ok, hypothesis okp): a journal
; whose replay fails is not its trace.  Replay stops at the duplicate enqueue
; with the first still pending and no restart applied; the trace ignores the
; duplicate and fences the pending intent at restart.
(defconst *bpr-dup* (list *bpr-config* *bpr-enqueue* *bpr-enqueue*))
(assert-event (not (car (fn-bp-replay-journal *bpr-node* *bpr-dup*))))
(must-fail
 (assert-event
  (equal (fn-bp-journal-nth 1 (fn-bp-replay-journal *bpr-node* *bpr-dup*))
         (fn-bp-trace *bpr-s0* (fn-bp-journal-denotation *bpr-dup*)))))
; Teeth (fn-bp-replay-journal-success-is-binding-state, hypothesis okp): a
; refused image is not a state at all.
(must-fail
 (assert-event
  (fn-bp-binding-statep
   (fn-bp-journal-nth 1 (fn-bp-replay-journal *bpr-node* '((:config "x")))))))

; Malformed or out-of-place records are refused wherever they occur
; (fn-bp-replay-journal-rejects-any-malformed-record), not skipped.
(assert-event
 (not (car (fn-bp-replay-journal *bpr-node*
                                 (append *bpr-all-kinds* '((:bogus)))))))
(assert-event
 (not (car (fn-bp-replay-journal *bpr-node*
                                 (append *bpr-all-kinds* (list *bpr-config*))))))
(assert-event
 (not (car (fn-bp-replay-journal
            *bpr-node*
            (list *bpr-config*
                  '(:transport "work:a" "attempt:1" 0 :not-a-status)
                  *bpr-enqueue*)))))
(assert-event
 (equal (fn-bp-apply-journal-record *bpr-all-state* '(:bogus))
        (list nil *bpr-all-state* nil)))
(assert-event
 (equal (fn-bp-apply-journal-record *bpr-all-state* *bpr-config*)
        (list nil *bpr-all-state* nil)))
; Teeth (hypothesis: the record is malformed): the same journal without it succeeds.
(must-fail (assert-event (not (car (fn-bp-replay-journal *bpr-node* *bpr-all-kinds*)))))

; ---------------------------------------------------------------------------
; The live entry point is one fn-bp-step (fn-bp-apply-journal-record-is-step-when-ok).
(defconst *bpr-live-enqueue* (fn-bp-apply-journal-record *bpr-s0* *bpr-enqueue*))
(assert-event (car *bpr-live-enqueue*))
(assert-event
 (equal (fn-bp-journal-nth 1 *bpr-live-enqueue*)
        (fn-bp-result-state
         (fn-bp-step *bpr-s0* (fn-bp-record-live-event *bpr-enqueue*)))))
(defconst *bpr-enq-state* (fn-bp-journal-nth 1 *bpr-live-enqueue*))
(defconst *bpr-enq-durable*
  (fn-bp-apply-journal-record *bpr-enq-state* '(:outcome 10 0 :ordinary :durable)))
(assert-event
 (equal (fn-bp-journal-nth 2 *bpr-enq-durable*)
        (fn-bp-result-effects
         (fn-bp-step *bpr-enq-state*
                     (fn-bp-record-live-event
                      '(:outcome 10 0 :ordinary :durable))))))
(defconst *bpr-att-prepared*
  (fn-bp-apply-journal-record (fn-bp-journal-nth 1 *bpr-enq-durable*) *bpr-attempt*))
(assert-event (car *bpr-att-prepared*))
; A pending attempt intent, prepared and (in host terms) persisted but with no
; outcome yet.
(defconst *bpr-att-state* (fn-bp-journal-nth 1 *bpr-att-prepared*))
(assert-event
 (equal (fn-bp-pending-kind (fn-bp-state-pending *bpr-att-state*)) :attempt))

; ---------------------------------------------------------------------------
; D8 over the live entry point
; (fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome).
(defun fn-bprt-submitp (effects)
  (and (consp effects) (equal (fn-bp-nth 0 (car effects)) :submit)))
(defconst *bpr-att-durable*
  (fn-bp-apply-journal-record *bpr-att-state* '(:outcome 11 0 :ordinary :durable)))
(assert-event (car *bpr-att-durable*))
(assert-event (fn-bprt-submitp (fn-bp-journal-nth 2 *bpr-att-durable*)))
(assert-event (equal (len (fn-bp-journal-nth 2 *bpr-att-durable*)) 1))
; The pending, not yet durable, intent yields no :submit from anything else.
(assert-event
 (not (fn-bprt-submitp
       (fn-bp-journal-nth 2 (fn-bp-apply-journal-record
                             *bpr-att-state* '(:outcome 11 0 :ordinary :aborted))))))
(assert-event
 (not (fn-bprt-submitp
       (fn-bp-journal-nth 2 (fn-bp-apply-journal-record
                             *bpr-att-state* '(:outcome 99 0 :ordinary :durable))))))
(assert-event
 (not (fn-bprt-submitp
       (fn-bp-journal-nth 2 (fn-bp-apply-journal-record
                             *bpr-att-state*
                             '(:transport "work:a" "attempt:1" 0 :delivered))))))
; A recovery outcome is refused live on an unfenced image ...
(assert-event
 (not (car (fn-bp-apply-journal-record
            *bpr-att-state* '(:outcome 11 0 :recovery :committed)))))
; ... and after the restart that fences the lone intent, the intent found
; committed installs :unknown and emits nothing: no :submit without an
; ordinary :durable outcome.
(defconst *bpr-att-restarted*
  (fn-bp-journal-nth 1 (fn-bp-replay-journal
                        *bpr-node*
                        (list *bpr-config* *bpr-enqueue*
                              '(:outcome 10 0 :ordinary :durable) *bpr-attempt*))))
(assert-event (equal (fn-bp-state-fenced *bpr-att-restarted*) t))
(defconst *bpr-att-recovered*
  (fn-bp-apply-journal-record *bpr-att-restarted* '(:outcome 11 0 :recovery :committed)))
(assert-event (car *bpr-att-recovered*))
(assert-event (equal (fn-bp-journal-nth 2 *bpr-att-recovered*) nil))
(must-fail (assert-event (fn-bprt-submitp (fn-bp-journal-nth 2 *bpr-att-recovered*))))
(assert-event
 (equal (fn-bp-attempt-status
         (fn-bp-work-attempt
          (car (fn-bp-state-works (fn-bp-journal-nth 1 *bpr-att-recovered*)))))
        :unknown))
; Teeth for the :submit hypothesis: an :enqueue-ack leaves a pending :enqueue.
(assert-event
 (member-equal '(:enqueue-ack "work:a") (fn-bp-journal-nth 2 *bpr-enq-durable*)))
(must-fail
 (assert-event
  (equal (fn-bp-pending-kind (fn-bp-state-pending *bpr-enq-state*)) :attempt)))

; ---------------------------------------------------------------------------
; Teeth for the binding-state hypothesis of
; fn-bp-apply-journal-record-preserves-binding-state: a structurally valid but
; unbound image stays structurally valid through a successful live record and
; stays unbound.  The weaker preservation holds; the stronger one needs the
; hypothesis.
(defconst *bpr-ghost-work*
  (fn-bp-make-work "work:ghost" "<ghost@example.invalid>" "subject:ghost"
                   "archive:ghost" "forward:g" "dtn://peer/" "policy:1"
                   "inc:1" "auth:1" "terms:1" 0 nil nil))
(defconst *bpr-ghost-state*
  (fn-bp-make-state *bpr-node* (fn-bp-config-from-record *bpr-config*)
                    (list *bpr-ghost-work*) nil nil nil nil))
(assert-event (fn-bp-statep *bpr-ghost-state*))
(assert-event (not (fn-bp-binding-statep *bpr-ghost-state*)))
(defconst *bpr-ghost-next*
  (fn-bp-apply-journal-record
   *bpr-ghost-state*
   '(:attempt 20 0 "work:ghost" "attempt:g" 0
     "dtn://local/" "dtn://peer/" "policy:1" 3600)))
(assert-event (car *bpr-ghost-next*))
(assert-event (fn-bp-statep (fn-bp-journal-nth 1 *bpr-ghost-next*)))
(must-fail
 (assert-event (fn-bp-binding-statep (fn-bp-journal-nth 1 *bpr-ghost-next*))))
