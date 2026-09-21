(in-package "ACL2")
(include-book "../../books/bp-workflow-replay-status")
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

; ---------------------------------------------------------------------------
; A reopen keeps the works its history enqueued, and the host's read model
; distinguishes "no such work" from "enqueued, not yet attempted".
; Witness for fn-bp-replay-preserves-works: a replay that really runs --
; a durable attempt and an expiry over a state that already holds a work --
; still finds that work, and the replay is not a no-op (the status moved).
(defconst *bpr-ghost-replayed*
  (fn-bp-replay-records
   *bpr-ghost-state*
   (list '(:attempt 20 0 "work:ghost" "attempt:g" 0
           "dtn://local/" "dtn://peer/" "policy:1" 3600)
         '(:outcome 20 0 :ordinary :durable)
         '(:transport "work:ghost" "attempt:g" 0 :expired))
   nil))
(assert-event (car *bpr-ghost-replayed*))
(assert-event (consp (fn-bp-find-work
                      "work:ghost"
                      (fn-bp-state-works
                       (fn-bp-journal-nth 1 *bpr-ghost-replayed*)))))
(assert-event (not (equal (fn-bp-journal-nth 1 *bpr-ghost-replayed*)
                          *bpr-ghost-state*)))
; Tooth for the one hypothesis: an id the state does not hold is not found
; after the same replay either.  Replay adds no work it was not given.
(assert-event (not (consp (fn-bp-find-work
                           "work:absent"
                           (fn-bp-state-works
                            (fn-bp-journal-nth 1 *bpr-ghost-replayed*))))))

; Witness and teeth for fn-bp-durable-enqueue-holds-the-work.  The kind
; hypothesis has no reachable violating value: a pending :attempt or :receipt
; always names a work the state already holds, so the conclusion survives its
; violation; it is kept because fn-bp-replace-work adds nothing on a miss.
(defconst *bpr-prepared-enqueue*
  (fn-bp-journal-nth
   1 (fn-bp-apply-journal-record
      (fn-bp-initial-state *bpr-node* (fn-bp-config-from-record *bpr-config*))
      *bpr-enqueue*)))
(assert-event (equal (fn-bp-pending-kind
                      (fn-bp-state-pending *bpr-prepared-enqueue*))
                     :enqueue))
(assert-event (not (fn-bp-state-fenced *bpr-prepared-enqueue*)))
(assert-event (consp (fn-bp-find-work
                      "work:a"
                      (fn-bp-state-works
                       (fn-bp-result-state
                        (fn-bp-complete *bpr-prepared-enqueue* 10 0 :durable))))))
; Tooth for fn-bp-pending-matchesp: another transaction pair commits nothing.
(assert-event (not (consp (fn-bp-find-work
                           "work:a"
                           (fn-bp-state-works
                            (fn-bp-result-state
                             (fn-bp-complete *bpr-prepared-enqueue* 99 0
                                             :durable)))))))
; Tooth for the fence: an uncertain outcome fences the same pending, and the
; later durable claim adds no work.  Recovery, not a second completion.
(defconst *bpr-fenced-enqueue*
  (fn-bp-result-state
   (fn-bp-complete *bpr-prepared-enqueue* 10 0 :indeterminate)))
(assert-event (fn-bp-state-fenced *bpr-fenced-enqueue*))
(assert-event (not (consp (fn-bp-find-work
                           "work:a"
                           (fn-bp-state-works
                            (fn-bp-result-state
                             (fn-bp-complete *bpr-fenced-enqueue* 10 0
                                             :durable)))))))

; fn-bp-work-status: three distinct answers, each on a state replay reaches.
; The defect the four-node lab hit is the first of these: a committed enqueue
; read :absent, so a reopened journal looked empty to its caller.
(defconst *bpr-enqueued*
  (fn-bp-journal-nth
   1 (fn-bp-replay-journal
      *bpr-node*
      (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable)))))
(assert-event (equal (fn-bp-work-status "work:a"
                                        (fn-bp-state-works *bpr-enqueued*))
                     :outstanding))
(assert-event (equal (fn-bp-work-status "work:none"
                                        (fn-bp-state-works *bpr-enqueued*))
                     :absent))
(assert-event (equal (fn-bp-work-status
                      "work:a"
                      (fn-bp-state-works (fn-bp-journal-nth 1 *bpr-image*)))
                     :expired))
; Once the receipt of *bpr-all-kinds* commits, the work is no longer
; outstanding and reads :receipted rather than its last attempt status.
(defconst *bpr-all-kinds-image*
  (fn-bp-journal-nth 1 (fn-bp-replay-journal *bpr-node* *bpr-all-kinds*)))
(assert-event (equal (fn-bp-work-status "work:a"
                                        (fn-bp-state-works *bpr-all-kinds-image*))
                     :receipted))

; ---------------------------------------------------------------------------
; The reopened image's answers: fn-bp-work-status across a restart, and
; provenance beside it (books/bp-workflow-replay-status.lisp).

; The machine that never died, for one journal: the trace over the durable
; events, without the restart fn-bp-replay-records appends.
(defconst *bpr-inflight*
  (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable)
        *bpr-attempt* '(:outcome 11 0 :ordinary :durable)))
(defconst *bpr-inflight-pre*
  (fn-bp-trace *bpr-s0* (fn-bp-durable-events (cdr *bpr-inflight*))))
(defconst *bpr-inflight-post*
  (fn-bp-journal-nth 1 (fn-bp-replay-journal *bpr-node* *bpr-inflight*)))

; WITNESS for fn-bp-work-status-of-restart and for
; fn-bp-replay-work-status-is-the-pre-crash-status-restarted.  The two sides
; are DIFFERENT words on this journal: the attempt was in flight when the
; process died, so the reopened image marks it and the pre-crash machine does
; not.  An equality witness on which both sides read the same word would
; separate nothing.
(assert-event (fn-bp-statep *bpr-inflight-pre*))
(assert-event (equal (fn-bp-work-status "work:a"
                                        (fn-bp-state-works *bpr-inflight-pre*))
                     :intent))
(assert-event (equal (fn-bp-work-status "work:a"
                                        (fn-bp-state-works *bpr-inflight-post*))
                     :restart-observed))
(assert-event (equal (fn-bp-work-status "work:a"
                                        (fn-bp-state-works *bpr-inflight-post*))
                     (fn-bp-work-status-after-restart
                      (fn-bp-work-status "work:a"
                                         (fn-bp-state-works *bpr-inflight-pre*)))))

; The three answers that are not an attempt status are fixed points of the
; reopen, which is what makes :absent mean "no such work" and nothing else.
(assert-event (equal (fn-bp-work-status "work:none"
                                        (fn-bp-state-works *bpr-inflight-pre*))
                     :absent))
(assert-event (equal (fn-bp-work-status "work:none"
                                        (fn-bp-state-works *bpr-inflight-post*))
                     :absent))
(defconst *bpr-receipted-journal*
  (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable)
        *bpr-receipt-intent-14* '(:outcome 14 0 :ordinary :durable)))
(assert-event (car (fn-bp-replay-journal *bpr-node* *bpr-receipted-journal*)))
(assert-event
 (equal (fn-bp-work-status
         "work:a" (fn-bp-state-works
                   (fn-bp-trace *bpr-s0* (fn-bp-durable-events
                                          (cdr *bpr-receipted-journal*)))))
        :receipted))
(assert-event
 (equal (fn-bp-work-status
         "work:a" (fn-bp-state-works
                   (fn-bp-journal-nth
                    1 (fn-bp-replay-journal *bpr-node* *bpr-receipted-journal*))))
        :receipted))
; A retryable attempt status is a fixed point too: :expired survives the reopen.
(assert-event (equal (fn-bp-work-status
                      "work:a"
                      (fn-bp-state-works (fn-bp-journal-nth 1 *bpr-image*)))
                     (fn-bp-work-status-after-restart :expired)))

; TOOTH for the fn-bp-statep hypothesis of fn-bp-work-status-of-restart.  On a
; value that is not a state, fn-bp-restart is the identity, so the in-flight
; attempt is NOT marked and the two sides part.
(defconst *bpr-inflight-work*
  (fn-bp-find-work "work:a" (fn-bp-state-works *bpr-inflight-pre*)))
(defconst *bpr-not-a-state* (list 0 1 (list *bpr-inflight-work*) 3 4 5 6))
(assert-event (not (fn-bp-statep *bpr-not-a-state*)))
(assert-event (not (equal (fn-bp-work-status
                           "work:a"
                           (fn-bp-state-works (fn-bp-restart *bpr-not-a-state*)))
                          (fn-bp-work-status-after-restart
                           (fn-bp-work-status
                            "work:a"
                            (fn-bp-state-works *bpr-not-a-state*))))))

; TOOTH for the success hypothesis of
; fn-bp-replay-work-status-is-the-pre-crash-status-restarted.  An attempt
; record before any enqueue is refused, and a refusal leaves the image at the
; prefix it had reached -- which is not what the same events denote.
(defconst *bpr-attempt-before-enqueue*
  (list *bpr-config* *bpr-attempt* *bpr-enqueue*
        '(:outcome 10 0 :ordinary :durable)))
(assert-event (not (car (fn-bp-replay-journal *bpr-node*
                                              *bpr-attempt-before-enqueue*))))
(assert-event
 (not (equal (fn-bp-work-status
              "work:a"
              (fn-bp-state-works
               (fn-bp-journal-nth
                1 (fn-bp-replay-journal *bpr-node* *bpr-attempt-before-enqueue*))))
             (fn-bp-work-status-after-restart
              (fn-bp-work-status
               "work:a"
               (fn-bp-state-works
                (fn-bp-trace *bpr-s0*
                             (fn-bp-durable-events
                              (cdr *bpr-attempt-before-enqueue*)))))))))

; WITNESS for fn-bp-work-origin-at-open-is-recovered-or-absent: at open the
; recorded id list is the image's own works, so a work the cut left behind
; reads :recovered and an id the image does not hold reads :absent.
(defconst *bpr-open-ids*
  (fn-bp-work-ids (fn-bp-state-works *bpr-inflight-post*)))
(assert-event (equal *bpr-open-ids* '("work:a")))
(assert-event (equal (fn-bp-work-origin "work:a" *bpr-open-ids*
                                        (fn-bp-state-works *bpr-inflight-post*))
                     :recovered))
(assert-event (equal (fn-bp-work-origin "work:none" *bpr-open-ids*
                                        (fn-bp-state-works *bpr-inflight-post*))
                     :absent))

; WITNESS for fn-bp-durable-enqueue-after-open-reads-enqueued: the same work
; id, the same :outstanding status, and the answer the lab's assertion needs
; -- this one the session enqueued, so it reads :enqueued and not :recovered.
(defconst *bpr-enqueued-after-open*
  (fn-bp-state-works
   (fn-bp-result-state (fn-bp-complete *bpr-prepared-enqueue* 10 0 :durable))))
(assert-event (equal (fn-bp-work-status "work:a" *bpr-enqueued-after-open*)
                     :outstanding))
(assert-event (equal (fn-bp-work-origin "work:a" nil *bpr-enqueued-after-open*)
                     :enqueued))
; TOOTH for the not-already-recovered hypothesis: with that id in the recorded
; list the same works read :recovered, so the hypothesis is what separates them.
(assert-event (equal (fn-bp-work-origin "work:a" '("work:a")
                                        *bpr-enqueued-after-open*)
                     :recovered))
; TOOTH for fn-bp-pending-matchesp: another transaction pair commits nothing.
(assert-event (equal (fn-bp-work-origin
                      "work:a" nil
                      (fn-bp-state-works
                       (fn-bp-result-state
                        (fn-bp-complete *bpr-prepared-enqueue* 99 0 :durable))))
                     :absent))
; TOOTH for the not-fenced hypothesis: the fenced pending commits nothing.
(assert-event (equal (fn-bp-work-origin
                      "work:a" nil
                      (fn-bp-state-works
                       (fn-bp-result-state
                        (fn-bp-complete *bpr-fenced-enqueue* 10 0 :durable))))
                     :absent))
; TOOTH for the :enqueue kind hypothesis.  This state is CONSTRUCTED, not
; reached: fn-bp-prepare-attempt only prepares an attempt for a work the image
; already holds, so the composed machine has no :attempt pending over an image
; that holds none.  It is a legal state all the same, and the theorem
; quantifies over states, so the hypothesis is required: completing this
; pending replaces a work that is not there and the answer is :absent.
(defconst *bpr-attempt-pending*
  (fn-bp-journal-nth
   1 (fn-bp-apply-journal-record
      (fn-bp-journal-nth
       1 (fn-bp-replay-journal
          *bpr-node*
          (list *bpr-config* *bpr-enqueue* '(:outcome 10 0 :ordinary :durable))))
      *bpr-attempt*)))
(defconst *bpr-attempt-pending-no-work*
  (fn-bp-make-state (fn-bp-state-node *bpr-attempt-pending*)
                    (fn-bp-state-config *bpr-attempt-pending*)
                    nil
                    (fn-bp-state-receipts *bpr-attempt-pending*)
                    (fn-bp-state-pending *bpr-attempt-pending*)
                    nil
                    (fn-bp-state-used-txs *bpr-attempt-pending*)))
(assert-event (fn-bp-statep *bpr-attempt-pending-no-work*))
(assert-event (fn-bp-pending-matchesp *bpr-attempt-pending-no-work* 11 0))
(assert-event (not (fn-bp-state-fenced *bpr-attempt-pending-no-work*)))
(assert-event (equal (fn-bp-pending-kind
                      (fn-bp-state-pending *bpr-attempt-pending-no-work*))
                     :attempt))
(assert-event (equal (fn-bp-work-origin
                      "work:a" nil
                      (fn-bp-state-works
                       (fn-bp-result-state
                        (fn-bp-complete *bpr-attempt-pending-no-work* 11 0
                                        :durable))))
                     :absent))
