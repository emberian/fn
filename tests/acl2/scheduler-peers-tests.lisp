; Witnesses and teeth for the per-peer scheduler table (books/scheduler-peers).
;
; The witnesses are two peers whose queues differ, so that "a tick for one
; peer touches no other peer" separates on something: peer "innA" carries the
; small article, peer "fnB" carries the large one, and each has its own
; contact and its own retry budget.

(in-package "ACL2")
(include-book "../../books/scheduler-peers")

; -----------------------------------------------------------------------------
; A reachable sender and two reachable per-peer schedulers.

(defconst *tp-groups* '("fn.letters"))
(defconst *tp-payload-small* '(72 105 13 10))
(defconst *tp-payload-big* '(76 111 110 103 13 10))
(defconst *tp-node-0* (fn-node-initial-state *tp-groups* 16))
(defconst *tp-node-1*
  (fn-node-complete
   (fn-node-prepare *tp-node-0* 9 "<small@fn.invalid>" *tp-payload-small*
                    *tp-groups* "archive-small" "subject-small"
                    "release-small" 4 841000000)
   0 9 :durable))
(defconst *tp-node*
  (fn-node-complete
   (fn-node-prepare *tp-node-1* 10 "<big@fn.invalid>" *tp-payload-big*
                    *tp-groups* "archive-big" "subject-big" "release-big" 4 841000000)
   1 10 :durable))

(defconst *tp-config*
  (fn-bp-make-config "dtn://home/fn" "dtn://peer/fn" "policy-1"
                     "receipt-authority" 1000 "home-incarnation-1"
                     "authorization-context-1"))

(defconst *tp-wf-0* (fn-bp-initial-state *tp-node* *tp-config*))
(defconst *tp-wf-1*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue *tp-wf-0* 10 0 "work-small" "<small@fn.invalid>"
                           "forward-small" "policy-1" "terms-1")
    10 0 :durable)))
(defconst *tp-wf*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue *tp-wf-1* 11 0 "work-big" "<big@fn.invalid>"
                           "forward-big" "policy-1" "terms-1")
    11 0 :durable)))
(assert-event (fn-bp-statep *tp-wf*))

(defconst *tp-conf* (fn-sched-config 4 2 16))
(defconst *tp-contact-a* (fn-sched-contact "innA" 0 100000))
(defconst *tp-contact-b* (fn-sched-contact "fnB" 0 100000))

(defconst *tp-ss-a*
  (fn-sched-open (fn-sched-admit (fn-sched-initial-state *tp-conf* 1000)
                                 "work-small" :article 10)
                 *tp-contact-a*))
(defconst *tp-ss-b*
  (fn-sched-open (fn-sched-admit (fn-sched-initial-state *tp-conf* 2000)
                                 "work-big" :article 1000)
                 *tp-contact-b*))

(assert-event (fn-sched-statep *tp-ss-a*))
(assert-event (fn-sched-statep *tp-ss-b*))
(assert-event (fn-sched-admissiblep *tp-ss-a*))
(assert-event (fn-sched-admissiblep *tp-ss-b*))

(defconst *tp-table*
  (fn-sched-table-put "fnB" *tp-ss-b*
                      (fn-sched-table-put "innA" *tp-ss-a* nil)))

(assert-event (fn-sched-tablep *tp-table*))
(assert-event (equal (fn-sched-table-peers *tp-table*) '("innA" "fnB")))
(assert-event (equal (fn-sched-table-find "innA" *tp-table*) *tp-ss-a*))
(assert-event (equal (fn-sched-table-find "fnB" *tp-table*) *tp-ss-b*))
(assert-event (null (fn-sched-table-find "absent" *tp-table*)))

; The two peers' queues are different, so the isolation witness separates on
; more than an empty queue.
(assert-event
 (and (fn-sched-queuedp "work-small" (fn-sched-queue *tp-ss-a*))
      (not (fn-sched-queuedp "work-big" (fn-sched-queue *tp-ss-a*)))
      (fn-sched-queuedp "work-big" (fn-sched-queue *tp-ss-b*))
      (not (fn-sched-queuedp "work-small" (fn-sched-queue *tp-ss-b*)))))

; -----------------------------------------------------------------------------
; One peer's tick: its own selection, its own retry charge, nothing of the
; other peer's.

(defconst *tp-ticked* (fn-sched-table-tick "innA" *tp-table* *tp-wf* "a-1"))
(defconst *tp-ticked-table* (fn-sched-result-ss *tp-ticked*))

(assert-event (fn-sched-tablep *tp-ticked-table*))

; The subject rule on the witness: what the table tick did to "innA" is what
; fn-sched-tick-step does to "innA"'s own state.
(assert-event
 (equal (fn-sched-table-find "innA" *tp-ticked-table*)
        (fn-sched-result-ss (fn-sched-tick-step *tp-ss-a* *tp-wf* "a-1"))))
(assert-event
 (equal (fn-sched-result-effects *tp-ticked*)
        (fn-sched-result-effects (fn-sched-tick-step *tp-ss-a* *tp-wf* "a-1"))))

; The tick selected "innA"'s article, not "fnB"'s, and charged "innA"'s retry
; budget alone.
(assert-event (equal (fn-sched-item-work-id (fn-sched-selection *tp-ss-a* *tp-wf*))
                     "work-small"))
(assert-event (equal (fn-sched-table-find "fnB" *tp-ticked-table*) *tp-ss-b*))
(assert-event (equal (fn-sched-retries (fn-sched-table-find "fnB" *tp-ticked-table*))
                     0))
(assert-event (equal (fn-sched-retries (fn-sched-table-find "innA" *tp-ticked-table*))
                     1))
(assert-event (equal (fn-sched-tick (fn-sched-table-find "fnB" *tp-ticked-table*))
                     0))

; -----------------------------------------------------------------------------
; Teeth, one per hypothesis.

; fn-sched-table-tick-is-the-peer-tick, hypothesis `(fn-sched-table-find peer
; tbl)': for an unbound peer the table tick is the identity, while
; fn-sched-tick-step on nil is not, so the conclusion fails without it.
(assert-event
 (let ((r (fn-sched-table-tick "absent" *tp-table* *tp-wf* "a-1")))
   (and (equal (fn-sched-result-ss r) *tp-table*)
        (null (fn-sched-result-effects r))
        (equal (fn-sched-result-wf r) *tp-wf*)
        (not (equal (fn-sched-result-ss r)
                    (fn-sched-result-ss
                     (fn-sched-tick-step (fn-sched-table-find "absent" *tp-table*)
                                         *tp-wf* "a-1")))))))

; fn-sched-tablep-of-put, hypothesis `(stringp peer)': a keyword key.
(assert-event (not (fn-sched-tablep (fn-sched-table-put :innA *tp-ss-a* nil))))

; fn-sched-tablep-of-put, hypothesis `(fn-sched-statep ss)': a value that is
; not a scheduler state.
(assert-event (not (fn-sched-tablep (fn-sched-table-put "innA" 7 nil))))

; fn-sched-tablep-of-put-when-bound, hypothesis `(fn-sched-tablep tbl)': a
; table with a duplicate key is not one, and put repairs only the first.
(defconst *tp-dup* (list (cons "innA" *tp-ss-a*) (cons "innA" *tp-ss-b*)))
(assert-event (not (fn-sched-tablep *tp-dup*)))
(assert-event (not (fn-sched-tablep (fn-sched-table-put "innA" *tp-ss-b* *tp-dup*))))

; fn-sched-table-tick-touches-only-its-peer, hypothesis `(not (equal other
; peer))': with other = peer the entry does change (the retry was charged).
(assert-event
 (not (equal (fn-sched-table-find "innA" *tp-ticked-table*)
             (fn-sched-table-find "innA" *tp-table*))))

; -----------------------------------------------------------------------------
; Install and forget.

(defconst *tp-installed*
  (fn-sched-table-install "innC" *tp-conf* 3000 *tp-table*))
(assert-event (fn-sched-tablep *tp-installed*))
(assert-event (equal (fn-sched-table-find "innC" *tp-installed*)
                     (fn-sched-initial-state *tp-conf* 3000)))
; Install never overwrites a live peer's queue.
(assert-event (equal (fn-sched-table-install "innA" *tp-conf* 3000 *tp-table*)
                     *tp-table*))
; Forget drops exactly one entry.
(assert-event (equal (fn-sched-table-forget "innA" *tp-table*)
                     (list (cons "fnB" *tp-ss-b*))))
(assert-event (fn-sched-tablep (fn-sched-table-forget "innA" *tp-table*)))
(assert-event (equal (fn-sched-table-forget "absent" *tp-table*) *tp-table*))
