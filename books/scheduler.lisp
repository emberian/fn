; fn: the durable contact/retry scheduler (C2-06).
;
; REP-005 (specs/replication.md:58): "queue durable work with explicit resource
; limits, retry state, and policy.  Contacts and monotonic elapsed time arrive
; as environmental observations.  Scheduling may prioritize small letters and
; receipts, but starvation and eventual delivery claims require a specified
; fairness/resource policy.  Wall-clock time is not a proof of non-delivery or
; permission to reclaim an obligated object."
;
; Everything this book decides is decided from explicit inputs:
;
;   * a contact-plan observation (peer endpoint identifier, window start and
;     window end, both in the host's monotonic milliseconds, `fn-sched-contact');
;   * a clock observation and a bundle expiry decision, taken by
;     `fn-clock-expiry-decision' (books/clock.lisp) and never recomputed here;
;   * the sender's durable works, read out of an `fn-bp-statep'
;     (books/bp-workflow.lisp).  Queue membership never makes a work durable;
;     eligibility is `fn-bp-work-retryablep' of the work the workflow holds.
;
; What this book does NOT do.  It never fabricates a `:submit'.  A tick that
; selects a work drives the *workflow's* own transitions --- an
; `:attempt-prepare' event and then a `:storage-complete :durable' event,
; through `fn-bp-step' --- and emits, verbatim, whatever effects that
; dispatcher returned.  If the workflow refuses (fenced, a pending intent, a
; consumed transaction pair, a work that is not retryable) there is no effect,
; no retry is charged, and no decision is recorded.  See
; `fn-sched-selected-submit-is-a-workflow-submit' in scheduler-invariants.
;
; It never releases anything either.  An expiry observation marks the queue
; item so that selection passes it by; the work, its attempt, its receipt and
; the node's pins are the workflow's and are returned unchanged.  `:uncertain'
; is not permission (books/clock.lisp), and neither is `:expired': a bundle
; whose lifetime ran out is a bundle the local BPA may drop, not an fn
; obligation that may be discharged.
;
; Priority and aging.  Deterministic priority is receipts before articles,
; then smaller before larger, then oldest (smallest admission sequence) first.
; That order starves a large article behind a stream of small ones, and
; scheduler-tests exhibits the trace on which it does.  The aging rule is the
; fix and it is a FIFO, not a boost: an eligible item that is passed over
; counts the passes, and on reaching the configured aging limit it is appended
; once to a promotion queue that selection drains from the head.  The bound
; that follows --- selection within `aging-limit' + `queue-bound' admissible
; ticks --- is `fn-sched-aging-bound' in scheduler-invariants.

(in-package "ACL2")
(include-book "bp-workflow")
(include-book "clock")
(include-book "frame")

; This book opens two other clusters' definitions, and each is named on the
; deputy board.  `fn-clock-vocabulary' (board 2026-09-19 bp) carries
; `fn-clock-observationp', `fn-clock-age-anchorp' and `fn-clock-expiry-decision',
; which this book's guards and refusal branches read.  `fn-frame-codec-vocabulary'
; (books/frame.lisp) carries the field grammar; it is opened only around the two
; FNSC entry points below, never over a wide spec (board 2026-09-19 time-anchor).
(local (in-theory (enable fn-clock-vocabulary)))

; -----------------------------------------------------------------------------
; Contact-plan observations

(defun fn-sched-contact-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4) (equal (car x) :fn-sched-contact)))

(defun fn-sched-contact (peer start end)
  (declare (xargs :guard t))
  (list :fn-sched-contact peer start end))

(defun fn-sched-contact-peer (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-contact-start (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-sched-contact-end (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))

(defthm fn-sched-contact-shapep-of-fn-sched-contact
  (fn-sched-contact-shapep (fn-sched-contact peer start end)))
(defthm fn-sched-contact-peer-of-fn-sched-contact
  (equal (fn-sched-contact-peer (fn-sched-contact peer start end)) peer))
(defthm fn-sched-contact-start-of-fn-sched-contact
  (equal (fn-sched-contact-start (fn-sched-contact peer start end)) start))
(defthm fn-sched-contact-end-of-fn-sched-contact
  (equal (fn-sched-contact-end (fn-sched-contact peer start end)) end))
(defthm fn-sched-contact-shapep-forward-shape
  (implies (fn-sched-contact-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-sched-contact-accessors-forward-consp
  (and (implies (fn-sched-contact-peer x) (consp x))
       (implies (fn-sched-contact-start x) (consp x))
       (implies (fn-sched-contact-end x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-sched-contact-peer x) (consp x))
                  :trigger-terms ((fn-sched-contact-peer x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-contact-start x) (consp x))
                  :trigger-terms ((fn-sched-contact-start x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-contact-end x) (consp x))
                  :trigger-terms ((fn-sched-contact-end x)))))
(in-theory (disable (:d fn-sched-contact-shapep) (:d fn-sched-contact)
                    (:d fn-sched-contact-peer) (:d fn-sched-contact-start)
                    (:d fn-sched-contact-end)))

(defun fn-sched-contactp (x)
  (declare (xargs :guard t))
  (and (fn-sched-contact-shapep x)
       (stringp (fn-sched-contact-peer x))
       (fn-clock-timep (fn-sched-contact-start x))
       (fn-clock-timep (fn-sched-contact-end x))
       (<= (fn-sched-contact-start x) (fn-sched-contact-end x))))

(defthm fn-sched-contactp-forward-shape
  (implies (fn-sched-contactp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sched-contact-shapep))))

; A contact window contains a monotonic reading.  The scheduler uses this only
; to refuse a tick outside the window it was told about; it is not a clock.
(defun fn-sched-contact-holdsp (contact obs)
  (declare (xargs :guard t))
  (and (fn-sched-contactp contact)
       (fn-clock-observationp obs)
       (<= (fn-sched-contact-start contact) (fn-clock-monotonic obs))
       (<= (fn-clock-monotonic obs) (fn-sched-contact-end contact))))

; -----------------------------------------------------------------------------
; Configuration

(defun fn-sched-config-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4) (equal (car x) :fn-sched-config)))

(defun fn-sched-config (queue-bound aging-limit retry-bound)
  (declare (xargs :guard t))
  (list :fn-sched-config queue-bound aging-limit retry-bound))

(defun fn-sched-queue-bound (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-aging-limit (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-sched-retry-bound (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))

(defthm fn-sched-config-shapep-of-fn-sched-config
  (fn-sched-config-shapep (fn-sched-config queue-bound aging-limit retry-bound)))
(defthm fn-sched-queue-bound-of-fn-sched-config
  (equal (fn-sched-queue-bound (fn-sched-config queue-bound aging-limit retry-bound))
         queue-bound))
(defthm fn-sched-aging-limit-of-fn-sched-config
  (equal (fn-sched-aging-limit (fn-sched-config queue-bound aging-limit retry-bound))
         aging-limit))
(defthm fn-sched-retry-bound-of-fn-sched-config
  (equal (fn-sched-retry-bound (fn-sched-config queue-bound aging-limit retry-bound))
         retry-bound))
(defthm fn-sched-config-shapep-forward-shape
  (implies (fn-sched-config-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-sched-config-accessors-forward-consp
  (and (implies (fn-sched-queue-bound x) (consp x))
       (implies (fn-sched-aging-limit x) (consp x))
       (implies (fn-sched-retry-bound x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-sched-queue-bound x) (consp x))
                  :trigger-terms ((fn-sched-queue-bound x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-aging-limit x) (consp x))
                  :trigger-terms ((fn-sched-aging-limit x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-retry-bound x) (consp x))
                  :trigger-terms ((fn-sched-retry-bound x)))))
(in-theory (disable (:d fn-sched-config-shapep) (:d fn-sched-config)
                    (:d fn-sched-queue-bound) (:d fn-sched-aging-limit)
                    (:d fn-sched-retry-bound)))

(defun fn-sched-configp (x)
  (declare (xargs :guard t))
  (and (fn-sched-config-shapep x)
       (posp (fn-sched-queue-bound x))
       (posp (fn-sched-aging-limit x))
       (posp (fn-sched-retry-bound x))))

(defthm fn-sched-configp-forward-shape
  (implies (fn-sched-configp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sched-config-shapep))))

; -----------------------------------------------------------------------------
; Queue items
;
; (work-id class size admission-sequence passes agedp expiredp).  `class' and
; `size' are the priority inputs; `admission-sequence' is the stable
; oldest-first tiebreak; `passes' is the aging counter; `agedp' records that
; the item has already been appended to the promotion queue, so that one item
; occupies at most one promotion slot; `expiredp' records an `:expired'
; decision from books/clock.

(defun fn-sched-item-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7)))

(defun fn-sched-item (work-id class size seq passes agedp expiredp)
  (declare (xargs :guard t))
  (list work-id class size seq passes agedp expiredp))

(defun fn-sched-item-work-id (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-sched-item-class (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-item-size (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-sched-item-seq (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-sched-item-passes (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))
(defun fn-sched-item-agedp (x) (declare (xargs :guard t)) (fn-bp-nth 5 x))
(defun fn-sched-item-expiredp (x) (declare (xargs :guard t)) (fn-bp-nth 6 x))

(defthm fn-sched-item-shapep-of-fn-sched-item
  (fn-sched-item-shapep (fn-sched-item w c s q p a e)))
(defthm fn-sched-item-work-id-of-fn-sched-item
  (equal (fn-sched-item-work-id (fn-sched-item w c s q p a e)) w))
(defthm fn-sched-item-class-of-fn-sched-item
  (equal (fn-sched-item-class (fn-sched-item w c s q p a e)) c))
(defthm fn-sched-item-size-of-fn-sched-item
  (equal (fn-sched-item-size (fn-sched-item w c s q p a e)) s))
(defthm fn-sched-item-seq-of-fn-sched-item
  (equal (fn-sched-item-seq (fn-sched-item w c s q p a e)) q))
(defthm fn-sched-item-passes-of-fn-sched-item
  (equal (fn-sched-item-passes (fn-sched-item w c s q p a e)) p))
(defthm fn-sched-item-agedp-of-fn-sched-item
  (equal (fn-sched-item-agedp (fn-sched-item w c s q p a e)) a))
(defthm fn-sched-item-expiredp-of-fn-sched-item
  (equal (fn-sched-item-expiredp (fn-sched-item w c s q p a e)) e))
(defthm fn-sched-item-shapep-forward-shape
  (implies (fn-sched-item-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-sched-item-accessors-forward-consp
  (and (implies (fn-sched-item-work-id x) (consp x))
       (implies (fn-sched-item-class x) (consp x))
       (implies (fn-sched-item-size x) (consp x))
       (implies (fn-sched-item-seq x) (consp x))
       (implies (fn-sched-item-passes x) (consp x))
       (implies (fn-sched-item-agedp x) (consp x))
       (implies (fn-sched-item-expiredp x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-sched-item-work-id x) (consp x))
                  :trigger-terms ((fn-sched-item-work-id x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-item-class x) (consp x))
                  :trigger-terms ((fn-sched-item-class x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-item-size x) (consp x))
                  :trigger-terms ((fn-sched-item-size x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-item-seq x) (consp x))
                  :trigger-terms ((fn-sched-item-seq x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-item-passes x) (consp x))
                  :trigger-terms ((fn-sched-item-passes x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-item-agedp x) (consp x))
                  :trigger-terms ((fn-sched-item-agedp x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-item-expiredp x) (consp x))
                  :trigger-terms ((fn-sched-item-expiredp x)))))
(in-theory (disable (:d fn-sched-item-shapep) (:d fn-sched-item)
                    (:d fn-sched-item-work-id) (:d fn-sched-item-class)
                    (:d fn-sched-item-size) (:d fn-sched-item-seq)
                    (:d fn-sched-item-passes) (:d fn-sched-item-agedp)
                    (:d fn-sched-item-expiredp)))

(defun fn-sched-classp (x)
  (declare (xargs :guard t))
  (if (member-equal x '(:receipt :article)) t nil))

(defun fn-sched-itemp (x)
  (declare (xargs :guard t))
  (and (fn-sched-item-shapep x)
       (stringp (fn-sched-item-work-id x))
       (fn-sched-classp (fn-sched-item-class x))
       (natp (fn-sched-item-size x))
       (natp (fn-sched-item-seq x))
       (natp (fn-sched-item-passes x))
       (booleanp (fn-sched-item-agedp x))
       (booleanp (fn-sched-item-expiredp x))))

(defthm fn-sched-itemp-forward-shape
  (implies (fn-sched-itemp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sched-item-shapep))))

(defun fn-sched-item-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-sched-itemp (car xs)) (fn-sched-item-listp (cdr xs)))
    (null xs)))

(defthm fn-sched-item-listp-forward-true-listp
  (implies (fn-sched-item-listp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defun fn-sched-string-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (stringp (car xs)) (fn-sched-string-listp (cdr xs)))
    (null xs)))

(defthm fn-sched-string-listp-forward-true-listp
  (implies (fn-sched-string-listp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm fn-sched-string-listp-of-cdr
  (implies (fn-sched-string-listp xs) (fn-sched-string-listp (cdr xs))))

(defthm fn-sched-string-listp-of-append
  (implies (and (fn-sched-string-listp a) (fn-sched-string-listp b))
           (fn-sched-string-listp (append a b))))

(defun fn-sched-find (work-id xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal work-id (fn-sched-item-work-id (car xs)))
          (car xs)
        (fn-sched-find work-id (cdr xs)))
    nil))

(defun fn-sched-queuedp (work-id xs)
  (declare (xargs :guard t))
  (if (consp (fn-sched-find work-id xs)) t nil))

; -----------------------------------------------------------------------------
; Scheduler state
;
; `generation' is stable: no contact, clock, expiry or admission observation
; moves it.  It advances only on `:restart', which is what distinguishes one
; run of the scheduler from the next in the decision log.

(defun fn-sched-state-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10) (equal (car x) :fn-sched-state)))

(defun fn-sched-state (generation config queue aged contact retries tick
                                  next-tx decisions)
  (declare (xargs :guard t))
  (list :fn-sched-state generation config queue aged contact retries tick
        next-tx decisions))

(defun fn-sched-generation (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-conf (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-sched-queue (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-sched-aged (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))
(defun fn-sched-open-contact (x) (declare (xargs :guard t)) (fn-bp-nth 5 x))
(defun fn-sched-retries (x) (declare (xargs :guard t)) (fn-bp-nth 6 x))
(defun fn-sched-tick (x) (declare (xargs :guard t)) (fn-bp-nth 7 x))
(defun fn-sched-next-tx (x) (declare (xargs :guard t)) (fn-bp-nth 8 x))
(defun fn-sched-decisions (x) (declare (xargs :guard t)) (fn-bp-nth 9 x))

(defthm fn-sched-state-shapep-of-fn-sched-state
  (fn-sched-state-shapep (fn-sched-state g c q a k r tk tx d)))
(defthm fn-sched-generation-of-fn-sched-state
  (equal (fn-sched-generation (fn-sched-state g c q a k r tk tx d)) g))
(defthm fn-sched-conf-of-fn-sched-state
  (equal (fn-sched-conf (fn-sched-state g c q a k r tk tx d)) c))
(defthm fn-sched-queue-of-fn-sched-state
  (equal (fn-sched-queue (fn-sched-state g c q a k r tk tx d)) q))
(defthm fn-sched-aged-of-fn-sched-state
  (equal (fn-sched-aged (fn-sched-state g c q a k r tk tx d)) a))
(defthm fn-sched-open-contact-of-fn-sched-state
  (equal (fn-sched-open-contact (fn-sched-state g c q a k r tk tx d)) k))
(defthm fn-sched-retries-of-fn-sched-state
  (equal (fn-sched-retries (fn-sched-state g c q a k r tk tx d)) r))
(defthm fn-sched-tick-of-fn-sched-state
  (equal (fn-sched-tick (fn-sched-state g c q a k r tk tx d)) tk))
(defthm fn-sched-next-tx-of-fn-sched-state
  (equal (fn-sched-next-tx (fn-sched-state g c q a k r tk tx d)) tx))
(defthm fn-sched-decisions-of-fn-sched-state
  (equal (fn-sched-decisions (fn-sched-state g c q a k r tk tx d)) d))
(defthm fn-sched-state-shapep-forward-shape
  (implies (fn-sched-state-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-sched-state-accessors-forward-consp
  (and (implies (fn-sched-generation x) (consp x))
       (implies (fn-sched-conf x) (consp x))
       (implies (fn-sched-queue x) (consp x))
       (implies (fn-sched-aged x) (consp x))
       (implies (fn-sched-open-contact x) (consp x))
       (implies (fn-sched-retries x) (consp x))
       (implies (fn-sched-tick x) (consp x))
       (implies (fn-sched-next-tx x) (consp x))
       (implies (fn-sched-decisions x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-sched-generation x) (consp x))
                  :trigger-terms ((fn-sched-generation x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-conf x) (consp x))
                  :trigger-terms ((fn-sched-conf x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-queue x) (consp x))
                  :trigger-terms ((fn-sched-queue x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-aged x) (consp x))
                  :trigger-terms ((fn-sched-aged x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-open-contact x) (consp x))
                  :trigger-terms ((fn-sched-open-contact x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-retries x) (consp x))
                  :trigger-terms ((fn-sched-retries x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-tick x) (consp x))
                  :trigger-terms ((fn-sched-tick x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-next-tx x) (consp x))
                  :trigger-terms ((fn-sched-next-tx x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-decisions x) (consp x))
                  :trigger-terms ((fn-sched-decisions x)))))
(in-theory (disable (:d fn-sched-state-shapep) (:d fn-sched-state)
                    (:d fn-sched-generation) (:d fn-sched-conf)
                    (:d fn-sched-queue) (:d fn-sched-aged)
                    (:d fn-sched-open-contact) (:d fn-sched-retries)
                    (:d fn-sched-tick) (:d fn-sched-next-tx)
                    (:d fn-sched-decisions)))

(defun fn-sched-statep (x)
  (declare (xargs :guard t))
  (and (fn-sched-state-shapep x)
       (natp (fn-sched-generation x))
       (fn-sched-configp (fn-sched-conf x))
       (fn-sched-item-listp (fn-sched-queue x))
       (fn-sched-string-listp (fn-sched-aged x))
       (or (null (fn-sched-open-contact x))
           (fn-sched-contactp (fn-sched-open-contact x)))
       (natp (fn-sched-retries x))
       (natp (fn-sched-tick x))
       (natp (fn-sched-next-tx x))
       (true-listp (fn-sched-decisions x))))

(defthm fn-sched-statep-forward-shape
  (implies (fn-sched-statep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sched-state-shapep))))

(defthm fn-sched-statep-forward-components
  (implies (fn-sched-statep x)
           (and (fn-sched-item-listp (fn-sched-queue x))
                (fn-sched-string-listp (fn-sched-aged x))
                (fn-sched-configp (fn-sched-conf x))))
  :rule-classes :forward-chaining)

(defun fn-sched-initial-state (config next-tx)
  (declare (xargs :guard t))
  (fn-sched-state 0 config nil nil nil 0 0 next-tx nil))

; -----------------------------------------------------------------------------
; Eligibility
;
; The queue never decides that a work exists.  `fn-bp-find-work' of the
; sender's durable works decides that, and `fn-bp-work-retryablep' decides
; whether an attempt is permitted: a work with a receipt is closed, and a work
; whose attempt is still live is not retried.  A nil work is not `consp' and
; so is not outstanding and not retryable.

(defun fn-sched-eligiblep (item wf)
  (declare (xargs :guard t))
  (and (fn-sched-itemp item)
       (not (fn-sched-item-expiredp item))
       (fn-bp-work-retryablep
        (fn-bp-find-work (fn-sched-item-work-id item)
                         (fn-bp-state-works wf)))
       t))

(defun fn-sched-eligible-idp (work-id ss wf)
  (declare (xargs :guard t))
  (fn-sched-eligiblep (fn-sched-find work-id (fn-sched-queue ss)) wf))

; -----------------------------------------------------------------------------
; Deterministic priority: receipts, then smaller, then oldest

(defun fn-sched-class-rank (c)
  (declare (xargs :guard t))
  (if (equal c :receipt) 0 1))

(defun fn-sched-betterp (a b)
  (declare (xargs :guard t))
  (let ((ra (fn-sched-class-rank (fn-sched-item-class a)))
        (rb (fn-sched-class-rank (fn-sched-item-class b)))
        (sa (nfix (fn-sched-item-size a)))
        (sb (nfix (fn-sched-item-size b)))
        (qa (nfix (fn-sched-item-seq a)))
        (qb (nfix (fn-sched-item-seq b))))
    (or (< ra rb)
        (and (equal ra rb)
             (or (< sa sb)
                 (and (equal sa sb) (< qa qb)))))))

(defun fn-sched-priority-pick (queue wf best)
  (declare (xargs :guard t))
  (if (consp queue)
      (fn-sched-priority-pick
       (cdr queue) wf
       (if (and (fn-sched-eligiblep (car queue) wf)
                (or (not (consp best)) (fn-sched-betterp (car queue) best)))
           (car queue)
         best))
    best))

; -----------------------------------------------------------------------------
; The promotion queue
;
; `fn-sched-aged-advance' drops the leading promotion slots whose item is gone
; from the queue or no longer eligible.  The result is a suffix of the
; promotion queue whose head is a live eligible item, or nil.

(defun fn-sched-aged-advance (aged queue wf)
  (declare (xargs :guard t))
  (if (consp aged)
      (if (fn-sched-eligiblep (fn-sched-find (car aged) queue) wf)
          aged
        (fn-sched-aged-advance (cdr aged) queue wf))
    nil))

(defthm fn-sched-string-listp-of-aged-advance
  (implies (fn-sched-string-listp aged)
           (fn-sched-string-listp (fn-sched-aged-advance aged queue wf)))
  :hints (("Goal" :in-theory (disable fn-sched-eligiblep fn-sched-find))))

; -----------------------------------------------------------------------------
; Selection
;
; A tick is admissible when a contact is open and the contact's retry budget is
; not spent.  Selection prefers the promotion queue; only when it is empty does
; the deterministic priority order decide.

(defun fn-sched-admissiblep (ss)
  (declare (xargs :guard t))
  (and (fn-sched-statep ss)
       (consp (fn-sched-open-contact ss))
       (< (nfix (fn-sched-retries ss))
          (nfix (fn-sched-retry-bound (fn-sched-conf ss))))
       t))

(defun fn-sched-selection (ss wf)
  (declare (xargs :guard t))
  (if (not (fn-sched-admissiblep ss))
      nil
    (let ((advanced (fn-sched-aged-advance (fn-sched-aged ss)
                                           (fn-sched-queue ss) wf)))
      (if (consp advanced)
          (fn-sched-find (car advanced) (fn-sched-queue ss))
        (fn-sched-priority-pick (fn-sched-queue ss) wf nil)))))

; The admissibility test carries the state recognizer, so every transition it
; gates discharges its own guard from it and no transition re-runs the
; recognizer (docs/proof-style.md 4).
(defthm fn-sched-admissiblep-forward-statep
  (implies (fn-sched-admissiblep ss) (fn-sched-statep ss))
  :rule-classes :forward-chaining)

(defun fn-sched-selection-reason (ss wf)
  (declare (xargs :guard t))
  (if (consp (fn-sched-aged-advance (fn-sched-aged ss) (fn-sched-queue ss) wf))
      :aged
    :priority))

; -----------------------------------------------------------------------------
; Driving the workflow
;
; Two workflow events and nothing else.  Every octet of the emitted effect
; comes from `fn-bp-step'.

(defun fn-sched-drive-attempt (wf txid work-id attempt-id)
  (declare (xargs :guard t))
  (let* ((r1 (fn-bp-step wf (fn-bp-attempt-prepare-event
                             txid 0 work-id attempt-id)))
         (s1 (fn-bp-result-state r1)))
    (fn-bp-step s1 (fn-bp-storage-complete-event txid 0 :durable))))

(defun fn-sched-submit-effectp (effects)
  (declare (xargs :guard t))
  (and (consp effects)
       (null (cdr effects))
       (equal (fn-bp-nth 0 (car effects)) :submit)
       t))

(defun fn-sched-submit-for-idp (work-id effects)
  (declare (xargs :guard t))
  (and (fn-sched-submit-effectp effects)
       (equal (fn-bp-nth 1 (car effects)) work-id)
       t))

; -----------------------------------------------------------------------------
; Counter maintenance after a tick

(defun fn-sched-bump-item (item wf selected-id limit)
  (declare (xargs :guard t))
  (if (equal (fn-sched-item-work-id item) selected-id)
      (fn-sched-item (fn-sched-item-work-id item) (fn-sched-item-class item)
                     (fn-sched-item-size item) (fn-sched-item-seq item)
                     0 nil (fn-sched-item-expiredp item))
    (if (fn-sched-eligiblep item wf)
        (let ((next (+ 1 (nfix (fn-sched-item-passes item)))))
          (fn-sched-item (fn-sched-item-work-id item)
                         (fn-sched-item-class item) (fn-sched-item-size item)
                         (fn-sched-item-seq item) next
                         (if (or (fn-sched-item-agedp item)
                                 (<= (nfix limit) next))
                             t nil)
                         (fn-sched-item-expiredp item)))
      item)))

(defun fn-sched-bump-queue (queue wf selected-id limit)
  (declare (xargs :guard t))
  (if (consp queue)
      (cons (fn-sched-bump-item (car queue) wf selected-id limit)
            (fn-sched-bump-queue (cdr queue) wf selected-id limit))
    nil))

; The work-ids promoted by this tick, in queue order.  An item is promoted the
; first time its pass count reaches the limit and never twice.
(defun fn-sched-promotions (queue wf selected-id limit)
  (declare (xargs :guard t))
  (if (consp queue)
      (let ((item (car queue)))
        (if (and (not (equal (fn-sched-item-work-id item) selected-id))
                 (fn-sched-eligiblep item wf)
                 (not (fn-sched-item-agedp item))
                 (<= (nfix limit) (+ 1 (nfix (fn-sched-item-passes item)))))
            (cons (fn-sched-item-work-id item)
                  (fn-sched-promotions (cdr queue) wf selected-id limit))
          (fn-sched-promotions (cdr queue) wf selected-id limit)))
    nil))

(defthm fn-sched-string-listp-of-promotions
  (implies (fn-sched-item-listp queue)
           (fn-sched-string-listp
            (fn-sched-promotions queue wf selected-id limit)))
  :hints (("Goal" :in-theory (disable fn-sched-eligiblep))))

(defun fn-sched-next-aged (ss wf selected-id)
  (declare (xargs :guard (fn-sched-statep ss)))
  (let* ((limit (fn-sched-aging-limit (fn-sched-conf ss)))
         (advanced (fn-sched-aged-advance (fn-sched-aged ss)
                                          (fn-sched-queue ss) wf))
         (rest (if (and (consp advanced) (equal (car advanced) selected-id))
                   (cdr advanced)
                 advanced)))
    (append rest (fn-sched-promotions (fn-sched-queue ss) wf selected-id
                                      limit))))

(defthm fn-sched-string-listp-of-next-aged
  (implies (fn-sched-statep ss)
           (fn-sched-string-listp (fn-sched-next-aged ss wf selected-id)))
  :hints (("Goal" :in-theory (disable fn-sched-aged-advance
                                      fn-sched-promotions
                                      fn-sched-eligiblep))))

; -----------------------------------------------------------------------------
; The durable decision record
;
; Proposed FNWF record kind `:schedule', field specification
;   (:nat :nat :text :text :text :nat (:enum :aged :priority) :nat)
; = (generation tick peer work-id attempt-id attempt-generation reason passes).
; `books/frame' owns the grammar; this book models the shape and validates it
; against `fn-frame-values-okp', so the host never decides what a decision
; record is.  Until the frame owner adds the row to
; `*fn-frame-workflow-kinds*' the host writes the record in its own FNSC
; family below, with the same header, the same field encoding and the same
; A-CRYPTO trailer.  specs/scheduler.md carries the proposal.

(defconst *fn-sched-reasons* '(:aged :priority))

(defconst *fn-sched-decision-spec*
  (list :nat :nat :text :text :text :nat (cons :enum *fn-sched-reasons*) :nat))

(defun fn-sched-decision (generation tick peer work-id attempt-id
                                     attempt-generation reason passes)
  (declare (xargs :guard t))
  (list generation tick peer work-id attempt-id attempt-generation reason
        passes))

(defun fn-sched-decision-recordp (values)
  (declare (xargs :guard t))
  (and (fn-frame-values-okp *fn-sched-decision-spec* values) t))

(defconst *fn-sched-magic* '(70 78 83 67)) ; FNSC
(defconst *fn-sched-kind* 1)
(defconst *fn-sched-max-payload* 4096)

; The frame grammar never opens here (board 2026-09-19 time-anchor, NOTE on
; `fn-anchor-encode'): `fn-frame-fields-octets' has `fn-frame-values-okp' as its
; guard, and that is exactly the conjunct `fn-sched-decision-recordp' already
; checked.  The two guard obligations below are discharged from that one
; equality, stated `:rule-classes nil' and cited by `:use'.
(defthm fn-sched-decision-recordp-is-frame-values-okp
  (implies (fn-sched-decision-recordp values)
           (fn-frame-values-okp *fn-sched-decision-spec* values))
  :rule-classes nil)

(defun fn-sched-decision-protected (values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-sched-decision-recordp values))
      :bad
    (let ((payload (fn-frame-fields-octets *fn-sched-decision-spec* values)))
      (if (not (<= (len payload) *fn-sched-max-payload*))
          :bad
        (fn-frame-protected *fn-sched-magic* *fn-frame-version*
                            *fn-sched-kind* payload)))))

(verify-guards fn-sched-decision-protected
  :hints (("Goal" :use fn-sched-decision-recordp-is-frame-values-okp)))

(defun fn-sched-decision-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-sched-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-sched-magic*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)
                    (equal (fn-frame-result-kind frame) *fn-sched-kind*)))
          (fn-frame-error :magic)
        (let ((parsed (fn-frame-fields-parse *fn-sched-decision-spec*
                                             (fn-frame-result-payload frame))))
          (if (not (fn-frame-parse-okp parsed))
              (fn-frame-error (fn-frame-parse-value parsed))
            (if (not (fn-sched-decision-recordp (fn-frame-parse-value parsed)))
                (fn-frame-error :fields)
              (fn-frame-ok *fn-sched-magic* *fn-frame-version* *fn-sched-kind*
                           (fn-frame-parse-value parsed)))))))))

; `fn-frame-decode-payload-octets' is withdrawn under
; `fn-frame-fields-vocabulary' (books/frame-fields.lisp); cited, not enabled.
(verify-guards fn-sched-decision-decode
  :hints (("Goal" :use ((:instance fn-frame-decode-payload-octets
                                   (max-payload *fn-sched-max-payload*))))))

; -----------------------------------------------------------------------------
; Results

(defun fn-sched-result-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))

(defun fn-sched-result (ss wf effects)
  (declare (xargs :guard t))
  (list ss wf effects))

(defun fn-sched-result-ss (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-sched-result-wf (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-result-effects (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))

(defthm fn-sched-result-shapep-of-fn-sched-result
  (fn-sched-result-shapep (fn-sched-result ss wf fx)))
(defthm fn-sched-result-ss-of-fn-sched-result
  (equal (fn-sched-result-ss (fn-sched-result ss wf fx)) ss))
(defthm fn-sched-result-wf-of-fn-sched-result
  (equal (fn-sched-result-wf (fn-sched-result ss wf fx)) wf))
(defthm fn-sched-result-effects-of-fn-sched-result
  (equal (fn-sched-result-effects (fn-sched-result ss wf fx)) fx))
(defthm fn-sched-result-shapep-forward-shape
  (implies (fn-sched-result-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-sched-result-accessors-forward-consp
  (and (implies (fn-sched-result-ss x) (consp x))
       (implies (fn-sched-result-wf x) (consp x))
       (implies (fn-sched-result-effects x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-sched-result-ss x) (consp x))
                  :trigger-terms ((fn-sched-result-ss x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-result-wf x) (consp x))
                  :trigger-terms ((fn-sched-result-wf x)))
                 (:forward-chaining
                  :corollary (implies (fn-sched-result-effects x) (consp x))
                  :trigger-terms ((fn-sched-result-effects x)))))
(in-theory (disable (:d fn-sched-result-shapep) (:d fn-sched-result)
                    (:d fn-sched-result-ss) (:d fn-sched-result-wf)
                    (:d fn-sched-result-effects)))

; -----------------------------------------------------------------------------
; The contact tick
;
; Three outcomes, kept distinct all the way out:
;
;   not admissible      only the tick counter moves.  A work cannot be "passed
;                       over" when no contact is open or the retry budget is
;                       spent, so no pass is counted and the promotion queue is
;                       untouched.
;   nothing selected    every eligible item counts a pass and may be promoted.
;                       No effect; the workflow is returned unchanged.
;   selected            the workflow is driven.  If, and only if, the workflow
;                       emitted its own `:submit', the retry is charged, the
;                       decision is recorded and the counters move.  A refusal
;                       leaves the scheduler and the workflow exactly as they
;                       were --- a refused submit is not a pass.

(defun fn-sched-with-tick (ss)
  (declare (xargs :guard t))
  (fn-sched-state (fn-sched-generation ss) (fn-sched-conf ss)
                  (fn-sched-queue ss) (fn-sched-aged ss)
                  (fn-sched-open-contact ss) (fn-sched-retries ss)
                  (+ 1 (nfix (fn-sched-tick ss))) (fn-sched-next-tx ss)
                  (fn-sched-decisions ss)))

(defun fn-sched-pass-over (ss wf)
  (declare (xargs :guard (fn-sched-statep ss)))
  (let ((limit (fn-sched-aging-limit (fn-sched-conf ss))))
    (fn-sched-state
     (fn-sched-generation ss) (fn-sched-conf ss)
     (fn-sched-bump-queue (fn-sched-queue ss) wf nil limit)
     (fn-sched-next-aged ss wf nil)
     (fn-sched-open-contact ss) (fn-sched-retries ss)
     (+ 1 (nfix (fn-sched-tick ss))) (fn-sched-next-tx ss)
     (fn-sched-decisions ss))))

(defun fn-sched-take (ss wf selected)
  (declare (xargs :guard (fn-sched-statep ss)))
  (let* ((limit (fn-sched-aging-limit (fn-sched-conf ss)))
         (id (fn-sched-item-work-id selected)))
    (fn-sched-state
     (fn-sched-generation ss) (fn-sched-conf ss)
     (fn-sched-bump-queue (fn-sched-queue ss) wf id limit)
     (fn-sched-next-aged ss wf id)
     (fn-sched-open-contact ss) (+ 1 (nfix (fn-sched-retries ss)))
     (+ 1 (nfix (fn-sched-tick ss))) (+ 1 (nfix (fn-sched-next-tx ss)))
     (fn-sched-decisions ss))))

(defun fn-sched-record-decision (ss wf selected attempt-id)
  (declare (xargs :guard t))
  (cons (fn-sched-decision
         (fn-sched-generation ss) (nfix (fn-sched-tick ss))
         (fn-sched-contact-peer (fn-sched-open-contact ss))
         (fn-sched-item-work-id selected) attempt-id
         (nfix (fn-bp-work-next-generation
                (fn-bp-find-work (fn-sched-item-work-id selected)
                                 (fn-bp-state-works wf))))
         (fn-sched-selection-reason ss wf)
         (nfix (fn-sched-item-passes selected)))
        (fn-sched-decisions ss)))

(defun fn-sched-with-decisions (ss decisions)
  (declare (xargs :guard t))
  (fn-sched-state (fn-sched-generation ss) (fn-sched-conf ss)
                  (fn-sched-queue ss) (fn-sched-aged ss)
                  (fn-sched-open-contact ss) (fn-sched-retries ss)
                  (fn-sched-tick ss) (fn-sched-next-tx ss) decisions))

(defun fn-sched-tick-step (ss wf attempt-id)
  (declare (xargs :guard t))
  (if (not (fn-sched-admissiblep ss))
      (fn-sched-result (fn-sched-with-tick ss) wf nil)
    (let ((selected (fn-sched-selection ss wf)))
      (if (not (consp selected))
          (fn-sched-result (fn-sched-pass-over ss wf) wf nil)
        (let* ((decision (fn-sched-record-decision ss wf selected attempt-id))
               (driven (fn-sched-drive-attempt
                        wf (fn-sched-next-tx ss)
                        (fn-sched-item-work-id selected) attempt-id))
               (effects (fn-bp-result-effects driven)))
          (if (not (fn-sched-submit-for-idp
                    (fn-sched-item-work-id selected) effects))
              (fn-sched-result ss wf nil)
            (fn-sched-result
             (fn-sched-with-decisions (fn-sched-take ss wf selected) decision)
             (fn-bp-result-state driven)
             effects)))))))

; -----------------------------------------------------------------------------
; Admission, contact and expiry observations
;
; None of these touch the workflow.  `fn-sched-step' returns WF itself on every
; one of them, which is how "expiry and contact loss leave the work and its
; pins untouched" is stated in scheduler-invariants.

(defun fn-sched-admit (ss work-id class size)
  (declare (xargs :guard t))
  (if (or (not (fn-sched-statep ss))
          (not (stringp work-id))
          (not (fn-sched-classp class))
          (not (natp size))
          (fn-sched-queuedp work-id (fn-sched-queue ss))
          (<= (nfix (fn-sched-queue-bound (fn-sched-conf ss)))
              (len (fn-sched-queue ss))))
      ss
    (fn-sched-state
     (fn-sched-generation ss) (fn-sched-conf ss)
     (append (fn-sched-queue ss)
             (list (fn-sched-item work-id class size
                                  (len (fn-sched-queue ss)) 0 nil nil)))
     (fn-sched-aged ss) (fn-sched-open-contact ss) (fn-sched-retries ss)
     (fn-sched-tick ss) (fn-sched-next-tx ss) (fn-sched-decisions ss))))

(defun fn-sched-open (ss contact)
  (declare (xargs :guard t))
  (if (or (not (fn-sched-statep ss)) (not (fn-sched-contactp contact)))
      ss
    (fn-sched-state
     (fn-sched-generation ss) (fn-sched-conf ss) (fn-sched-queue ss)
     (fn-sched-aged ss) contact 0 (fn-sched-tick ss) (fn-sched-next-tx ss)
     (fn-sched-decisions ss))))

(defun fn-sched-close (ss)
  (declare (xargs :guard t))
  (if (not (fn-sched-statep ss))
      ss
    (fn-sched-state
     (fn-sched-generation ss) (fn-sched-conf ss) (fn-sched-queue ss)
     (fn-sched-aged ss) nil 0 (fn-sched-tick ss) (fn-sched-next-tx ss)
     (fn-sched-decisions ss))))

(defun fn-sched-mark-expired (item)
  (declare (xargs :guard t))
  (fn-sched-item (fn-sched-item-work-id item) (fn-sched-item-class item)
                 (fn-sched-item-size item) (fn-sched-item-seq item)
                 (fn-sched-item-passes item) (fn-sched-item-agedp item) t))

(defun fn-sched-expire-queue (work-id queue)
  (declare (xargs :guard t))
  (if (consp queue)
      (if (equal work-id (fn-sched-item-work-id (car queue)))
          (cons (fn-sched-mark-expired (car queue)) (cdr queue))
        (cons (car queue) (fn-sched-expire-queue work-id (cdr queue))))
    nil))

; The decision is taken by books/clock and only `:expired' acts.  `:live' and
; `:uncertain' leave the item schedulable; `:uncertain' is not permission.
(defun fn-sched-observe-expiry (ss work-id creation-time lifetime anchor obs)
  (declare (xargs :guard t))
  (if (or (not (fn-sched-statep ss))
          (not (fn-clock-timep creation-time))
          (not (fn-clock-timep lifetime))
          (not (fn-clock-age-anchorp anchor))
          (not (fn-clock-observationp obs)))
      ss
    (if (not (equal (fn-clock-expiry-decision creation-time lifetime anchor obs)
                    :expired))
        ss
      (fn-sched-state
       (fn-sched-generation ss) (fn-sched-conf ss)
       (fn-sched-expire-queue work-id (fn-sched-queue ss))
       (fn-sched-aged ss) (fn-sched-open-contact ss) (fn-sched-retries ss)
       (fn-sched-tick ss) (fn-sched-next-tx ss) (fn-sched-decisions ss)))))

(defun fn-sched-restart (ss)
  (declare (xargs :guard t))
  (if (not (fn-sched-statep ss))
      ss
    (fn-sched-state
     (+ 1 (nfix (fn-sched-generation ss))) (fn-sched-conf ss)
     (fn-sched-queue ss) (fn-sched-aged ss) nil 0 (fn-sched-tick ss)
     (fn-sched-next-tx ss) (fn-sched-decisions ss))))

; -----------------------------------------------------------------------------
; Observation events and finite traces

(defun fn-sched-admit-event (work-id class size)
  (declare (xargs :guard t))
  (list :admit work-id class size))
(defun fn-sched-open-event (peer start end)
  (declare (xargs :guard t))
  (list :contact-open (fn-sched-contact peer start end)))
(defun fn-sched-close-event ()
  (declare (xargs :guard t))
  (list :contact-close))
(defun fn-sched-tick-event (attempt-id obs)
  (declare (xargs :guard t))
  (list :tick attempt-id obs))
(defun fn-sched-expiry-event (work-id creation-time lifetime anchor obs)
  (declare (xargs :guard t))
  (list :expiry work-id creation-time lifetime anchor obs))
(defun fn-sched-transport-event (work-id attempt-id generation status)
  (declare (xargs :guard t))
  (list :transport work-id attempt-id generation status))
(defun fn-sched-restart-event ()
  (declare (xargs :guard t))
  (list :restart))

(defun fn-sched-eventp (event)
  (declare (xargs :guard t))
  (let ((kind (fn-bp-nth 0 event)))
    (cond ((equal kind :admit)
           (and (true-listp event) (equal (len event) 4)
                (stringp (fn-bp-nth 1 event))
                (fn-sched-classp (fn-bp-nth 2 event))
                (natp (fn-bp-nth 3 event))))
          ((equal kind :contact-open)
           (and (true-listp event) (equal (len event) 2)
                (fn-sched-contactp (fn-bp-nth 1 event))))
          ((equal kind :contact-close)
           (and (true-listp event) (equal (len event) 1)))
          ((equal kind :tick)
           (and (true-listp event) (equal (len event) 3)
                (stringp (fn-bp-nth 1 event))
                (fn-clock-observationp (fn-bp-nth 2 event))))
          ((equal kind :expiry)
           (and (true-listp event) (equal (len event) 6)
                (stringp (fn-bp-nth 1 event))
                (fn-clock-timep (fn-bp-nth 2 event))
                (fn-clock-timep (fn-bp-nth 3 event))
                (fn-clock-age-anchorp (fn-bp-nth 4 event))
                (fn-clock-observationp (fn-bp-nth 5 event))))
          ((equal kind :transport)
           (and (true-listp event) (equal (len event) 5)
                (stringp (fn-bp-nth 1 event))
                (stringp (fn-bp-nth 2 event))
                (natp (fn-bp-nth 3 event))
                (fn-bp-transport-statusp (fn-bp-nth 4 event))))
          (t (and (equal kind :restart) (true-listp event)
                  (equal (len event) 1))))))

(defun fn-sched-eventp-listp (events)
  (declare (xargs :guard t))
  (if (consp events)
      (and (fn-sched-eventp (car events)) (fn-sched-eventp-listp (cdr events)))
    (null events)))

; A tick outside the open contact's window is not a contact tick.  It advances
; the tick counter and nothing else; the contact plan, not the scheduler, says
; when the peer is reachable.
(defun fn-sched-step (ss wf event)
  (declare (xargs :guard t))
  (let ((kind (fn-bp-nth 0 event)))
    (cond ((equal kind :admit)
           (fn-sched-result (fn-sched-admit ss (fn-bp-nth 1 event)
                                            (fn-bp-nth 2 event)
                                            (fn-bp-nth 3 event))
                            wf nil))
          ((equal kind :contact-open)
           (fn-sched-result (fn-sched-open ss (fn-bp-nth 1 event)) wf nil))
          ((equal kind :contact-close)
           (fn-sched-result (fn-sched-close ss) wf nil))
          ((equal kind :tick)
           (if (fn-sched-contact-holdsp (fn-sched-open-contact ss)
                                        (fn-bp-nth 2 event))
               (fn-sched-tick-step ss wf (fn-bp-nth 1 event))
             (fn-sched-result (fn-sched-with-tick ss) wf nil)))
          ((equal kind :expiry)
           (fn-sched-result
            (fn-sched-observe-expiry ss (fn-bp-nth 1 event)
                                     (fn-bp-nth 2 event) (fn-bp-nth 3 event)
                                     (fn-bp-nth 4 event) (fn-bp-nth 5 event))
            wf nil))
          ((equal kind :transport)
           ; Relayed, not decided.  The scheduler has no opinion about
           ; transport evidence; `fn-bp-observe-transport' rules on it and the
           ; scheduler's own state does not move.  The relay exists so that a
           ; composed trace can re-arm a work whose attempt ended
           ; `:no-contact' or `:expired', which is what a contact plan with a
           ; missed window actually produces.
           (fn-sched-result
            ss (fn-bp-result-state
                (fn-bp-step wf (fn-bp-transport-event
                                (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                                (fn-bp-nth 3 event) (fn-bp-nth 4 event))))
            nil))
          ((equal kind :restart)
           (fn-sched-result (fn-sched-restart ss) wf nil))
          (t (fn-sched-result ss wf nil)))))

; A fold that recurs on a list while threading two kernel states must NAME its
; measure: ACL2 guesses the first formal and then opens the whole scheduler
; inside the termination proof (deputy board 2026-09-19, w3-fragment-container).
(defun fn-sched-trace (ss wf events)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (consp events)
      (let ((r (fn-sched-step ss wf (car events))))
        (fn-sched-trace (fn-sched-result-ss r) (fn-sched-result-wf r)
                        (cdr events)))
    (fn-sched-result ss wf nil)))

; -----------------------------------------------------------------------------
; The hypotheses the progress results take
;
; `fn-sched-drive-okp' is the capacity hypothesis, stated at one tick: when the
; scheduler has selected a work, the durable store accepts the intent and the
; workflow emits its own submit.  It says nothing about WHICH work is selected,
; so it cannot supply the conclusion of the aging bound.  A fenced workflow, a
; workflow with a pending intent and a consumed transaction pair all falsify
; it, and scheduler-tests exhibits each.

(defun fn-sched-drive-okp (ss wf attempt-id)
  (declare (xargs :guard t))
  (let ((selected (fn-sched-selection ss wf)))
    (or (not (consp selected))
        (fn-sched-submit-for-idp
         (fn-sched-item-work-id selected)
         (fn-bp-result-effects
          (fn-sched-drive-attempt wf (fn-sched-next-tx ss)
                                  (fn-sched-item-work-id selected)
                                  attempt-id))))))

; N consecutive admissible contact ticks on which the store accepts.  The
; countdown is `(- (nfix n) 1)' in all three run predicates: and the test is `(zp (nfix n))':
; `zp' has `natp' for a guard and `-' needs a number, and these predicates are
; hypotheses of keystones that must not carry a `natp'. Under `(not (zp n))'
; both forms are `n' itself, so no statement changes.
(defun fn-sched-contact-runp (ss wf n attempt-id)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp (nfix n))
      t
    (and (fn-sched-admissiblep ss)
         (fn-sched-drive-okp ss wf attempt-id)
         (let ((r (fn-sched-tick-step ss wf attempt-id)))
           (fn-sched-contact-runp (fn-sched-result-ss r)
                                  (fn-sched-result-wf r) (- (nfix n) 1) attempt-id)))))

; WORK-ID is eligible at each of N consecutive ticks.
(defun fn-sched-eligible-runp (ss wf n attempt-id work-id)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp (nfix n))
      t
    (and (fn-sched-eligible-idp work-id ss wf)
         (let ((r (fn-sched-tick-step ss wf attempt-id)))
           (fn-sched-eligible-runp (fn-sched-result-ss r)
                                   (fn-sched-result-wf r) (- (nfix n) 1) attempt-id
                                   work-id)))))

; WORK-ID receives a submit within N ticks.
(defun fn-sched-selected-withinp (ss wf n attempt-id work-id)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp (nfix n))
      nil
    (let ((r (fn-sched-tick-step ss wf attempt-id)))
      (if (fn-sched-submit-for-idp work-id (fn-sched-result-effects r))
          t
        (fn-sched-selected-withinp (fn-sched-result-ss r)
                                   (fn-sched-result-wf r) (- (nfix n) 1) attempt-id
                                   work-id)))))

; The position of a work-id in the promotion queue; the length when absent.
(defun fn-sched-pos (x lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (if (equal x (car lst)) 0 (+ 1 (fn-sched-pos x (cdr lst))))
    0))

(defun fn-sched-aging-horizon (ss)
  (declare (xargs :guard t))
  (+ (nfix (fn-sched-aging-limit (fn-sched-conf ss)))
     (nfix (fn-sched-queue-bound (fn-sched-conf ss)))))

; The promotion queue holds at most one slot per queued item, so it fits
; inside the configured queue bound.  Carried as an explicit hypothesis of the
; aging bound rather than assumed: scheduler-tests exhibits a reachable state
; satisfying it and the must-fail case without it.
(defun fn-sched-aged-fitsp (ss)
  (declare (xargs :guard t))
  (<= (len (fn-sched-aged ss))
      (nfix (fn-sched-queue-bound (fn-sched-conf ss)))))

; -----------------------------------------------------------------------------
; The stated unfair policy
;
; Identical to the scheduler above except that selection never consults the
; promotion queue: deterministic priority decides every tick.  It is defined
; here so that the starvation counterexample is a runnable trace about a policy
; fn wrote down, not a story about a policy nobody wrote down.

(defun fn-sched-unfair-selection (ss wf)
  (declare (xargs :guard t))
  (if (not (fn-sched-admissiblep ss))
      nil
    (fn-sched-priority-pick (fn-sched-queue ss) wf nil)))

(defun fn-sched-unfair-take (ss wf selected)
  (declare (xargs :guard t))
  (fn-sched-state
   (fn-sched-generation ss) (fn-sched-conf ss)
   (fn-sched-bump-queue (fn-sched-queue ss) wf
                        (fn-sched-item-work-id selected)
                        (fn-sched-aging-limit (fn-sched-conf ss)))
   (fn-sched-aged ss) (fn-sched-open-contact ss)
   (+ 1 (nfix (fn-sched-retries ss))) (+ 1 (nfix (fn-sched-tick ss)))
   (+ 1 (nfix (fn-sched-next-tx ss))) (fn-sched-decisions ss)))

(defun fn-sched-unfair-tick-step (ss wf attempt-id)
  (declare (xargs :guard t))
  (if (not (fn-sched-admissiblep ss))
      (fn-sched-result (fn-sched-with-tick ss) wf nil)
    (let ((selected (fn-sched-unfair-selection ss wf)))
      (if (not (consp selected))
          (fn-sched-result (fn-sched-with-tick ss) wf nil)
        (let* ((driven (fn-sched-drive-attempt
                        wf (fn-sched-next-tx ss)
                        (fn-sched-item-work-id selected) attempt-id))
               (effects (fn-bp-result-effects driven)))
          (if (not (fn-sched-submit-for-idp
                    (fn-sched-item-work-id selected) effects))
              (fn-sched-result ss wf nil)
            (fn-sched-result (fn-sched-unfair-take ss wf selected)
                             (fn-bp-result-state driven) effects)))))))

(defun fn-sched-unfair-step (ss wf event)
  (declare (xargs :guard t))
  (if (equal (fn-bp-nth 0 event) :tick)
      (if (fn-sched-contact-holdsp (fn-sched-open-contact ss)
                                   (fn-bp-nth 2 event))
          (fn-sched-unfair-tick-step ss wf (fn-bp-nth 1 event))
        (fn-sched-result (fn-sched-with-tick ss) wf nil))
    (fn-sched-step ss wf event)))

(defun fn-sched-unfair-trace (ss wf events)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (consp events)
      (let ((r (fn-sched-unfair-step ss wf (car events))))
        (fn-sched-unfair-trace (fn-sched-result-ss r) (fn-sched-result-wf r)
                               (cdr events)))
    (fn-sched-result ss wf nil)))

; Whether any tick of a trace emitted a submit for WORK-ID, under each policy.
; The starvation counterexample is the pair of answers on one trace.
(defun fn-sched-submitted-in-trace (ss wf events work-id)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (consp events)
      (let ((r (fn-sched-step ss wf (car events))))
        (or (fn-sched-submit-for-idp work-id (fn-sched-result-effects r))
            (fn-sched-submitted-in-trace (fn-sched-result-ss r)
                                         (fn-sched-result-wf r) (cdr events)
                                         work-id)))
    nil))

(defun fn-sched-unfair-submitted-in-trace (ss wf events work-id)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (consp events)
      (let ((r (fn-sched-unfair-step ss wf (car events))))
        (or (fn-sched-submit-for-idp work-id (fn-sched-result-effects r))
            (fn-sched-unfair-submitted-in-trace
             (fn-sched-result-ss r) (fn-sched-result-wf r) (cdr events)
             work-id)))
    nil))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md §2)
;
; What leaves this book enabled: the keystones proved above, the record lemmas
; and the three forward-chaining shape facts of each of the five records, the
; list-recursive vocabulary the proofs induct on (`fn-sched-item-listp',
; `fn-sched-string-listp', `fn-sched-find', `fn-sched-queuedp',
; `fn-sched-eventp-listp', `fn-sched-pos'), and the small glue predicates
; written in accessor vocabulary (`fn-sched-classp', `fn-sched-class-rank',
; `fn-sched-betterp', `fn-sched-submit-effectp', `fn-sched-submit-for-idp').
;
; What is withdrawn: the recognizers, the initial state, every transition, the
; selection machinery and the two FNSC codec entry points.  `scheduler-invariants'
; opens them under this one name.

(deftheory fn-sched-vocabulary
  '(fn-sched-contactp fn-sched-contact-holdsp fn-sched-configp fn-sched-itemp
    fn-sched-statep fn-sched-initial-state
    fn-sched-eligiblep fn-sched-eligible-idp
    fn-sched-priority-pick fn-sched-aged-advance
    fn-sched-admissiblep fn-sched-selection fn-sched-selection-reason
    fn-sched-drive-attempt
    fn-sched-bump-item fn-sched-bump-queue fn-sched-promotions
    fn-sched-next-aged
    fn-sched-with-tick fn-sched-pass-over fn-sched-take
    fn-sched-record-decision fn-sched-with-decisions fn-sched-tick-step
    fn-sched-admit fn-sched-open fn-sched-close
    fn-sched-mark-expired fn-sched-expire-queue fn-sched-observe-expiry
    fn-sched-restart
    fn-sched-admit-event fn-sched-open-event fn-sched-close-event
    fn-sched-tick-event fn-sched-expiry-event fn-sched-transport-event
    fn-sched-restart-event
    fn-sched-eventp fn-sched-step fn-sched-trace
    fn-sched-drive-okp fn-sched-contact-runp fn-sched-eligible-runp
    fn-sched-selected-withinp fn-sched-aging-horizon fn-sched-aged-fitsp
    fn-sched-unfair-selection fn-sched-unfair-take fn-sched-unfair-tick-step
    fn-sched-unfair-step fn-sched-unfair-trace
    fn-sched-submitted-in-trace fn-sched-unfair-submitted-in-trace))

(deftheory fn-sched-codec-vocabulary
  '(fn-sched-decision fn-sched-decision-recordp fn-sched-decision-protected
    fn-sched-decision-decode))

(in-theory (disable fn-sched-vocabulary fn-sched-codec-vocabulary))
