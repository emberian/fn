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

; -----------------------------------------------------------------------------
; Contact-plan observations

(defun fn-sched-contact (peer start end)
  (declare (xargs :guard t))
  (list :fn-sched-contact peer start end))

(defun fn-sched-contact-peer (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-contact-start (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-sched-contact-end (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))

(defun fn-sched-contactp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (equal (car x) :fn-sched-contact)
       (stringp (fn-sched-contact-peer x))
       (fn-clock-timep (fn-sched-contact-start x))
       (fn-clock-timep (fn-sched-contact-end x))
       (<= (fn-sched-contact-start x) (fn-sched-contact-end x))))

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

(defun fn-sched-config (queue-bound aging-limit retry-bound)
  (declare (xargs :guard t))
  (list :fn-sched-config queue-bound aging-limit retry-bound))

(defun fn-sched-queue-bound (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-aging-limit (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-sched-retry-bound (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))

(defun fn-sched-configp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (equal (car x) :fn-sched-config)
       (posp (fn-sched-queue-bound x))
       (posp (fn-sched-aging-limit x))
       (posp (fn-sched-retry-bound x))))

; -----------------------------------------------------------------------------
; Queue items
;
; (work-id class size admission-sequence passes agedp expiredp).  `class' and
; `size' are the priority inputs; `admission-sequence' is the stable
; oldest-first tiebreak; `passes' is the aging counter; `agedp' records that
; the item has already been appended to the promotion queue, so that one item
; occupies at most one promotion slot; `expiredp' records an `:expired'
; decision from books/clock.

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

(defun fn-sched-classp (x)
  (declare (xargs :guard t))
  (if (member-equal x '(:receipt :article)) t nil))

(defun fn-sched-itemp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 7)
       (stringp (fn-sched-item-work-id x))
       (fn-sched-classp (fn-sched-item-class x))
       (natp (fn-sched-item-size x))
       (natp (fn-sched-item-seq x))
       (natp (fn-sched-item-passes x))
       (booleanp (fn-sched-item-agedp x))
       (booleanp (fn-sched-item-expiredp x))))

(defun fn-sched-item-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-sched-itemp (car xs)) (fn-sched-item-listp (cdr xs)))
    (null xs)))

(defun fn-sched-string-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (stringp (car xs)) (fn-sched-string-listp (cdr xs)))
    (null xs)))

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

(defun fn-sched-statep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 10)
       (equal (car x) :fn-sched-state)
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

(defun fn-sched-next-aged (ss wf selected-id)
  (declare (xargs :guard t))
  (let* ((limit (fn-sched-aging-limit (fn-sched-conf ss)))
         (advanced (fn-sched-aged-advance (fn-sched-aged ss)
                                          (fn-sched-queue ss) wf))
         (rest (if (and (consp advanced) (equal (car advanced) selected-id))
                   (cdr advanced)
                 advanced)))
    (append rest (fn-sched-promotions (fn-sched-queue ss) wf selected-id
                                      limit))))

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

(defun fn-sched-decision-protected (values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-sched-decision-recordp values))
      :bad
    (let ((payload (fn-frame-fields-octets *fn-sched-decision-spec* values)))
      (if (not (<= (len payload) *fn-sched-max-payload*))
          :bad
        (fn-frame-protected *fn-sched-magic* *fn-frame-version*
                            *fn-sched-kind* payload)))))

(verify-guards fn-sched-decision-protected)

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

(verify-guards fn-sched-decision-decode)

; -----------------------------------------------------------------------------
; Results

(defun fn-sched-result (ss wf effects)
  (declare (xargs :guard t))
  (list ss wf effects))

(defun fn-sched-result-ss (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-sched-result-wf (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-sched-result-effects (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))

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
  (declare (xargs :guard t))
  (let ((limit (fn-sched-aging-limit (fn-sched-conf ss))))
    (fn-sched-state
     (fn-sched-generation ss) (fn-sched-conf ss)
     (fn-sched-bump-queue (fn-sched-queue ss) wf nil limit)
     (fn-sched-next-aged ss wf nil)
     (fn-sched-open-contact ss) (fn-sched-retries ss)
     (+ 1 (nfix (fn-sched-tick ss))) (fn-sched-next-tx ss)
     (fn-sched-decisions ss))))

(defun fn-sched-take (ss wf selected)
  (declare (xargs :guard t))
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

(defun fn-sched-trace (ss wf events)
  (declare (xargs :guard t))
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

; N consecutive admissible contact ticks on which the store accepts.
(defun fn-sched-contact-runp (ss wf n attempt-id)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp n)
      t
    (and (fn-sched-admissiblep ss)
         (fn-sched-drive-okp ss wf attempt-id)
         (let ((r (fn-sched-tick-step ss wf attempt-id)))
           (fn-sched-contact-runp (fn-sched-result-ss r)
                                  (fn-sched-result-wf r) (- n 1) attempt-id)))))

; WORK-ID is eligible at each of N consecutive ticks.
(defun fn-sched-eligible-runp (ss wf n attempt-id work-id)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp n)
      t
    (and (fn-sched-eligible-idp work-id ss wf)
         (let ((r (fn-sched-tick-step ss wf attempt-id)))
           (fn-sched-eligible-runp (fn-sched-result-ss r)
                                   (fn-sched-result-wf r) (- n 1) attempt-id
                                   work-id)))))

; WORK-ID receives a submit within N ticks.
(defun fn-sched-selected-withinp (ss wf n attempt-id work-id)
  (declare (xargs :guard t :measure (nfix n)))
  (if (zp n)
      nil
    (let ((r (fn-sched-tick-step ss wf attempt-id)))
      (if (fn-sched-submit-for-idp work-id (fn-sched-result-effects r))
          t
        (fn-sched-selected-withinp (fn-sched-result-ss r)
                                   (fn-sched-result-wf r) (- n 1) attempt-id
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
  (declare (xargs :guard t))
  (if (consp events)
      (let ((r (fn-sched-unfair-step ss wf (car events))))
        (fn-sched-unfair-trace (fn-sched-result-ss r) (fn-sched-result-wf r)
                               (cdr events)))
    (fn-sched-result ss wf nil)))

; Whether any tick of a trace emitted a submit for WORK-ID, under each policy.
; The starvation counterexample is the pair of answers on one trace.
(defun fn-sched-submitted-in-trace (ss wf events work-id)
  (declare (xargs :guard t))
  (if (consp events)
      (let ((r (fn-sched-step ss wf (car events))))
        (or (fn-sched-submit-for-idp work-id (fn-sched-result-effects r))
            (fn-sched-submitted-in-trace (fn-sched-result-ss r)
                                         (fn-sched-result-wf r) (cdr events)
                                         work-id)))
    nil))

(defun fn-sched-unfair-submitted-in-trace (ss wf events work-id)
  (declare (xargs :guard t))
  (if (consp events)
      (let ((r (fn-sched-unfair-step ss wf (car events))))
        (or (fn-sched-submit-for-idp work-id (fn-sched-result-effects r))
            (fn-sched-unfair-submitted-in-trace
             (fn-sched-result-ss r) (fn-sched-result-wf r) (cdr events)
             work-id)))
    nil))
