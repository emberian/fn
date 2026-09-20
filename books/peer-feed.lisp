; fn: the outbound feed machine (specs/peering.md sec. 3).
;
; One feed state per configured outbound peer.  The queue holds Message-IDs
; and an offer state; no article bytes live here (the article is rendered from
; the store when it is offered).  Every decision the feed takes is journaled
; in the FNFD record family below BEFORE the effect it authorizes, and
; `fn-feed-replay' folds those records back into a feed state.  That fold and
; the restart it feeds are what make the offer exactly-once per peer: the
; decision to transfer is journaled once per attempt, an attempt id is never
; re-run, and an attempt whose outcome the crash lost is resolved by a fresh
; CHECK/IHAVE offer -- never by a blind TAKETHIS -- whose 435/438 is the
; peer's own history answering for us.
;
; Two deliberate differences from the design text of specs/peering.md sec. 3.1,
; both recorded in that file's status section:
;
;   * `fn-feed-make' carries a `limits' record (max-queue, backoff base, retry
;     bound, streaming) copied from the peer record's outbound half at open,
;     instead of reading `fn-cfg-peer-*' here.  The feed book therefore does
;     not include `peer-config', its recognizer is self-contained, and the
;     owner is the one place that reads a peer record.
;   * peer names and Message-IDs are `fn-frame-textp' octets throughout, which
;     is the transit vocabulary of `books/peer-inbound.lisp' and exactly the
;     `:text' field type of the journal records, so no string conversion
;     happens anywhere between the state and the record.  The scheduler's
;     contact carries the peer as a string; binding the two is the owner's
;     obligation and is stated in the handoff, not proved here.
;
; The in-flight rule is the strong one: AT MOST ONE entry of a feed is
; `(:offered n)' or `(:sent n)'.  RFC 4644 permits a streaming window; fn does
; not take it yet, and `fn-feed-at-most-one-in-flight' is the conjunct that
; makes exactly-once an argument about one entry rather than a window.

(in-package "ACL2")
(include-book "scheduler")
(include-book "frame")
; `fn-feed-record-decode-of-encode' rests on frame's own round trip.
(include-book "frame-invariants")
(local (include-book "arithmetic/top" :dir :system))

; Local vocabulary re-enable (docs/proof-style.md sec. 2), copied from
; `books/anchor-record.lisp': the small frame predicates and the spec
; machinery, never the field grammar and never the two codec entry points.
(local (in-theory (enable fn-frame-fields-vocabulary
                          fn-frame-octet-vocabulary
                          (:d fn-frame-magicp) (:d fn-frame-spec-for)
                          (:d fn-frame-specp) (:d fn-frame-spec-listp)
                          (:d fn-frame-digestp))))

; -----------------------------------------------------------------------------
; Closed enumerations
;
; `*fn-feed-outcome-codes*' is the response vocabulary of RFC 3977 sec. 6.3.2
; and RFC 4644 sec. 2.4/2.5 that the feed journals.  `*fn-feed-drop-reasons*'
; is closed so that no entry can leave the queue without a reason a reader of
; the journal can name.

(defconst *fn-feed-outcome-codes* '(235 239 435 438 437 439 431 436 400))
(defconst *fn-feed-accepted-codes* '(235 239))
(defconst *fn-feed-drop-reasons* '(:retry-bound :peer-removed :operator))

; The backoff ceiling: one hour in milliseconds.  A base above it is clamped,
; so `fn-feed-backoff-delay' is bounded however a peer record is configured.
(defconst *fn-feed-max-backoff* 3600000)

; -----------------------------------------------------------------------------
; Message-IDs and peer names, as carried here
;
; `fn-frame-textp' is a bounded, non-empty, UTF-8 octet list.  Using it as the
; recognizer means the journal codec's field guard is discharged from the feed
; recognizer with no conversion and no second notion of a Message-ID.

(defun fn-feed-namep (x)
  (declare (xargs :guard t))
  (fn-frame-textp x))

(defun fn-feed-name-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs) (null xs)
      (and (fn-feed-namep (car xs)) (fn-feed-name-listp (cdr xs)))))

; -----------------------------------------------------------------------------
; The offer state of a queue entry
;
; :queued | (:offered n) | (:sent n) | :done | (:dropped reason).
; These five glue predicates are the only place a state's spelling is opened;
; every rule above them is stated in this vocabulary (docs/proof-style.md
; sec. 8: glue predicates in accessor vocabulary may leave the book enabled).

(defun fn-feed-offeredp (s)
  (declare (xargs :guard t))
  (and (consp s) (equal (car s) :offered) (natp (fn-bp-nth 1 s))
       (true-listp s) (equal (len s) 2)))

(defun fn-feed-sentp (s)
  (declare (xargs :guard t))
  (and (consp s) (equal (car s) :sent) (natp (fn-bp-nth 1 s))
       (true-listp s) (equal (len s) 2)))

(defun fn-feed-droppedp (s)
  (declare (xargs :guard t))
  (and (consp s) (equal (car s) :dropped)
       (member-equal (fn-bp-nth 1 s) *fn-feed-drop-reasons*)
       (true-listp s) (equal (len s) 2)))

(defun fn-feed-state-attempt (s)
  (declare (xargs :guard t))
  (nfix (fn-bp-nth 1 s)))

(defun fn-feed-state-reason (s)
  (declare (xargs :guard t))
  (fn-bp-nth 1 s))

(defun fn-feed-state-inflightp (s)
  (declare (xargs :guard t))
  (or (fn-feed-offeredp s) (fn-feed-sentp s)))

(defun fn-feed-state-okp (s)
  (declare (xargs :guard t))
  (or (equal s :queued)
      (equal s :done)
      (fn-feed-offeredp s)
      (fn-feed-sentp s)
      (fn-feed-droppedp s)))

(defun fn-feed-offered (attempt)
  (declare (xargs :guard t))
  (list :offered (nfix attempt)))

(defun fn-feed-sent (attempt)
  (declare (xargs :guard t))
  (list :sent (nfix attempt)))

(defun fn-feed-dropped (reason)
  (declare (xargs :guard t))
  (list :dropped (if (member-equal reason *fn-feed-drop-reasons*)
                     reason
                     :operator)))

; -----------------------------------------------------------------------------
; The queue entry, an opaque record (docs/proof-style.md sec. 1)

(defun fn-feed-entry-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))

(defun fn-feed-entry (msgid st attempts tick)
  (declare (xargs :guard t))
  (list msgid st attempts tick))

(defun fn-feed-entry-msgid (x)
  (declare (xargs :guard t))
  (fn-bp-nth 0 x))
(defun fn-feed-entry-state (x)
  (declare (xargs :guard t))
  (fn-bp-nth 1 x))
(defun fn-feed-entry-attempts (x)
  (declare (xargs :guard t))
  (fn-bp-nth 2 x))
(defun fn-feed-entry-tick (x)
  (declare (xargs :guard t))
  (fn-bp-nth 3 x))

(defthm fn-feed-entry-shapep-of-fn-feed-entry
  (fn-feed-entry-shapep (fn-feed-entry msgid st attempts tick)))
(defthm fn-feed-entry-msgid-of-fn-feed-entry
  (equal (fn-feed-entry-msgid (fn-feed-entry msgid st attempts tick))
         msgid))
(defthm fn-feed-entry-state-of-fn-feed-entry
  (equal (fn-feed-entry-state (fn-feed-entry msgid st attempts tick))
         st))
(defthm fn-feed-entry-attempts-of-fn-feed-entry
  (equal (fn-feed-entry-attempts (fn-feed-entry msgid st attempts tick))
         attempts))
(defthm fn-feed-entry-tick-of-fn-feed-entry
  (equal (fn-feed-entry-tick (fn-feed-entry msgid st attempts tick))
         tick))
(defthm fn-feed-entry-shapep-forward-shape
  (implies (fn-feed-entry-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-feed-entry-accessors-forward-consp
  (and (implies (fn-feed-entry-msgid x) (consp x))
       (implies (fn-feed-entry-state x) (consp x))
       (implies (fn-feed-entry-attempts x) (consp x))
       (implies (fn-feed-entry-tick x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-feed-entry-msgid x) (consp x))
                  :trigger-terms ((fn-feed-entry-msgid x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-entry-state x) (consp x))
                  :trigger-terms ((fn-feed-entry-state x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-entry-attempts x) (consp x))
                  :trigger-terms ((fn-feed-entry-attempts x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-entry-tick x) (consp x))
                  :trigger-terms ((fn-feed-entry-tick x)))))

(in-theory (disable (:d fn-feed-entry-shapep) (:d fn-feed-entry)
                    (:d fn-feed-entry-msgid) (:d fn-feed-entry-state)
                    (:d fn-feed-entry-attempts) (:d fn-feed-entry-tick)))

(defun fn-feed-entryp (x)
  (declare (xargs :guard t))
  (and (fn-feed-entry-shapep x)
       (fn-feed-namep (fn-feed-entry-msgid x))
       (fn-feed-state-okp (fn-feed-entry-state x))
       (natp (fn-feed-entry-attempts x))
       (natp (fn-feed-entry-tick x))))

(defthm fn-feed-entryp-forward-shape
  (implies (fn-feed-entryp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

; -----------------------------------------------------------------------------
; Queue vocabulary (list-recursive: this is the induction vocabulary and it
; leaves the book enabled, docs/proof-style.md sec. 8)

(defun fn-feed-entry-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs) (null xs)
      (and (fn-feed-entryp (car xs)) (fn-feed-entry-listp (cdr xs)))))

(defthm fn-feed-entry-listp-forward-true-listp
  (implies (fn-feed-entry-listp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defun fn-feed-find (msgid xs)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
      (if (equal (fn-feed-entry-msgid (car xs)) msgid)
          (car xs)
          (fn-feed-find msgid (cdr xs)))))

(defun fn-feed-state-of (msgid xs)
  (declare (xargs :guard t))
  (fn-feed-entry-state (fn-feed-find msgid xs)))

(defun fn-feed-msgids (xs)
  (declare (xargs :guard t))
  (if (atom xs) nil (cons (fn-feed-entry-msgid (car xs))
                          (fn-feed-msgids (cdr xs)))))

(defun fn-feed-distinctp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      t
      (and (not (member-equal (fn-feed-entry-msgid (car xs))
                              (fn-feed-msgids (cdr xs))))
           (fn-feed-distinctp (cdr xs)))))

(defun fn-feed-inflight-count (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      0
      (+ (if (fn-feed-state-inflightp (fn-feed-entry-state (car xs))) 1 0)
         (fn-feed-inflight-count (cdr xs)))))

(defun fn-feed-attempts-belowp (xs n)
  (declare (xargs :guard t))
  (if (atom xs)
      t
      (and (or (not (fn-feed-state-inflightp (fn-feed-entry-state (car xs))))
               (< (fn-feed-state-attempt (fn-feed-entry-state (car xs)))
                  (nfix n)))
           (fn-feed-attempts-belowp (cdr xs) n))))

; The head queued entry: the FIFO discipline of specs/peering.md sec. 3.2.
(defun fn-feed-head-queued (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
      (if (equal (fn-feed-entry-state (car xs)) :queued)
          (fn-feed-entry-msgid (car xs))
          (fn-feed-head-queued (cdr xs)))))

(defun fn-feed-queue-set-state (xs msgid st)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
      (if (equal (fn-feed-entry-msgid (car xs)) msgid)
          (cons (fn-feed-entry (fn-feed-entry-msgid (car xs)) st
                               (fn-feed-entry-attempts (car xs))
                               (fn-feed-entry-tick (car xs)))
                (cdr xs))
          (cons (car xs) (fn-feed-queue-set-state (cdr xs) msgid st)))))

; Requeue after a 431/436 or a connection loss: back to :queued, one more
; attempt counted, the tick remembered.
(defun fn-feed-queue-requeue (xs msgid tick)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
      (if (equal (fn-feed-entry-msgid (car xs)) msgid)
          (cons (fn-feed-entry (fn-feed-entry-msgid (car xs)) :queued
                               (+ 1 (nfix (fn-feed-entry-attempts (car xs))))
                               (nfix tick))
                (cdr xs))
          (cons (car xs) (fn-feed-queue-requeue (cdr xs) msgid tick)))))

; Every in-flight entry back to :queued with one more attempt: the 400 / lost
; connection case.  Nothing is dropped.
(defun fn-feed-queue-requeue-inflight (xs tick)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
      (cons (if (fn-feed-state-inflightp (fn-feed-entry-state (car xs)))
                (fn-feed-entry (fn-feed-entry-msgid (car xs)) :queued
                               (+ 1 (nfix (fn-feed-entry-attempts (car xs))))
                               (nfix tick))
                (car xs))
            (fn-feed-queue-requeue-inflight (cdr xs) tick))))

; `fn-feed-settle' is the RELATION between a live feed and its replay: it maps
; (:offered n)/(:sent n) to :queued and forgets the attempt id.  It is not a
; second implementation of restart; `fn-feed-restart-is-settle-with-no-conn'
; is the equation that says so.
(defun fn-feed-queue-settle (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
      (cons (if (fn-feed-state-inflightp (fn-feed-entry-state (car xs)))
                (fn-feed-entry (fn-feed-entry-msgid (car xs)) :queued
                               (fn-feed-entry-attempts (car xs))
                               (fn-feed-entry-tick (car xs)))
                (car xs))
            (fn-feed-queue-settle (cdr xs)))))

; -----------------------------------------------------------------------------
; The per-peer limits, copied from the peer record's outbound half at open

(defun fn-feed-limits-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))

(defun fn-feed-limits (max-queue backoff retry-bound streamingp)
  (declare (xargs :guard t))
  (list max-queue backoff retry-bound streamingp))

(defun fn-feed-max-queue (x)
  (declare (xargs :guard t))
  (fn-bp-nth 0 x))
(defun fn-feed-backoff-base (x)
  (declare (xargs :guard t))
  (fn-bp-nth 1 x))
(defun fn-feed-retry-bound (x)
  (declare (xargs :guard t))
  (fn-bp-nth 2 x))
(defun fn-feed-streamingp (x)
  (declare (xargs :guard t))
  (fn-bp-nth 3 x))

(defthm fn-feed-limits-shapep-of-fn-feed-limits
  (fn-feed-limits-shapep (fn-feed-limits q b r s)))
(defthm fn-feed-max-queue-of-fn-feed-limits
  (equal (fn-feed-max-queue (fn-feed-limits q b r s)) q))
(defthm fn-feed-backoff-base-of-fn-feed-limits
  (equal (fn-feed-backoff-base (fn-feed-limits q b r s)) b))
(defthm fn-feed-retry-bound-of-fn-feed-limits
  (equal (fn-feed-retry-bound (fn-feed-limits q b r s)) r))
(defthm fn-feed-streamingp-of-fn-feed-limits
  (equal (fn-feed-streamingp (fn-feed-limits q b r s)) s))
(defthm fn-feed-limits-shapep-forward-shape
  (implies (fn-feed-limits-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-feed-limits-accessors-forward-consp
  (and (implies (fn-feed-max-queue x) (consp x))
       (implies (fn-feed-backoff-base x) (consp x))
       (implies (fn-feed-retry-bound x) (consp x))
       (implies (fn-feed-streamingp x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-feed-max-queue x) (consp x))
                  :trigger-terms ((fn-feed-max-queue x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-backoff-base x) (consp x))
                  :trigger-terms ((fn-feed-backoff-base x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-retry-bound x) (consp x))
                  :trigger-terms ((fn-feed-retry-bound x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-streamingp x) (consp x))
                  :trigger-terms ((fn-feed-streamingp x)))))

(in-theory (disable (:d fn-feed-limits-shapep) (:d fn-feed-limits)
                    (:d fn-feed-max-queue) (:d fn-feed-backoff-base)
                    (:d fn-feed-retry-bound) (:d fn-feed-streamingp)))

(defun fn-feed-limitsp (x)
  (declare (xargs :guard t))
  (and (fn-feed-limits-shapep x)
       (posp (fn-feed-max-queue x))
       (natp (fn-feed-backoff-base x))
       (posp (fn-feed-retry-bound x))
       (booleanp (fn-feed-streamingp x))))

(defthm fn-feed-limitsp-forward-shape
  (implies (fn-feed-limitsp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

; Exponential backoff with a ceiling.  Stated recursively rather than with
; `expt' so that monotonicity is one induction and the value is bounded
; however the peer record is configured.
(defun fn-feed-backoff-delay (base attempts)
  (declare (xargs :guard t :measure (nfix attempts)))
  ; `zp' has `(natp x)' for its guard, so the counter is nfixed at the test
  ; as well as at the recursive call: the guard conjecture is then
  ; unconditional and the measure is the same nat.
  (if (zp (nfix attempts))
      (if (<= *fn-feed-max-backoff* (nfix base)) *fn-feed-max-backoff*
          (nfix base))
      (let ((d (nfix (fn-feed-backoff-delay base (- (nfix attempts) 1)))))
        (if (<= *fn-feed-max-backoff* (* 2 d)) *fn-feed-max-backoff*
            (* 2 d)))))

; -----------------------------------------------------------------------------
; The feed, an opaque record

(defun fn-feed-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7)))

(defun fn-feed-make (peer limits queue contact backoff-until conn next-attempt)
  (declare (xargs :guard t))
  (list peer limits queue contact backoff-until conn next-attempt))

(defun fn-feed-peer (x)
  (declare (xargs :guard t))
  (fn-bp-nth 0 x))
(defun fn-feed-limits-of (x)
  (declare (xargs :guard t))
  (fn-bp-nth 1 x))
(defun fn-feed-queue (x)
  (declare (xargs :guard t))
  (fn-bp-nth 2 x))
(defun fn-feed-contact (x)
  (declare (xargs :guard t))
  (fn-bp-nth 3 x))
(defun fn-feed-backoff-until (x)
  (declare (xargs :guard t))
  (fn-bp-nth 4 x))
(defun fn-feed-conn (x)
  (declare (xargs :guard t))
  (fn-bp-nth 5 x))
(defun fn-feed-next-attempt (x)
  (declare (xargs :guard t))
  (fn-bp-nth 6 x))

(defthm fn-feed-shapep-of-fn-feed-make
  (fn-feed-shapep (fn-feed-make p l q c b n a)))
(defthm fn-feed-peer-of-fn-feed-make
  (equal (fn-feed-peer (fn-feed-make p l q c b n a)) p))
(defthm fn-feed-limits-of-of-fn-feed-make
  (equal (fn-feed-limits-of (fn-feed-make p l q c b n a)) l))
(defthm fn-feed-queue-of-fn-feed-make
  (equal (fn-feed-queue (fn-feed-make p l q c b n a)) q))
(defthm fn-feed-contact-of-fn-feed-make
  (equal (fn-feed-contact (fn-feed-make p l q c b n a)) c))
(defthm fn-feed-backoff-until-of-fn-feed-make
  (equal (fn-feed-backoff-until (fn-feed-make p l q c b n a)) b))
(defthm fn-feed-conn-of-fn-feed-make
  (equal (fn-feed-conn (fn-feed-make p l q c b n a)) n))
(defthm fn-feed-next-attempt-of-fn-feed-make
  (equal (fn-feed-next-attempt (fn-feed-make p l q c b n a)) a))
(defthm fn-feed-shapep-forward-shape
  (implies (fn-feed-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-feed-accessors-forward-consp
  (and (implies (fn-feed-peer x) (consp x))
       (implies (fn-feed-limits-of x) (consp x))
       (implies (fn-feed-queue x) (consp x))
       (implies (fn-feed-contact x) (consp x))
       (implies (fn-feed-backoff-until x) (consp x))
       (implies (fn-feed-conn x) (consp x))
       (implies (fn-feed-next-attempt x) (consp x)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-feed-peer x) (consp x))
                  :trigger-terms ((fn-feed-peer x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-limits-of x) (consp x))
                  :trigger-terms ((fn-feed-limits-of x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-queue x) (consp x))
                  :trigger-terms ((fn-feed-queue x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-contact x) (consp x))
                  :trigger-terms ((fn-feed-contact x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-backoff-until x) (consp x))
                  :trigger-terms ((fn-feed-backoff-until x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-conn x) (consp x))
                  :trigger-terms ((fn-feed-conn x)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-next-attempt x) (consp x))
                  :trigger-terms ((fn-feed-next-attempt x)))))

(in-theory (disable (:d fn-feed-shapep) (:d fn-feed-make)
                    (:d fn-feed-peer) (:d fn-feed-limits-of)
                    (:d fn-feed-queue) (:d fn-feed-contact)
                    (:d fn-feed-backoff-until) (:d fn-feed-conn)
                    (:d fn-feed-next-attempt)))

(defun fn-feedp (f)
  (declare (xargs :guard t))
  (and (fn-feed-shapep f)
       (fn-feed-namep (fn-feed-peer f))
       (fn-feed-limitsp (fn-feed-limits-of f))
       (fn-feed-entry-listp (fn-feed-queue f))
       (fn-feed-distinctp (fn-feed-queue f))
       (<= (len (fn-feed-queue f))
           (fn-feed-max-queue (fn-feed-limits-of f)))
       (<= (fn-feed-inflight-count (fn-feed-queue f)) 1)
       (fn-feed-attempts-belowp (fn-feed-queue f) (fn-feed-next-attempt f))
       (or (null (fn-feed-contact f)) (fn-sched-contactp (fn-feed-contact f)))
       (natp (fn-feed-backoff-until f))
       (or (null (fn-feed-conn f)) (natp (fn-feed-conn f)))
       (posp (fn-feed-next-attempt f))))

(defthm fn-feedp-forward-shape
  (implies (fn-feedp f) (and (consp f) (true-listp f)))
  :rule-classes :forward-chaining)

(defthm fn-feedp-forward-components
  (implies (fn-feedp f)
           (and (fn-feed-entry-listp (fn-feed-queue f))
                (fn-feed-limitsp (fn-feed-limits-of f))))
  :rule-classes :forward-chaining)

(defun fn-feed-open (peer limits contact conn)
  (declare (xargs :guard t))
  (fn-feed-make peer limits nil contact 0 conn 1))

; Field updates.  Each rebuilds the record, so nothing below opens it.
(defun fn-feed-with-queue (f queue)
  (declare (xargs :guard t))
  (fn-feed-make (fn-feed-peer f) (fn-feed-limits-of f) queue
                (fn-feed-contact f) (fn-feed-backoff-until f)
                (fn-feed-conn f) (fn-feed-next-attempt f)))

(defun fn-feed-with-conn (f conn)
  (declare (xargs :guard t))
  (fn-feed-make (fn-feed-peer f) (fn-feed-limits-of f) (fn-feed-queue f)
                (fn-feed-contact f) (fn-feed-backoff-until f) conn
                (fn-feed-next-attempt f)))

(defun fn-feed-with-contact (f contact)
  (declare (xargs :guard t))
  (fn-feed-make (fn-feed-peer f) (fn-feed-limits-of f) (fn-feed-queue f)
                contact (fn-feed-backoff-until f) (fn-feed-conn f)
                (fn-feed-next-attempt f)))

; -----------------------------------------------------------------------------
; Transitions (specs/peering.md sec. 3.2)

; Enqueue on a durable local acceptance.  Refused -- f unchanged -- when the
; Message-ID is already queued or the peer's queue is full.  Whether the
; article is IN SCOPE for this peer is the caller's decision
; (`fn-feed-offerablep' of the design, which reads the peer record and the
; Path): the feed never re-derives it.
(defun fn-feed-enqueue (f msgid tick)
  (declare (xargs :guard t))
  (if (or (not (fn-feedp f))
          (not (fn-feed-namep msgid))
          (consp (fn-feed-find msgid (fn-feed-queue f)))
          (<= (fn-feed-max-queue (fn-feed-limits-of f))
              (len (fn-feed-queue f))))
      f
      (fn-feed-with-queue
       f (append (fn-feed-queue f)
                 (list (fn-feed-entry msgid :queued 0 (nfix tick)))))))

; Select: the head :queued entry, when the contact holds this observation, the
; connection is up, the backoff has elapsed and nothing is in flight.
(defun fn-feed-selection (f obs)
  (declare (xargs :guard t))
  (if (and (fn-feedp f)
           (fn-clock-observationp obs)
           (fn-sched-contact-holdsp (fn-feed-contact f) obs)
           (natp (fn-feed-conn f))
           (<= (nfix (fn-feed-backoff-until f))
               (nfix (fn-clock-monotonic obs)))
           (equal (fn-feed-inflight-count (fn-feed-queue f)) 0))
      (fn-feed-head-queued (fn-feed-queue f))
      nil))

; The offer command line.  CHECK for a streaming peer (RFC 4644 sec. 2.4),
; IHAVE otherwise (RFC 3977 sec. 6.3.2); TAKETHIS (RFC 4644 sec. 2.5) only
; after a 238.
(defconst *fn-feed-check-prefix* '(67 72 69 67 75 32))              ; "CHECK "
(defconst *fn-feed-ihave-prefix* '(73 72 65 86 69 32))              ; "IHAVE "
(defconst *fn-feed-takethis-prefix* '(84 65 75 69 84 72 73 83 32))  ; "TAKETHIS "
(defconst *fn-feed-crlf* '(13 10))

; `append' wants a true list on its left, and a Message-ID is only a true list
; when it is `fn-feed-namep'.  The fix is in the total builder, not a guard on
; the three callers: a malformed Message-ID renders as the bare command line,
; which no peer answers, rather than making the renderer partial.
(defun fn-feed-line (prefix msgid)
  (declare (xargs :guard (true-listp prefix)))
  (append prefix
          (append (if (true-listp msgid) msgid nil) *fn-feed-crlf*)))

(defun fn-feed-check-line (msgid)
  (declare (xargs :guard t))
  (fn-feed-line *fn-feed-check-prefix* msgid))
(defun fn-feed-ihave-line (msgid)
  (declare (xargs :guard t))
  (fn-feed-line *fn-feed-ihave-prefix* msgid))
(defun fn-feed-takethis-line (msgid)
  (declare (xargs :guard t))
  (fn-feed-line *fn-feed-takethis-prefix* msgid))

(defun fn-feed-offer-line (msgid streamingp)
  (declare (xargs :guard t))
  (if streamingp (fn-feed-check-line msgid) (fn-feed-ihave-line msgid)))

(defun fn-feed-check-linep (octets msgid)
  (declare (xargs :guard t))
  (equal octets (fn-feed-check-line msgid)))
(defun fn-feed-ihave-linep (octets msgid)
  (declare (xargs :guard t))
  (equal octets (fn-feed-ihave-line msgid)))
(defun fn-feed-takethis-linep (octets msgid)
  (declare (xargs :guard t))
  (equal octets (fn-feed-takethis-line msgid)))

; The predicate K5 is stated over: an octet string that offers this
; Message-ID, in either of the two offer spellings.
(defun fn-feed-command-offersp (octets msgid)
  (declare (xargs :guard t))
  (or (fn-feed-check-linep octets msgid)
      (fn-feed-ihave-linep octets msgid)))

; Drive: the offer.  The journal record is written first by the host; this is
; the state change and the effect it authorizes.
(defun fn-feed-offer (f msgid)
  (declare (xargs :guard t))
  (if (or (not (fn-feedp f))
          (not (equal (fn-feed-state-of msgid (fn-feed-queue f)) :queued))
          (not (natp (fn-feed-conn f))))
      (mv f nil)
      (let ((attempt (fn-feed-next-attempt f)))
        (mv (fn-feed-make (fn-feed-peer f) (fn-feed-limits-of f)
                          (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                                   (fn-feed-offered attempt))
                          (fn-feed-contact f) (fn-feed-backoff-until f)
                          (fn-feed-conn f) (+ 1 attempt))
            (list (list :command (fn-feed-conn f)
                        (fn-feed-offer-line
                         msgid
                         (fn-feed-streamingp (fn-feed-limits-of f)))))))))

; 335 (IHAVE) or 238 (CHECK): send the article.  The attempt id is the one the
; offer allocated; no new attempt is opened.
(defun fn-feed-send (f msgid article)
  (declare (xargs :guard t))
  (if (or (not (fn-feedp f))
          (not (fn-feed-offeredp (fn-feed-state-of msgid (fn-feed-queue f))))
          (not (natp (fn-feed-conn f))))
      (mv f nil)
      (let ((attempt (fn-feed-state-attempt
                      (fn-feed-state-of msgid (fn-feed-queue f)))))
        (mv (fn-feed-with-queue
             f (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                        (fn-feed-sent attempt)))
            (list (list :command (fn-feed-conn f)
                        (if (fn-feed-streamingp (fn-feed-limits-of f))
                            (append (fn-feed-takethis-line msgid) article)
                            article)))))))

; 235/239 (accepted), 435/438 (the peer has it), 437/439 (the peer refused it):
; the entry is finished either way.  Which of the three it was is in the
; outcome record, never lost.
(defun fn-feed-done (f msgid)
  (declare (xargs :guard t))
  (if (or (not (fn-feedp f))
          (not (fn-feed-state-inflightp
                (fn-feed-state-of msgid (fn-feed-queue f)))))
      f
      (fn-feed-with-queue
       f (fn-feed-queue-set-state (fn-feed-queue f) msgid :done))))

(defun fn-feed-with-backoff (f until)
  (declare (xargs :guard t))
  (fn-feed-make (fn-feed-peer f) (fn-feed-limits-of f) (fn-feed-queue f)
                (fn-feed-contact f)
                (if (<= (nfix (fn-feed-backoff-until f)) (nfix until))
                    (nfix until)
                    (nfix (fn-feed-backoff-until f)))
                (fn-feed-conn f) (fn-feed-next-attempt f)))

; 431/436: retry later.  attempts + 1, backoff-until pushed out exponentially,
; the entry queued again.  `fn-feed-with-backoff' never lowers the deadline,
; which is what makes the backoff monotone.
(defun fn-feed-back-off (f msgid obs)
  (declare (xargs :guard t))
  (if (or (not (fn-feedp f))
          (not (fn-feed-state-inflightp
                (fn-feed-state-of msgid (fn-feed-queue f)))))
      f
      (let* ((entry (fn-feed-find msgid (fn-feed-queue f)))
             (attempts (nfix (fn-feed-entry-attempts entry)))
             (now (nfix (fn-clock-monotonic obs)))
             (delay (fn-feed-backoff-delay
                     (fn-feed-backoff-base (fn-feed-limits-of f)) attempts)))
        (fn-feed-with-backoff
         (fn-feed-with-queue
          f (fn-feed-queue-requeue (fn-feed-queue f) msgid now))
         (+ now delay)))))

; 400 or any code outside the map: the connection is lost.  Every in-flight
; entry returns to :queued with one more attempt; nothing is dropped and the
; connection is forgotten so that the next selection waits for a reopen.
(defun fn-feed-lost (f obs)
  (declare (xargs :guard t))
  (if (not (fn-feedp f))
      f
      (let* ((now (nfix (fn-clock-monotonic obs)))
             (delay (fn-feed-backoff-delay
                     (fn-feed-backoff-base (fn-feed-limits-of f)) 0)))
        (fn-feed-with-backoff
         (fn-feed-with-conn
          (fn-feed-with-queue
           f (fn-feed-queue-requeue-inflight (fn-feed-queue f) now))
          nil)
         (+ now delay)))))

; Give up: at the retry bound the entry is dropped WITH ITS REASON.  A dropped
; entry is never re-offered automatically; the CLI reports it as refused and an
; operator can re-feed.
(defun fn-feed-give-up (f msgid reason)
  (declare (xargs :guard t))
  (if (or (not (fn-feedp f))
          (not (consp (fn-feed-find msgid (fn-feed-queue f))))
          (fn-feed-droppedp (fn-feed-state-of msgid (fn-feed-queue f)))
          (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done))
      f
      (fn-feed-with-queue
       f (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                  (fn-feed-dropped reason)))))

(defun fn-feed-retry-exhaustedp (f msgid)
  (declare (xargs :guard t))
  (and (consp (fn-feed-find msgid (fn-feed-queue f)))
       (<= (nfix (fn-feed-retry-bound (fn-feed-limits-of f)))
           (nfix (fn-feed-entry-attempts
                  (fn-feed-find msgid (fn-feed-queue f)))))))

; -----------------------------------------------------------------------------
; The response and the code map (specs/peering.md sec. 3.2)

(defun fn-feed-response (code msgid)
  (declare (xargs :guard t))
  (list code msgid))
(defun fn-feed-response-code (r)
  (declare (xargs :guard t))
  (fn-bp-nth 0 r))
(defun fn-feed-response-msgid (r)
  (declare (xargs :guard t))
  (fn-bp-nth 1 r))

(defun fn-feed-responsep (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 2)
       (natp (fn-feed-response-code r))
       (fn-feed-namep (fn-feed-response-msgid r))))

; Confirmed against a real INN 2.7.4 on hbox
; (planning/evidence/inn-lab-f4e8272-2026-09-20.md): IHAVE 335 then 235,
; 435 duplicate, 436 transient, 437 rejected permanently (a Path already
; naming the peer yields 437); CHECK 238/431/438; TAKETHIS 239/439;
; MODE STREAM 203.  So 435/437/438/439 are FINAL here -- `fn-feed-done', never
; re-offered -- 431/436 back off, and 400, 480, 503 and every unknown code
; fall through to `fn-feed-lost', which requeues the in-flight entry so the
; reconnect resolves it by CHECK.
;
; The response the peer sent names a Message-ID for CHECK/TAKETHIS; for IHAVE
; the reply has no Message-ID and the host supplies the in-flight one, which
; is unambiguous because at most one entry is in flight.
(defun fn-feed-observe (f response article obs)
  (declare (xargs :guard t))
  (if (not (fn-feedp f))
      (mv f nil)
      (let ((code (fn-feed-response-code response))
            (msgid (fn-feed-response-msgid response)))
        (cond ((member-equal code '(335 238)) (fn-feed-send f msgid article))
              ((member-equal code '(235 239 435 438 437 439))
               (mv (fn-feed-done f msgid) nil))
              ((member-equal code '(431 436))
               (let ((g (fn-feed-back-off f msgid obs)))
                 (mv (if (fn-feed-retry-exhaustedp g msgid)
                         (fn-feed-give-up g msgid :retry-bound)
                         g)
                     nil)))
              (t (mv (fn-feed-lost f obs) nil))))))

; Restart: on open, before any offer.  Every in-flight entry is fenced back to
; :queued with its attempt RETIRED, and the connection is forgotten.  The next
; command for such an entry is therefore an offer -- a CHECK or an IHAVE --
; whose 435/438 is the peer's own history absorbing the one retransmission a
; lost reply can cause.  Never a blind TAKETHIS.
(defun fn-feed-restart (f)
  (declare (xargs :guard t))
  (if (not (fn-feedp f))
      f
      (fn-feed-with-conn
       (fn-feed-with-queue f (fn-feed-queue-settle (fn-feed-queue f)))
       nil)))

(defun fn-feed-settle (f)
  (declare (xargs :guard t))
  (if (not (fn-feedp f))
      f
      (fn-feed-with-conn
       (fn-feed-with-queue f (fn-feed-queue-settle (fn-feed-queue f)))
       nil)))

(defun fn-feed-inflightp (msgid f)
  (declare (xargs :guard t))
  (fn-feed-state-inflightp (fn-feed-state-of msgid (fn-feed-queue f))))

; -----------------------------------------------------------------------------
; The host entry point: one tick, select then drive
;
; This is the function the host calls once per scheduler tick for one peer.
; Every theorem about what the feed emits is stated over it
; (AGENTS.md: the theorem subject is the function the host calls).

(defun fn-feed-tick-step (f obs)
  (declare (xargs :guard t))
  (let ((selected (fn-feed-selection f obs)))
    (if (null selected)
        (mv f nil)
        (fn-feed-offer f selected))))

; -----------------------------------------------------------------------------
; The FNFD journal record family (specs/peering.md sec. 3.3)
;
; Six kinds over books/frame's grammar; frame.lisp is untouched.  The shape is
; books/anchor-record.lisp's: the field grammar never opens here, and the two
; frame entry points are discharged from named `:rule-classes nil' guard
; lemmas.

(defconst *fn-feed-magic* '(70 78 70 68))   ; FNFD
(defconst *fn-feed-max-payload* 1024)

(defconst *fn-feed-kinds*
  '(:feed-enqueue :feed-offer :feed-sent :feed-outcome :feed-drop
    :feed-restart))

(defconst *fn-feed-specs*
  (list (cons :feed-enqueue '(:text :text :nat))           ; peer msgid tick
        (cons :feed-offer   '(:text :text :nat :nat))      ; peer msgid attempt tick
        (cons :feed-sent    '(:text :text :nat))           ; peer msgid attempt
        (cons :feed-outcome (list :text :text :nat
                                  (cons :enum *fn-feed-outcome-codes*)))
        (cons :feed-drop    (list :text :text
                                  (cons :enum *fn-feed-drop-reasons*)))
        (cons :feed-restart '(:text))))                    ; peer

(defthm fn-feed-spec-for-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-feed-specs*) :none))
           (fn-frame-spec-listp (fn-frame-spec-for kind *fn-feed-specs*))))

(defun fn-feed-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-feed-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values))))

(verify-guards fn-feed-record-okp)

; Field projections, in one vocabulary for every kind: field 0 is always the
; peer and field 1 is the Message-ID (except `:feed-restart', which has only
; the peer).
(defun fn-feed-record-peer (values)
  (declare (xargs :guard t))
  (fn-frame-item 0 values))
(defun fn-feed-record-msgid (values)
  (declare (xargs :guard t))
  (fn-frame-item 1 values))
(defun fn-feed-record-nat (n values)
  (declare (xargs :guard t))
  (nfix (fn-frame-item n values)))

(defun fn-feed-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-feed-record-okp kind values) (fn-frame-digestp digest)))
      :bad
      (let ((code (fn-frame-enum-index kind *fn-feed-kinds*)))
        (if (equal code 0)
            :bad
            (let ((payload (fn-frame-fields-octets
                            (fn-frame-spec-for kind *fn-feed-specs*) values)))
              (if (not (fn-cbor-at-mostp payload *fn-feed-max-payload*))
                  :bad
                  (fn-frame-encode *fn-feed-magic* *fn-frame-version* code
                                   payload digest)))))))

(defun fn-feed-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-feed-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
        (if (not (and (equal (fn-frame-result-magic frame) *fn-feed-magic*)
                      (equal (fn-frame-result-version frame)
                             *fn-frame-version*)))
            (fn-frame-error :magic)
            (let ((code (fn-frame-result-kind frame)))
              (if (or (not (posp code)) (< (len *fn-feed-kinds*) code))
                  (fn-frame-error :kind)
                  (let* ((kind (fn-frame-item (- code 1) *fn-feed-kinds*))
                         (spec (fn-frame-spec-for kind *fn-feed-specs*)))
                    (if (equal spec :none)
                        (fn-frame-error :kind)
                        (let ((parsed (fn-frame-fields-parse
                                       spec (fn-frame-result-payload frame))))
                          (if (not (fn-frame-parse-okp parsed))
                              (fn-frame-error (fn-frame-parse-value parsed))
                              (if (not (fn-feed-record-okp
                                        kind (fn-frame-parse-value parsed)))
                                  (fn-frame-error :fields)
                                  (fn-frame-ok *fn-feed-magic* *fn-frame-version*
                                               kind
                                               (fn-frame-parse-value
                                                parsed)))))))))))))

(defthm fn-feed-encode-frame-guard
  (implies (fn-feed-record-okp kind values)
           (and (fn-frame-spec-listp (fn-frame-spec-for kind *fn-feed-specs*))
                (fn-frame-values-okp (fn-frame-spec-for kind *fn-feed-specs*)
                                     values)
                (fn-cbor-octet-listp
                 (fn-frame-fields-octets
                  (fn-frame-spec-for kind *fn-feed-specs*) values))
                (fn-frame-magicp *fn-feed-magic*)
                (fn-cbor-octetp *fn-frame-version*)
                (fn-cbor-octetp (fn-frame-enum-index kind *fn-feed-kinds*))))
  :rule-classes nil)

(verify-guards fn-feed-encode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-feed-encode-frame-guard)))))

(defthm fn-feed-decode-frame-guard
  (implies (fn-frame-result-okp
            (fn-frame-decode octets digest *fn-feed-max-payload*))
           (fn-cbor-octet-listp
            (fn-frame-result-payload
             (fn-frame-decode octets digest *fn-feed-max-payload*))))
  :rule-classes nil)

(verify-guards fn-feed-decode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-feed-decode-frame-guard)))))

; KEYSTONE: the value direction for FNFD.  Every record the host writes
; decodes back to the kind and the field values it started from, so a replay
; reads exactly the decisions that were journaled.
(defthm fn-feed-decode-of-encode
  (implies (and (fn-feed-record-okp kind values)
                (fn-frame-digestp digest)
                (not (equal (fn-feed-encode kind values digest) :bad)))
           (equal (fn-feed-decode (fn-feed-encode kind values digest) digest)
                  (fn-frame-ok *fn-feed-magic* *fn-frame-version* kind values)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-feed-encode fn-feed-decode
                            fn-frame-fields-parse-of-octets
                            fn-frame-item-of-enum-index
                            fn-frame-enum-index-of-item
                            fn-frame-inputp fn-frame-item)
                           (fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets)))))

; KEYSTONE: canonicality.  Two accepted records with the same octets are the
; same record: the encoding is injective on the accepted set, so a journal has
; exactly one spelling per decision.
(defthm fn-feed-encode-is-injective
  (implies (and (fn-feed-record-okp kind values)
                (fn-feed-record-okp kind2 values2)
                (fn-frame-digestp digest)
                (not (equal (fn-feed-encode kind values digest) :bad))
                (not (equal (fn-feed-encode kind2 values2 digest) :bad))
                (equal (fn-feed-encode kind values digest)
                       (fn-feed-encode kind2 values2 digest)))
           (and (equal kind kind2) (equal values values2)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-feed-decode-of-encode)
                 (:instance fn-feed-decode-of-encode
                            (kind kind2) (values values2)))
           :in-theory (disable fn-feed-decode-of-encode fn-feed-encode
                               fn-feed-decode))))

; -----------------------------------------------------------------------------
; Replay: the fold of a journal into a feed state
;
; A journal entry is a decoded `(kind values)' pair.  `fn-feed-replay' folds
; them left to right; `fn-feed-replay-is-the-fold' (peer-feed-invariants) is
; the determinism statement.  Records for another peer are ignored, so one
; file per peer is a host convenience and not a correctness condition.

(defun fn-feed-journal-entry (kind values)
  (declare (xargs :guard t))
  (list kind values))
(defun fn-feed-journal-kind (e)
  (declare (xargs :guard t))
  (fn-bp-nth 0 e))
(defun fn-feed-journal-values (e)
  (declare (xargs :guard t))
  (fn-bp-nth 1 e))

(defun fn-feed-journal-entryp (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len e) 2)
       (fn-feed-record-okp (fn-feed-journal-kind e)
                           (fn-feed-journal-values e))))

(defun fn-feed-journalp (es)
  (declare (xargs :guard t))
  (if (atom es) (null es)
      (and (fn-feed-journal-entryp (car es)) (fn-feed-journalp (cdr es)))))

(defthm fn-feed-journalp-forward-true-listp
  (implies (fn-feed-journalp es) (true-listp es))
  :rule-classes :forward-chaining)

(defun fn-feed-apply-record (f kind values)
  (declare (xargs :guard t))
  (if (not (fn-feedp f))
      f
      (if (not (equal (fn-feed-record-peer values) (fn-feed-peer f)))
          f
          (let ((msgid (fn-feed-record-msgid values)))
            (cond
             ((equal kind :feed-enqueue)
              (fn-feed-enqueue f msgid (fn-feed-record-nat 2 values)))
             ((equal kind :feed-offer)
              (let ((attempt (fn-feed-record-nat 2 values)))
                (if (not (equal (fn-feed-state-of msgid (fn-feed-queue f))
                                :queued))
                    f
                    (fn-feed-make
                     (fn-feed-peer f) (fn-feed-limits-of f)
                     (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                              (fn-feed-offered attempt))
                     (fn-feed-contact f) (fn-feed-backoff-until f)
                     (fn-feed-conn f)
                     (if (< attempt (fn-feed-next-attempt f))
                         (fn-feed-next-attempt f)
                         (+ 1 attempt))))))
             ((equal kind :feed-sent)
              (let ((attempt (fn-feed-record-nat 2 values)))
                (if (not (and (fn-feed-offeredp
                               (fn-feed-state-of msgid (fn-feed-queue f)))
                              (equal (fn-feed-state-attempt
                                      (fn-feed-state-of msgid
                                                        (fn-feed-queue f)))
                                     attempt)))
                    f
                    (fn-feed-with-queue
                     f (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                                (fn-feed-sent attempt))))))
             ((equal kind :feed-outcome)
              (let ((code (fn-frame-item 3 values)))
                (cond ((member-equal code '(235 239 435 438 437 439))
                       (fn-feed-done f msgid))
                      ((member-equal code '(431 436))
                       (fn-feed-with-queue
                        f (fn-feed-queue-requeue (fn-feed-queue f) msgid 0)))
                      (t (fn-feed-with-queue
                          f (fn-feed-queue-requeue-inflight
                             (fn-feed-queue f) 0))))))
             ((equal kind :feed-drop)
              (fn-feed-give-up f msgid (fn-frame-item 2 values)))
             ((equal kind :feed-restart) (fn-feed-restart f))
             (t f))))))

(defun fn-feed-replay (f es)
  (declare (xargs :guard t))
  (if (atom es)
      f
      (fn-feed-replay (fn-feed-apply-record f (fn-feed-journal-kind (car es))
                                            (fn-feed-journal-values (car es)))
                      (cdr es))))

; `fn-feed-drivenp': the journal is one a feed machine could have written.
; Each record must be admissible in the state the fold reached before it -- an
; outcome names an attempt that is in flight, a sent names the attempt its
; offer allocated.  This is a CHECK over the fold, never the conclusion of any
; theorem below: it is what "a journal, not an arbitrary record list" means.
(defun fn-feed-record-drivenp (f kind values)
  (declare (xargs :guard t))
  (and (fn-feedp f)
       (equal (fn-feed-record-peer values) (fn-feed-peer f))
       (let ((msgid (fn-feed-record-msgid values)))
         (cond
          ((equal kind :feed-enqueue)
           (and (fn-feed-namep msgid)
                (not (consp (fn-feed-find msgid (fn-feed-queue f))))
                (< (len (fn-feed-queue f))
                   (fn-feed-max-queue (fn-feed-limits-of f)))))
          ((equal kind :feed-offer)
           (and (equal (fn-feed-state-of msgid (fn-feed-queue f)) :queued)
                (<= (fn-feed-next-attempt f) (fn-feed-record-nat 2 values))))
          ((equal kind :feed-sent)
           (and (fn-feed-offeredp (fn-feed-state-of msgid (fn-feed-queue f)))
                (equal (fn-feed-state-attempt
                        (fn-feed-state-of msgid (fn-feed-queue f)))
                       (fn-feed-record-nat 2 values))))
          ((equal kind :feed-outcome)
           (fn-feed-state-inflightp
            (fn-feed-state-of msgid (fn-feed-queue f))))
          ((equal kind :feed-drop)
           (and (consp (fn-feed-find msgid (fn-feed-queue f)))
                (not (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done))
                (not (fn-feed-droppedp
                      (fn-feed-state-of msgid (fn-feed-queue f))))))
          ((equal kind :feed-restart) t)
          (t nil)))))

(defun fn-feed-drivenp (f es)
  (declare (xargs :guard t))
  (if (atom es)
      (fn-feedp f)
      (and (fn-feed-journal-entryp (car es))
           (fn-feed-record-drivenp f (fn-feed-journal-kind (car es))
                                   (fn-feed-journal-values (car es)))
           (fn-feed-drivenp
            (fn-feed-apply-record f (fn-feed-journal-kind (car es))
                                  (fn-feed-journal-values (car es)))
            (cdr es)))))

; Counting: how many accepted outcomes a journal holds for one (peer, msgid).
(defun fn-feed-accepted-outcomep (peer msgid e)
  (declare (xargs :guard t))
  (and (equal (fn-feed-journal-kind e) :feed-outcome)
       (equal (fn-feed-record-peer (fn-feed-journal-values e)) peer)
       (equal (fn-feed-record-msgid (fn-feed-journal-values e)) msgid)
       (member-equal (fn-frame-item 3 (fn-feed-journal-values e))
                     *fn-feed-accepted-codes*)
       t))

(defun fn-feed-count-accepted (peer msgid es)
  (declare (xargs :guard t))
  (if (atom es)
      0
      (+ (if (fn-feed-accepted-outcomep peer msgid (car es)) 1 0)
         (fn-feed-count-accepted peer msgid (cdr es)))))

; A drop record for one (peer, msgid) naming one reason.
(defun fn-feed-drop-recordp (peer msgid reason e)
  (declare (xargs :guard t))
  (and (equal (fn-feed-journal-kind e) :feed-drop)
       (equal (fn-feed-record-peer (fn-feed-journal-values e)) peer)
       (equal (fn-feed-record-msgid (fn-feed-journal-values e)) msgid)
       (equal (fn-frame-item 2 (fn-feed-journal-values e)) reason)
       t))

(defun fn-feed-has-drop-recordp (peer msgid es)
  (declare (xargs :guard t))
  (if (atom es)
      nil
      (or (and (equal (fn-feed-journal-kind (car es)) :feed-drop)
               (equal (fn-feed-record-peer (fn-feed-journal-values (car es)))
                      peer)
               (equal (fn-feed-record-msgid (fn-feed-journal-values (car es)))
                      msgid)
               t)
          (fn-feed-has-drop-recordp peer msgid (cdr es)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md sec. 2)
;
; What leaves this book enabled: the record lemmas, the two codec keystones,
; the list-recursive queue and journal vocabulary (the induction vocabulary),
; and the five offer-state glue predicates, which are written in accessor
; vocabulary.  Withdrawn: the recognizers, every transition, the two codec
; entry points and the replay fold.  `peer-feed-invariants' opens them under
; the one name below.

(deftheory fn-feed-vocabulary
  '((:d fn-feed-entryp) (:d fn-feedp) (:d fn-feed-limitsp)
    (:d fn-feed-namep)
    (:d fn-feed-open) (:d fn-feed-with-queue) (:d fn-feed-with-conn)
    (:d fn-feed-with-contact) (:d fn-feed-with-backoff)
    (:d fn-feed-enqueue) (:d fn-feed-selection) (:d fn-feed-offer)
    (:d fn-feed-send) (:d fn-feed-done) (:d fn-feed-back-off)
    (:d fn-feed-lost) (:d fn-feed-give-up) (:d fn-feed-retry-exhaustedp)
    (:d fn-feed-observe) (:d fn-feed-restart) (:d fn-feed-settle)
    (:d fn-feed-tick-step) (:d fn-feed-responsep)
    (:d fn-feed-line)
    (:d fn-feed-record-okp) (:d fn-feed-encode) (:d fn-feed-decode)
    (:d fn-feed-apply-record) (:d fn-feed-record-drivenp)
    fn-feed-spec-for-is-spec-list))

(in-theory (disable fn-feed-vocabulary))
