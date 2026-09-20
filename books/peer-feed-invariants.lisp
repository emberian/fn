; fn: the outbound feed keystones (specs/peering.md sec. 4, K5).
;
; Exactly-once per peer under restart, stated over the functions the host
; calls: `fn-feed-tick-step' (one scheduler tick for one peer),
; `fn-feed-observe' (one parsed response line) and `fn-feed-replay' (the fold
; of the FNFD journal at open).
;
; The four claims, each a theorem below:
;
;   1. In a journal a feed machine could have written, at most one accepted
;      outcome is ever recorded for one (peer, Message-ID).
;      `fn-feed-at-most-one-accepted-outcome'.
;   2. A finished entry is never offered again, and after a restart no
;      TAKETHIS can be emitted until a fresh CHECK/IHAVE has been offered and
;      answered.  `fn-feed-done-is-never-selected',
;      `fn-feed-tick-step-offers-the-selection',
;      `fn-feed-restart-emits-no-transfer'.
;   3. Replay is deterministic and is a fold: replaying a journal in two
;      pieces is replaying it whole.  `fn-feed-replay-is-the-fold'.
;   4. Backoff is monotone in the attempt count and a deadline is never
;      lowered.  `fn-feed-backoff-delay-is-monotone',
;      `fn-feed-back-off-does-not-lower-the-deadline'.
;   5. Nothing leaves the queue without a drop record naming a reason.
;      `fn-feed-drop-needs-a-drop-record'.

(in-package "ACL2")
(include-book "peer-feed")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-feed-vocabulary)))

; -----------------------------------------------------------------------------
; Queue vocabulary lemmas
;
; Proof vocabulary, withdrawn at the end under `fn-feed-invariants-vocabulary'.

(defthm fn-feed-state-of-of-set-state-same
  (implies (consp (fn-feed-find msgid xs))
           (equal (fn-feed-state-of msgid (fn-feed-queue-set-state xs msgid s))
                  s)))

(defthm fn-feed-state-of-of-set-state-other
  (implies (not (equal other msgid))
           (equal (fn-feed-state-of other (fn-feed-queue-set-state xs msgid s))
                  (fn-feed-state-of other xs))))

(defthm fn-feed-state-of-of-requeue-other
  (implies (not (equal other msgid))
           (equal (fn-feed-state-of other (fn-feed-queue-requeue xs msgid tick))
                  (fn-feed-state-of other xs))))

(defthm fn-feed-state-of-of-requeue-inflight-when-not-inflight
  (implies (not (fn-feed-state-inflightp (fn-feed-state-of other xs)))
           (equal (fn-feed-state-of other
                                    (fn-feed-queue-requeue-inflight xs tick))
                  (fn-feed-state-of other xs))))

(defthm fn-feed-state-of-of-settle-when-not-inflight
  (implies (not (fn-feed-state-inflightp (fn-feed-state-of other xs)))
           (equal (fn-feed-state-of other (fn-feed-queue-settle xs))
                  (fn-feed-state-of other xs))))

(defthm fn-feed-find-of-append-when-absent
  (implies (not (consp (fn-feed-find msgid xs)))
           (equal (fn-feed-find msgid (append xs (list e)))
                  (if (equal (fn-feed-entry-msgid e) msgid) e nil))))

(defthm fn-feed-head-queued-is-queued
  (implies (fn-feed-head-queued xs)
           (equal (fn-feed-state-of (fn-feed-head-queued xs) xs) :queued)))

(defthm fn-feed-head-queued-is-a-member
  (implies (fn-feed-head-queued xs)
           (consp (fn-feed-find (fn-feed-head-queued xs) xs))))

(defthm fn-feed-inflight-count-of-settle
  (equal (fn-feed-inflight-count (fn-feed-queue-settle xs)) 0))

(defthm fn-feed-inflight-count-of-requeue-inflight
  (equal (fn-feed-inflight-count (fn-feed-queue-requeue-inflight xs tick)) 0))

(defthm fn-feed-entry-listp-of-set-state
  (implies (and (fn-feed-entry-listp xs) (fn-feed-state-okp s))
           (fn-feed-entry-listp (fn-feed-queue-set-state xs msgid s))))

(defthm fn-feed-entry-listp-of-requeue
  (implies (fn-feed-entry-listp xs)
           (fn-feed-entry-listp (fn-feed-queue-requeue xs msgid tick))))

(defthm fn-feed-entry-listp-of-requeue-inflight
  (implies (fn-feed-entry-listp xs)
           (fn-feed-entry-listp (fn-feed-queue-requeue-inflight xs tick))))

(defthm fn-feed-entry-listp-of-settle
  (implies (fn-feed-entry-listp xs)
           (fn-feed-entry-listp (fn-feed-queue-settle xs))))

(defthm fn-feed-msgids-of-set-state
  (equal (fn-feed-msgids (fn-feed-queue-set-state xs msgid s))
         (fn-feed-msgids xs)))
(defthm fn-feed-msgids-of-requeue
  (equal (fn-feed-msgids (fn-feed-queue-requeue xs msgid tick))
         (fn-feed-msgids xs)))
(defthm fn-feed-msgids-of-requeue-inflight
  (equal (fn-feed-msgids (fn-feed-queue-requeue-inflight xs tick))
         (fn-feed-msgids xs)))
(defthm fn-feed-msgids-of-settle
  (equal (fn-feed-msgids (fn-feed-queue-settle xs)) (fn-feed-msgids xs)))
(defthm fn-feed-msgids-of-append
  (equal (fn-feed-msgids (append xs ys))
         (append (fn-feed-msgids xs) (fn-feed-msgids ys))))

(defthm fn-feed-distinctp-of-set-state
  (implies (fn-feed-distinctp xs)
           (fn-feed-distinctp (fn-feed-queue-set-state xs msgid s))))
(defthm fn-feed-distinctp-of-requeue
  (implies (fn-feed-distinctp xs)
           (fn-feed-distinctp (fn-feed-queue-requeue xs msgid tick))))
(defthm fn-feed-distinctp-of-requeue-inflight
  (implies (fn-feed-distinctp xs)
           (fn-feed-distinctp (fn-feed-queue-requeue-inflight xs tick))))
(defthm fn-feed-distinctp-of-settle
  (implies (fn-feed-distinctp xs)
           (fn-feed-distinctp (fn-feed-queue-settle xs))))

(defthm fn-feed-len-of-set-state
  (equal (len (fn-feed-queue-set-state xs msgid s)) (len xs)))
(defthm fn-feed-len-of-requeue
  (equal (len (fn-feed-queue-requeue xs msgid tick)) (len xs)))
(defthm fn-feed-len-of-requeue-inflight
  (equal (len (fn-feed-queue-requeue-inflight xs tick)) (len xs)))
(defthm fn-feed-len-of-settle
  (equal (len (fn-feed-queue-settle xs)) (len xs)))

(defthm fn-feed-inflight-count-of-set-state-not-inflight
  (implies (and (not (fn-feed-state-inflightp s))
                (<= (fn-feed-inflight-count xs) 1))
           (<= (fn-feed-inflight-count (fn-feed-queue-set-state xs msgid s))
               1))
  :rule-classes :linear)

(defthm fn-feed-inflight-count-of-requeue
  (implies (<= (fn-feed-inflight-count xs) 1)
           (<= (fn-feed-inflight-count (fn-feed-queue-requeue xs msgid tick))
               1))
  :rule-classes :linear)

(defthm fn-feed-attempts-belowp-of-settle
  (fn-feed-attempts-belowp (fn-feed-queue-settle xs) n))
(defthm fn-feed-attempts-belowp-of-requeue-inflight
  (fn-feed-attempts-belowp (fn-feed-queue-requeue-inflight xs tick) n))
(defthm fn-feed-attempts-belowp-of-requeue
  (implies (fn-feed-attempts-belowp xs n)
           (fn-feed-attempts-belowp (fn-feed-queue-requeue xs msgid tick) n)))
(defthm fn-feed-attempts-belowp-of-set-state-not-inflight
  (implies (and (fn-feed-attempts-belowp xs n) (not (fn-feed-state-inflightp s)))
           (fn-feed-attempts-belowp (fn-feed-queue-set-state xs msgid s) n)))

; -----------------------------------------------------------------------------
; KEYSTONE: backoff is monotone (specs/peering.md sec. 3.2)

(defthm fn-feed-backoff-delay-is-bounded
  (<= (fn-feed-backoff-delay base attempts) *fn-feed-max-backoff*)
  :rule-classes :linear)

(defthm fn-feed-backoff-delay-is-a-nat
  (natp (fn-feed-backoff-delay base attempts))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-feed-backoff-delay-step-is-not-smaller
  (<= (fn-feed-backoff-delay base n)
      (fn-feed-backoff-delay base (+ 1 (nfix n))))
  :rule-classes :linear)

(defthm fn-feed-backoff-delay-is-monotone
  (implies (<= (nfix m) (nfix n))
           (<= (fn-feed-backoff-delay base m)
               (fn-feed-backoff-delay base n)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-feed-backoff-delay base n))))

(defthm fn-feed-back-off-does-not-lower-the-deadline
  (implies (fn-feedp f)
           (<= (fn-feed-backoff-until f)
               (fn-feed-backoff-until (fn-feed-back-off f msgid obs))))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; Preservation: every transition keeps `fn-feedp'

(defthm fn-feed-enqueue-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-enqueue f msgid tick))))

(defthm fn-feed-offer-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (mv-nth 0 (fn-feed-offer f msgid)))))

(defthm fn-feed-send-preserves-feedp
  (implies (fn-feedp f)
           (fn-feedp (mv-nth 0 (fn-feed-send f msgid article)))))

(defthm fn-feed-done-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-done f msgid))))

(defthm fn-feed-back-off-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-back-off f msgid obs))))

(defthm fn-feed-lost-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-lost f obs))))

(defthm fn-feed-give-up-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-give-up f msgid reason))))

(defthm fn-feed-restart-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-restart f))))

(defthm fn-feed-observe-preserves-feedp
  (implies (fn-feedp f)
           (fn-feedp (mv-nth 0 (fn-feed-observe f response article obs)))))

(defthm fn-feed-tick-step-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (mv-nth 0 (fn-feed-tick-step f obs)))))

(defthm fn-feed-apply-record-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-apply-record f kind values))))

(defthm fn-feed-replay-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-replay f es))))

(defthm fn-feed-apply-record-preserves-peer
  (implies (fn-feedp f)
           (equal (fn-feed-peer (fn-feed-apply-record f kind values))
                  (fn-feed-peer f))))

(defthm fn-feed-replay-preserves-peer
  (implies (fn-feedp f)
           (equal (fn-feed-peer (fn-feed-replay f es)) (fn-feed-peer f))))

; -----------------------------------------------------------------------------
; KEYSTONE: replay is a fold, so it is deterministic and order is all that
; matters -- replaying a journal in two pieces is replaying it whole.

(defthm fn-feed-replay-is-the-fold
  (equal (fn-feed-replay f (append es fs))
         (fn-feed-replay (fn-feed-replay f es) fs)))

; -----------------------------------------------------------------------------
; KEYSTONE: a finished entry is never offered again
;
; `fn-feed-tick-step' is the function the host calls once per scheduler tick.
; Its only effect is one `:command' offering the selection, and the selection
; is a `:queued' entry, so an entry that is `:done' or `(:dropped r)' is never
; the subject of a command.

(defthm fn-feed-selection-is-queued
  (implies (and (fn-feedp f) (fn-feed-selection f obs))
           (equal (fn-feed-state-of (fn-feed-selection f obs)
                                    (fn-feed-queue f))
                  :queued)))

(defthm fn-feed-done-is-never-selected
  (implies (and (fn-feedp f)
                (not (equal (fn-feed-state-of msgid (fn-feed-queue f))
                            :queued)))
           (not (equal (fn-feed-selection f obs) msgid)))
  :hints (("Goal" :use ((:instance fn-feed-selection-is-queued))
           :in-theory (disable fn-feed-selection-is-queued))))

(defthm fn-feed-tick-step-offers-the-selection
  (implies (and (fn-feedp f) (fn-feed-selection f obs))
           (equal (mv-nth 1 (fn-feed-tick-step f obs))
                  (list (list :command (fn-feed-conn f)
                              (fn-feed-offer-line
                               (fn-feed-selection f obs)
                               (fn-feed-streamingp (fn-feed-limits-of f))))))))

(defthm fn-feed-tick-step-is-silent-without-a-selection
  (implies (not (fn-feed-selection f obs))
           (equal (mv-nth 1 (fn-feed-tick-step f obs)) nil)))

; -----------------------------------------------------------------------------
; KEYSTONE: a restart resolves an in-flight offer by CHECK/IHAVE, never by a
; blind TAKETHIS
;
; `fn-feed-send' is the only producer of a TAKETHIS or of an article block, and
; it fires only on an entry in `(:offered n)'.  A restart leaves no entry in
; flight, so no transfer can be emitted until a fresh offer has been made and
; answered 335/238.

(defthm fn-feed-restart-has-no-inflight
  (implies (fn-feedp f)
           (equal (fn-feed-inflight-count (fn-feed-queue (fn-feed-restart f)))
                  0)))

(defthm fn-feed-inflight-count-zero-means-not-inflight
  (implies (and (equal (fn-feed-inflight-count xs) 0)
                (consp (fn-feed-find msgid xs)))
           (not (fn-feed-state-inflightp (fn-feed-state-of msgid xs)))))

(defthm fn-feed-restart-emits-no-transfer
  (implies (fn-feedp f)
           (equal (mv-nth 1 (fn-feed-send (fn-feed-restart f) msgid article))
                  nil))
  :hints (("Goal"
           :use ((:instance fn-feed-inflight-count-zero-means-not-inflight
                            (xs (fn-feed-queue (fn-feed-restart f)))))
           :in-theory (disable fn-feed-inflight-count-zero-means-not-inflight))))

(defthm fn-feed-restart-then-tick-offers
  (implies (and (fn-feedp f) (fn-feed-selection (fn-feed-restart f) obs))
           (fn-feed-command-offersp
            (fn-frame-item 2 (car (mv-nth 1 (fn-feed-tick-step
                                             (fn-feed-restart f) obs))))
            (fn-feed-selection (fn-feed-restart f) obs))))

; -----------------------------------------------------------------------------
; KEYSTONE: at most one accepted outcome per (peer, Message-ID)
;
; `fn-feed-drivenp' says the record list is one a feed machine could have
; written: every record was admissible in the state the fold had reached.  It
; is a check over the fold, never the conclusion.  Once an entry is `:done' no
; driven record can make it in flight again, and only an in-flight entry can
; carry an outcome, so a second accepted outcome is not a journal.

(defthm fn-feed-donep-is-not-inflight
  (implies (equal (fn-feed-state-of msgid xs) :done)
           (not (fn-feed-state-inflightp (fn-feed-state-of msgid xs)))))

(defthm fn-feed-done-survives-a-driven-record
  (implies (and (fn-feedp f)
                (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done)
                (fn-feed-record-drivenp f kind values))
           (equal (fn-feed-state-of
                   msgid (fn-feed-queue (fn-feed-apply-record f kind values)))
                  :done)))

(defthm fn-feed-done-is-not-an-accepted-outcome-record
  (implies (and (fn-feedp f)
                (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done)
                (fn-feed-record-drivenp f kind values)
                (equal (fn-feed-record-peer values) (fn-feed-peer f))
                (equal (fn-feed-record-msgid values) msgid))
           (not (equal kind :feed-outcome))))

(defthm fn-feed-done-means-no-more-accepted-outcomes
  (implies (and (fn-feedp f)
                (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done)
                (fn-feed-drivenp f es))
           (and (equal (fn-feed-state-of
                        msgid (fn-feed-queue (fn-feed-replay f es)))
                       :done)
                (equal (fn-feed-count-accepted (fn-feed-peer f) msgid es) 0)))
  :hints (("Goal" :induct (fn-feed-drivenp f es))))

(defthm fn-feed-accepted-outcome-makes-it-done
  (implies (and (fn-feedp f)
                (fn-feed-record-drivenp f kind values)
                (fn-feed-accepted-outcomep (fn-feed-peer f) msgid
                                           (fn-feed-journal-entry kind values)))
           (equal (fn-feed-state-of
                   msgid (fn-feed-queue (fn-feed-apply-record f kind values)))
                  :done)))

(defthm fn-feed-at-most-one-accepted-outcome
  (implies (and (fn-feedp f) (fn-feed-drivenp f es))
           (<= (fn-feed-count-accepted (fn-feed-peer f) msgid es) 1))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-feed-drivenp f es))))

; -----------------------------------------------------------------------------
; KEYSTONE: nothing is dropped without a drop record naming the reason

(defthm fn-feed-not-dropped-survives-a-non-drop-record
  (implies (and (fn-feedp f)
                (not (fn-feed-droppedp (fn-feed-state-of msgid
                                                         (fn-feed-queue f))))
                (not (and (equal kind :feed-drop)
                          (equal (fn-feed-record-peer values) (fn-feed-peer f))
                          (equal (fn-feed-record-msgid values) msgid))))
           (not (fn-feed-droppedp
                 (fn-feed-state-of
                  msgid
                  (fn-feed-queue (fn-feed-apply-record f kind values)))))))

(defthm fn-feed-drop-needs-a-drop-record
  (implies (and (fn-feedp f)
                (not (fn-feed-droppedp (fn-feed-state-of msgid
                                                         (fn-feed-queue f))))
                (fn-feed-droppedp
                 (fn-feed-state-of msgid
                                   (fn-feed-queue (fn-feed-replay f es)))))
           (fn-feed-has-drop-recordp (fn-feed-peer f) msgid es))
  :hints (("Goal" :induct (fn-feed-replay f es))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md sec. 2)

(deftheory fn-feed-invariants-vocabulary
  '(fn-feed-state-of-of-set-state-same fn-feed-state-of-of-set-state-other
    fn-feed-state-of-of-requeue-other
    fn-feed-state-of-of-requeue-inflight-when-not-inflight
    fn-feed-state-of-of-settle-when-not-inflight
    fn-feed-find-of-append-when-absent
    fn-feed-head-queued-is-queued fn-feed-head-queued-is-a-member
    fn-feed-inflight-count-of-settle fn-feed-inflight-count-of-requeue-inflight
    fn-feed-entry-listp-of-set-state fn-feed-entry-listp-of-requeue
    fn-feed-entry-listp-of-requeue-inflight fn-feed-entry-listp-of-settle
    fn-feed-msgids-of-set-state fn-feed-msgids-of-requeue
    fn-feed-msgids-of-requeue-inflight fn-feed-msgids-of-settle
    fn-feed-msgids-of-append
    fn-feed-distinctp-of-set-state fn-feed-distinctp-of-requeue
    fn-feed-distinctp-of-requeue-inflight fn-feed-distinctp-of-settle
    fn-feed-len-of-set-state fn-feed-len-of-requeue
    fn-feed-len-of-requeue-inflight fn-feed-len-of-settle
    fn-feed-inflight-count-of-set-state-not-inflight
    fn-feed-inflight-count-of-requeue
    fn-feed-attempts-belowp-of-settle
    fn-feed-attempts-belowp-of-requeue-inflight
    fn-feed-attempts-belowp-of-requeue
    fn-feed-attempts-belowp-of-set-state-not-inflight
    fn-feed-donep-is-not-inflight
    fn-feed-inflight-count-zero-means-not-inflight
    fn-feed-done-survives-a-driven-record
    fn-feed-done-is-not-an-accepted-outcome-record
    fn-feed-accepted-outcome-makes-it-done
    fn-feed-not-dropped-survives-a-non-drop-record))

(in-theory (disable fn-feed-invariants-vocabulary))
