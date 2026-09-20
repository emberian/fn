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

; The companions of the four rules above: what those queue operations do to
; the entry they DO touch.  `fn-feed-state-of' reads the FIRST entry with the
; Message-ID, and every operation here keeps the order and the Message-IDs,
; so the entry read after it is the transform of the entry read before it.
(defthm fn-feed-find-of-append-when-present
  (implies (consp (fn-feed-find msgid xs))
           (equal (fn-feed-find msgid (append xs ys))
                  (fn-feed-find msgid xs))))

; And the same fact in `fn-feed-state-of' vocabulary.  The rule above cannot
; serve a proof that closes `(:d fn-feed-state-of)' -- the goal never becomes
; a `fn-feed-find' term for it to match -- and the enqueue arm of the
; dispatcher is exactly such a proof (`Subgoal 2.77''').
(defthm fn-feed-state-of-of-append-when-present
  (implies (consp (fn-feed-find msgid xs))
           (equal (fn-feed-state-of msgid (append xs ys))
                  (fn-feed-state-of msgid xs))))

(defthm fn-feed-state-of-of-requeue-same
  (implies (consp (fn-feed-find msgid xs))
           (equal (fn-feed-state-of msgid
                                    (fn-feed-queue-requeue xs msgid tick))
                  :queued)))

(defthm fn-feed-state-of-of-requeue-inflight-when-inflight
  (implies (fn-feed-state-inflightp (fn-feed-state-of msgid xs))
           (equal (fn-feed-state-of msgid
                                    (fn-feed-queue-requeue-inflight xs tick))
                  :queued)))

(defthm fn-feed-state-of-of-settle-when-inflight
  (implies (fn-feed-state-inflightp (fn-feed-state-of msgid xs))
           (equal (fn-feed-state-of msgid (fn-feed-queue-settle xs))
                  :queued)))

; Every entry of an `fn-feed-entry-listp' is a cons (`fn-feed-entry-shapep'
; forward-chains to it), so "find returned a non-cons" IS "no entry matches"
; -- but only under that hypothesis, which is why it is stated here.
(defthm fn-feed-find-of-append-when-absent
  (implies (and (fn-feed-entry-listp xs)
                (not (consp (fn-feed-find msgid xs))))
           (equal (fn-feed-find msgid (append xs (list e)))
                  (if (equal (fn-feed-entry-msgid e) msgid) e nil))))

; The head queued Message-ID is one of the queue's, and a Message-ID of the
; queue is found: the two facts the head-queued lemmas below run on.
(defthm fn-feed-head-queued-is-in-msgids
  (implies (fn-feed-head-queued xs)
           (member-equal (fn-feed-head-queued xs) (fn-feed-msgids xs))))

(defthm fn-feed-find-of-a-member-is-consp
  (implies (and (fn-feed-entry-listp xs)
                (member-equal msgid (fn-feed-msgids xs)))
           (consp (fn-feed-find msgid xs))))

; The shape fact the composite preservation proofs were missing: `find'
; returns either nil or an element of the list, and every element of an
; `fn-feed-entry-listp' is a cons, so an entry whose STATE is anything at all
; is a cons.  This is what turns `(equal (fn-feed-state-of msgid xs) :queued)'
; -- which is what a transition arm tests -- into the `consp' hypothesis of
; the exact in-flight count below.
(defthm fn-feed-find-is-consp-when-the-state-is-a-state
  (implies (and (fn-feed-entry-listp xs) (fn-feed-state-of msgid xs))
           (consp (fn-feed-find msgid xs))))

; Distinctness is what makes `fn-feed-state-of' of the head queued
; Message-ID the head queued entry: without it an earlier entry with the same
; Message-ID would answer first.
(defthm fn-feed-head-queued-is-queued
  (implies (and (fn-feed-distinctp xs) (fn-feed-head-queued xs))
           (equal (fn-feed-state-of (fn-feed-head-queued xs) xs) :queued)))

(defthm fn-feed-head-queued-is-a-member
  (implies (and (fn-feed-entry-listp xs) (fn-feed-head-queued xs))
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

; Enqueue appends one entry, so every conjunct of `fn-feedp' needs its
; append case.  These are the five, plus the two membership bridges the
; distinctness case runs on.

; The exact in-flight count under a state replacement, and the two facts an
; offer needs: the new state is a state, and an attempt id below the bumped
; next-attempt keeps every other entry below it too.

(defthm fn-feed-state-okp-of-offered
  (fn-feed-state-okp (fn-feed-offered a)))
(defthm fn-feed-state-okp-of-sent
  (fn-feed-state-okp (fn-feed-sent a)))
(defthm fn-feed-state-okp-of-dropped
  (fn-feed-state-okp (fn-feed-dropped r)))

(defthm fn-feed-droppedp-of-the-offer-states
  (and (not (fn-feed-droppedp (fn-feed-offered a)))
       (not (fn-feed-droppedp (fn-feed-sent a)))
       (fn-feed-droppedp (fn-feed-dropped r))))

; `fn-feed-droppedp' propagation.  Every queue operation a journal record can
; perform either leaves an entry alone or writes `:queued', `:done' or an
; offer state over it, so an entry that is not dropped stays not dropped --
; WITHOUT any disequality between the entry read and the entry written.  That
; is the point of stating them this way: the dispatcher's arms then need no
; case split on whether the record names this entry, which is what the
; `Subgoal 142.104.78''' of the previous lane's measurement was.
(defthm fn-feed-droppedp-of-state-of-set-state
  (implies (and (not (fn-feed-droppedp st))
                (not (fn-feed-droppedp (fn-feed-state-of msgid xs))))
           (not (fn-feed-droppedp
                 (fn-feed-state-of msgid
                                   (fn-feed-queue-set-state xs other st))))))

(defthm fn-feed-droppedp-of-state-of-requeue
  (implies (not (fn-feed-droppedp (fn-feed-state-of msgid xs)))
           (not (fn-feed-droppedp
                 (fn-feed-state-of msgid
                                   (fn-feed-queue-requeue xs other tick))))))

(defthm fn-feed-droppedp-of-state-of-requeue-inflight
  (implies (not (fn-feed-droppedp (fn-feed-state-of msgid xs)))
           (not (fn-feed-droppedp
                 (fn-feed-state-of
                  msgid (fn-feed-queue-requeue-inflight xs tick))))))

(defthm fn-feed-droppedp-of-state-of-settle
  (implies (not (fn-feed-droppedp (fn-feed-state-of msgid xs)))
           (not (fn-feed-droppedp
                 (fn-feed-state-of msgid (fn-feed-queue-settle xs))))))

(defthm fn-feed-droppedp-of-state-of-append-one
  (implies (and (fn-feed-entry-listp xs)
                (not (fn-feed-droppedp (fn-feed-state-of msgid xs)))
                (not (fn-feed-droppedp (fn-feed-entry-state e))))
           (not (fn-feed-droppedp
                 (fn-feed-state-of msgid (append xs (list e)))))))

; Predicate-and-accessor-of-constructor facts for the offer states, and the
; consp shape facts forward reasoning needs once the state predicates are
; closed (docs/proof-style.md sec. 1).  A proof that closes the state
; vocabulary keeps its goals in it and reaches the queue lemmas through
; these.
(defthm fn-feed-state-inflightp-of-offered
  (fn-feed-state-inflightp (fn-feed-offered a)))
(defthm fn-feed-state-inflightp-of-sent
  (fn-feed-state-inflightp (fn-feed-sent a)))
(defthm fn-feed-state-inflightp-of-dropped
  (not (fn-feed-state-inflightp (fn-feed-dropped r))))
(defthm fn-feed-state-attempt-of-offered
  (equal (fn-feed-state-attempt (fn-feed-offered a)) (nfix a)))
(defthm fn-feed-state-attempt-of-sent
  (equal (fn-feed-state-attempt (fn-feed-sent a)) (nfix a)))
; The attempt of an in-flight state is a natural.  `fn-feed-offeredp' carries
; it as a conjunct, and a proof that closes that predicate loses it: the
; `:feed-sent' arm's residue was a subgoal whose hypothesis said the attempt
; was NEGATIVE, which `fn-feed-offeredp' already forbids.  Stated over
; `fn-bp-nth' because that is what `fn-feed-state-attempt' opens to.
(defthm fn-feed-offer-states-forward-natp
  (and (implies (fn-feed-offeredp s) (natp (fn-bp-nth 1 s)))
       (implies (fn-feed-sentp s) (natp (fn-bp-nth 1 s))))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-feed-offeredp s)
                                      (natp (fn-bp-nth 1 s)))
                  :trigger-terms ((fn-feed-offeredp s)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-sentp s) (natp (fn-bp-nth 1 s)))
                  :trigger-terms ((fn-feed-sentp s)))))

; The attempt-bound case over the OPEN spelling of an in-flight state: a
; ground constructor call such as `(fn-feed-sent 0)' evaluates to
; `'(:sent 0)' however the definition rune is set, so the constructor-form
; rule above cannot reach it.
(defthm fn-feed-attempts-belowp-of-set-state-open-inflight
  (implies (and (fn-feed-attempts-belowp xs n) (natp a) (< a (nfix n)))
           (and (fn-feed-attempts-belowp
                 (fn-feed-queue-set-state xs msgid (list :offered a)) n)
                (fn-feed-attempts-belowp
                 (fn-feed-queue-set-state xs msgid (list :sent a)) n))))

(defthm fn-feed-offer-states-forward-consp
  (and (implies (fn-feed-offeredp s) (consp s))
       (implies (fn-feed-sentp s) (consp s))
       (implies (fn-feed-state-inflightp s) (consp s)))
  :rule-classes ((:forward-chaining
                  :corollary (implies (fn-feed-offeredp s) (consp s))
                  :trigger-terms ((fn-feed-offeredp s)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-sentp s) (consp s))
                  :trigger-terms ((fn-feed-sentp s)))
                 (:forward-chaining
                  :corollary (implies (fn-feed-state-inflightp s) (consp s))
                  :trigger-terms ((fn-feed-state-inflightp s)))))

(defthm fn-feed-inflight-count-of-set-state-exact
  (implies (consp (fn-feed-find msgid xs))
           (equal (fn-feed-inflight-count (fn-feed-queue-set-state xs msgid s))
                  (+ (fn-feed-inflight-count xs)
                     (if (fn-feed-state-inflightp s) 1 0)
                     (- (if (fn-feed-state-inflightp (fn-feed-state-of msgid xs))
                            1 0))))))

; The form the arms actually need: the old state is `:queued', which is not in
; flight, so the subtraction term of the exact count vanishes.  Proved from
; the exact count and the shape fact above, so it adds no new content.
(defthm fn-feed-inflight-count-of-set-state-from-queued
  (implies (and (fn-feed-entry-listp xs)
                (equal (fn-feed-state-of msgid xs) :queued))
           (equal (fn-feed-inflight-count (fn-feed-queue-set-state xs msgid s))
                  (+ (fn-feed-inflight-count xs)
                     (if (fn-feed-state-inflightp s) 1 0))))
  :hints (("Goal"
           :use ((:instance fn-feed-inflight-count-of-set-state-exact)
                 (:instance fn-feed-find-is-consp-when-the-state-is-a-state))
           :in-theory (disable fn-feed-inflight-count-of-set-state-exact
                               fn-feed-find-is-consp-when-the-state-is-a-state))))

(defthm fn-feed-attempts-belowp-monotone
  (implies (and (fn-feed-attempts-belowp xs m) (<= (nfix m) (nfix n)))
           (fn-feed-attempts-belowp xs n)))

(defthm fn-feed-attempts-belowp-of-set-state-inflight
  (implies (and (fn-feed-attempts-belowp xs n) (< (nfix a) (nfix n)))
           (and (fn-feed-attempts-belowp
                 (fn-feed-queue-set-state xs msgid (fn-feed-offered a)) n)
                (fn-feed-attempts-belowp
                 (fn-feed-queue-set-state xs msgid (fn-feed-sent a)) n))))

(defthm fn-feed-member-of-append
  (iff (member-equal a (append p q))
       (or (member-equal a p) (member-equal a q))))

(defthm fn-feed-not-member-when-find-is-not-consp
  (implies (and (fn-feed-entry-listp xs)
                (not (consp (fn-feed-find msgid xs))))
           (not (member-equal msgid (fn-feed-msgids xs)))))

(defthm fn-feed-entry-listp-of-append-one
  (implies (and (fn-feed-entry-listp xs) (fn-feed-entryp e))
           (fn-feed-entry-listp (append xs (list e)))))

(defthm fn-feed-distinctp-of-append-one
  (implies (and (fn-feed-entry-listp xs)
                (fn-feed-distinctp xs)
                (not (consp (fn-feed-find (fn-feed-entry-msgid e) xs))))
           (fn-feed-distinctp (append xs (list e)))))

(defthm fn-feed-inflight-count-of-append-one
  (implies (not (fn-feed-state-inflightp (fn-feed-entry-state e)))
           (equal (fn-feed-inflight-count (append xs (list e)))
                  (fn-feed-inflight-count xs))))

(defthm fn-feed-attempts-belowp-of-append-one
  (implies (and (fn-feed-attempts-belowp xs n)
                (not (fn-feed-state-inflightp (fn-feed-entry-state e))))
           (fn-feed-attempts-belowp (append xs (list e)) n)))

(defthm fn-feed-len-of-append-one
  (equal (len (append xs (list e))) (+ 1 (len xs))))

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

; The one `fn-feedp' conjunct an offer moves is the attempt bound, and the
; checkpoint showed why the rewrite above cannot reach it: `fn-feed-offered'
; is a two-element list the simplifier opens to `(list :offered n)' before any
; rule keyed on the constructor could fire.  So the conjunct is stated on its
; own, over the queue field with the feed record closed around it, and cited
; by `:use' -- the match then does not depend on how the offer state is
; spelled.  Content: the offer writes the CURRENT next-attempt into the entry
; and bumps next-attempt past it, so every in-flight entry is below the new
; bound -- the new entry by one, the others because they were below the old.
(local
 (defthm fn-feed-attempts-belowp-after-an-offer
   (implies (and (fn-feed-attempts-belowp xs n) (natp n))
            (fn-feed-attempts-belowp
             (fn-feed-queue-set-state xs msgid (list :offered n))
             (+ 1 n)))
   :rule-classes nil))

; The same for the transfer: `fn-feed-send' reuses the attempt the offer
; allocated -- it opens no new one -- so the bound is unchanged, and the
; attempt it reuses is below it because the entry was in flight.
(local
 (defthm fn-feed-inflight-attempt-is-below-the-bound
   (implies (and (fn-feed-attempts-belowp xs n)
                 (fn-feed-state-inflightp (fn-feed-state-of msgid xs)))
            (< (fn-feed-state-attempt (fn-feed-state-of msgid xs)) (nfix n)))
   :rule-classes :linear))

(local
 (defthm fn-feed-attempts-belowp-after-a-transfer
   (implies (and (fn-feed-attempts-belowp xs n) (natp a) (< a (nfix n)))
            (fn-feed-attempts-belowp
             (fn-feed-queue-set-state xs msgid (list :sent a)) n))
   :rule-classes nil))

; The general form, for the replay fold: an offer state written with attempt
; `a' keeps the bound at any `m' above both `a' and the old bound.
(local
 (defthm fn-feed-attempts-belowp-of-an-offered-state
   (implies (and (fn-feed-attempts-belowp xs n) (natp a) (natp m)
                 (< a m) (<= (nfix n) m))
            (fn-feed-attempts-belowp
             (fn-feed-queue-set-state xs msgid (list :offered a)) m))
   :rule-classes nil))

; The same over the CONSTRUCTOR, for a proof that keeps `fn-feed-offered'
; closed: the replay fold's offer arm is such a proof.
(local
 (defthm fn-feed-attempts-belowp-of-an-offered-state-closed
   (implies (and (fn-feed-attempts-belowp xs n) (natp m)
                 (< (nfix a) m) (<= (nfix n) m))
            (fn-feed-attempts-belowp
             (fn-feed-queue-set-state xs msgid (fn-feed-offered a)) m))
   :rule-classes nil))

; The `:feed-sent' arm of the replay fold is the one place where the journal
; can name an attempt the live machine would never have written, and the
; arm's hypotheses are then CONTRADICTORY: `fn-feed-attempts-belowp' puts an
; in-flight entry's attempt strictly below the bound, and an `fn-feed-offeredp'
; entry is in flight, so a `(:feed-sent ... a)' record with `a' at or above
; `fn-feed-next-attempt' cannot be reached.  This is
; `fn-feed-inflight-attempt-is-below-the-bound' restated over `fn-bp-nth',
; which is what `fn-feed-state-attempt' opens to and what the arm's goal
; carries, and over `fn-feed-offeredp' rather than `fn-feed-state-inflightp',
; which the arm closes.
;
; `:rule-classes nil' and cited by `:use' at exactly that instance, DELIBERATELY:
; the same join supplied as a forward-chaining rule into the closed
; `fn-feed-state-inflightp' plus a `:linear' rule triggered on
; `fn-feed-state-of' fires under every arm of the dispatcher's case split and
; turned a 150 s certification into a runaway killed at the timeout with no
; checkpoint (run `run-20260920T191056Z-aa48`, recorded in
; planning/lanes/HANDOFF-w6-peering-feed.md and on the board).  Do not promote
; this to a rule.
(local
 (defthm fn-feed-sent-record-above-the-bound-is-unreachable
   (implies (and (fn-feed-attempts-belowp xs n)
                 (fn-feed-offeredp (fn-feed-state-of msgid xs)))
            (< (fn-bp-nth 1 (fn-feed-state-of msgid xs)) (nfix n)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-feed-inflight-attempt-is-below-the-bound))))))

(defthm fn-feed-offer-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (mv-nth 0 (fn-feed-offer f msgid))))
  :hints (("Goal"
           :use ((:instance fn-feed-attempts-belowp-after-an-offer
                            (xs (fn-feed-queue f))
                            (n (fn-feed-next-attempt f)))))))

(defthm fn-feed-send-preserves-feedp
  (implies (fn-feedp f)
           (fn-feedp (mv-nth 0 (fn-feed-send f msgid article))))
  :hints (("Goal"
           :use ((:instance fn-feed-inflight-attempt-is-below-the-bound
                            (xs (fn-feed-queue f))
                            (n (fn-feed-next-attempt f)))
                 (:instance fn-feed-attempts-belowp-after-a-transfer
                            (xs (fn-feed-queue f))
                            (n (fn-feed-next-attempt f))
                            (a (fn-feed-state-attempt
                                (fn-feed-state-of
                                 msgid (fn-feed-queue f)))))))))

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

; The dispatcher stays open and every arm stays CLOSED: each arm is one of
; the transitions above and its preservation lemma is the rewrite that closes
; it.  Opening the arms instead put the proof into a 137-way split
; (`fn-feed-give-up' and `fn-feed-retry-exhaustedp' under every code).
(defthm fn-feed-observe-preserves-feedp
  (implies (fn-feedp f)
           (fn-feedp (mv-nth 0 (fn-feed-observe f response article obs))))
  :hints (("Goal" :in-theory (disable (:d fn-feed-offer) (:d fn-feed-send) (:d fn-feed-done)
                            (:d fn-feed-back-off) (:d fn-feed-lost)
                            (:d fn-feed-give-up) (:d fn-feed-enqueue)
                            (:d fn-feed-restart)
                            (:d fn-feed-retry-exhaustedp) (:d fn-feedp)
                            ; `mv-nth' too: opened, it turns the arm into
                            ; `(car (fn-feed-send ...))' and the arm's
                            ; preservation rewrite no longer matches.
                            mv-nth))))

(defthm fn-feed-tick-step-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (mv-nth 0 (fn-feed-tick-step f obs))))
  :hints (("Goal" :in-theory (disable (:d fn-feed-offer) (:d fn-feed-send) (:d fn-feed-done)
                            (:d fn-feed-back-off) (:d fn-feed-lost)
                            (:d fn-feed-give-up) (:d fn-feed-enqueue)
                            (:d fn-feed-restart)
                            (:d fn-feed-retry-exhaustedp) (:d fn-feedp)
                            ; `mv-nth' too: opened, it turns the arm into
                            ; `(car (fn-feed-send ...))' and the arm's
                            ; preservation rewrite no longer matches.
                            mv-nth))))

; `fn-feedp' stays OPEN here, unlike the three above: the `:feed-offer' and
; `:feed-outcome' arms rebuild the record with `fn-feed-make' instead of
; calling a transition, so the recognizer has to open on both sides -- closed,
; the prover could not even see that `(fn-feedp f)' contradicts
; `(not (fn-feed-attempts-belowp (fn-feed-queue f) (fn-feed-next-attempt f)))'.
(defthm fn-feed-apply-record-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-apply-record f kind values)))
  :hints (("Goal"
           ; The state vocabulary is closed too: with `fn-feed-state-of',
           ; the three offer-state predicates and their constructors open,
           ; the `:feed-sent' arm's hypotheses become
           ; `consp'/`car'/`true-listp'/`len' of the found entry's state and
           ; neither `fn-feed-inflight-count-of-set-state-exact' nor
           ; `fn-feed-find-is-consp-when-the-state-is-a-state' can match.
           ; Closing them is docs/proof-style.md sec. 1, not an opening of
           ; `fn-feedp' -- which stays open, for the reason above.
           :in-theory (disable (:d fn-feed-offer) (:d fn-feed-send) (:d fn-feed-done)
                            (:d fn-feed-back-off) (:d fn-feed-lost)
                            (:d fn-feed-give-up) (:d fn-feed-enqueue)
                            (:d fn-feed-restart)
                            (:d fn-feed-retry-exhaustedp)
                            (:d fn-feed-state-of) (:d fn-feed-offeredp)
                            (:d fn-feed-sentp) (:d fn-feed-droppedp)
                            (:d fn-feed-state-inflightp)
                            (:d fn-feed-offered) (:d fn-feed-sent)
                            (:d fn-feed-dropped)
                            mv-nth)
           :use ((:instance fn-feed-attempts-belowp-of-an-offered-state-closed
                            (xs (fn-feed-queue f))
                            (n (fn-feed-next-attempt f))
                            (msgid (fn-feed-record-msgid values))
                            (a (fn-feed-record-nat 2 values))
                            (m (if (< (fn-feed-record-nat 2 values)
                                      (fn-feed-next-attempt f))
                                   (fn-feed-next-attempt f)
                                   (+ 1 (fn-feed-record-nat 2 values)))))
                 (:instance fn-feed-sent-record-above-the-bound-is-unreachable
                            (xs (fn-feed-queue f))
                            (n (fn-feed-next-attempt f))
                            (msgid (fn-frame-item 1 values)))))))

; The fold over the journal, and the same discipline as the three composite
; theorems above: the fold stays OPEN (it is the induction) and the record
; step stays CLOSED, so `fn-feed-apply-record-preserves-feedp' is the rewrite
; that carries the recognizer across one record.  Measured on 2026-09-20: with
; `fn-feed-apply-record' open the induction step re-splits the dispatcher
; under every arm and the form did not finish in 1800 s (run
; `run-20260920T200246Z-fa0b'); closed, it is seconds.  `fn-feedp' is closed
; with it, or the keystone's conclusion cannot match.
(defthm fn-feed-replay-preserves-feedp
  (implies (fn-feedp f) (fn-feedp (fn-feed-replay f es)))
  :hints (("Goal" :in-theory (disable (:d fn-feed-apply-record) (:d fn-feedp)))))

; -----------------------------------------------------------------------------
; Preservation: the peer name
;
; Every transition either returns the feed unchanged or rebuilds it with
; `fn-feed-make' on `(fn-feed-peer f)', directly or through one of the four
; field updates, so each equation below is UNCONDITIONAL -- `fn-feedp' is not
; needed and has no violating value, so it is not stated (the micro
; discipline's fourth rule).  These are the rewrites the two dispatcher
; theorems after them run on: with the transitions closed -- which is what
; keeps the dispatcher's case split from re-splitting under every arm --
; nothing else can reduce `(fn-feed-peer (fn-feed-give-up f ...))', and that
; is the `Subgoal 40'' the previous lane measured.  The six single-valued
; members (`enqueue', `done', `back-off', `lost', `give-up', `restart') came
; from lane w6/peering-inbound-2 on dev at `ca1ce5d' and are kept here, in
; one block with the four field updates and the two `mv' transitions, so the
; family is read in one place; the four `fn-feed-peer-of-with-*' equations
; make each proof a rewrite rather than an `e/d' per form.
;
; The eleven transition members and the four field equations are PROOF
; VOCABULARY and are withdrawn at the end of this book under
; `fn-feed-invariants-vocabulary' (docs/proof-style.md sec. 2 and 8).
; Exported enabled they are a rule an includer has to disable: measured on
; persvati `run-20260920T211802Z-ba78', `fn-feed-tick-step-preserves-peer'
; fired on the `:use'd hypothesis of `books/owner-feed's
; `fn-own-feed-tick-step-keeps-the-feed-half', rewrote it to T, and left
; that proof with a conclusion in `car' vocabulary and nothing to close it.
; What leaves this book enabled is the two DISPATCHER members,
; `fn-feed-apply-record-preserves-peer' and `fn-feed-replay-preserves-peer',
; which are what an includer folding a journal actually needs.  An includer
; that wants one of the eleven enables the vocabulary name in the one hint
; that needs it and deletes its local twin.

(defthm fn-feed-peer-of-with-queue
  (equal (fn-feed-peer (fn-feed-with-queue f queue)) (fn-feed-peer f)))
(defthm fn-feed-peer-of-with-conn
  (equal (fn-feed-peer (fn-feed-with-conn f conn)) (fn-feed-peer f)))
(defthm fn-feed-peer-of-with-contact
  (equal (fn-feed-peer (fn-feed-with-contact f contact)) (fn-feed-peer f)))
(defthm fn-feed-peer-of-with-backoff
  (equal (fn-feed-peer (fn-feed-with-backoff f until)) (fn-feed-peer f)))

(defthm fn-feed-enqueue-preserves-peer
  (equal (fn-feed-peer (fn-feed-enqueue f msgid tick)) (fn-feed-peer f)))
(defthm fn-feed-offer-preserves-peer
  (equal (fn-feed-peer (mv-nth 0 (fn-feed-offer f msgid))) (fn-feed-peer f)))
(defthm fn-feed-send-preserves-peer
  (equal (fn-feed-peer (mv-nth 0 (fn-feed-send f msgid article)))
         (fn-feed-peer f)))
(defthm fn-feed-done-preserves-peer
  (equal (fn-feed-peer (fn-feed-done f msgid)) (fn-feed-peer f)))
(defthm fn-feed-back-off-preserves-peer
  (equal (fn-feed-peer (fn-feed-back-off f msgid obs)) (fn-feed-peer f)))
(defthm fn-feed-lost-preserves-peer
  (equal (fn-feed-peer (fn-feed-lost f obs)) (fn-feed-peer f)))
(defthm fn-feed-give-up-preserves-peer
  (equal (fn-feed-peer (fn-feed-give-up f msgid reason)) (fn-feed-peer f)))
(defthm fn-feed-restart-preserves-peer
  (equal (fn-feed-peer (fn-feed-restart f)) (fn-feed-peer f)))
(defthm fn-feed-settle-preserves-peer
  (equal (fn-feed-peer (fn-feed-settle f)) (fn-feed-peer f)))

(defthm fn-feed-observe-preserves-peer
  (equal (fn-feed-peer (mv-nth 0 (fn-feed-observe f response article obs)))
         (fn-feed-peer f))
  :hints (("Goal" :in-theory (disable (:d fn-feed-offer) (:d fn-feed-send) (:d fn-feed-done)
                            (:d fn-feed-back-off) (:d fn-feed-lost)
                            (:d fn-feed-give-up) (:d fn-feed-enqueue)
                            (:d fn-feed-restart)
                            (:d fn-feed-retry-exhaustedp) (:d fn-feedp)
                            mv-nth))))

(defthm fn-feed-tick-step-preserves-peer
  (equal (fn-feed-peer (mv-nth 0 (fn-feed-tick-step f obs)))
         (fn-feed-peer f))
  :hints (("Goal" :in-theory (disable (:d fn-feed-offer) (:d fn-feed-send) (:d fn-feed-done)
                            (:d fn-feed-back-off) (:d fn-feed-lost)
                            (:d fn-feed-give-up) (:d fn-feed-enqueue)
                            (:d fn-feed-restart)
                            (:d fn-feed-retry-exhaustedp) (:d fn-feedp)
                            (:d fn-feed-selection) mv-nth))))

; The dispatcher.  `fn-feedp' is not a hypothesis here either: the record
; step returns the feed unchanged when it does not recognize it.
(defthm fn-feed-apply-record-preserves-peer
  (equal (fn-feed-peer (fn-feed-apply-record f kind values))
         (fn-feed-peer f))
  :hints (("Goal" :in-theory (disable (:d fn-feed-offer) (:d fn-feed-send) (:d fn-feed-done)
                            (:d fn-feed-back-off) (:d fn-feed-lost)
                            (:d fn-feed-give-up) (:d fn-feed-enqueue)
                            (:d fn-feed-restart)
                            (:d fn-feed-retry-exhaustedp) (:d fn-feedp)
                            mv-nth))))

; The same closure, for the same reason: the record-step keystone above is
; the rewrite, and it only matches with the step closed.
(defthm fn-feed-replay-preserves-peer
  (equal (fn-feed-peer (fn-feed-replay f es)) (fn-feed-peer f))
  :hints (("Goal" :in-theory (disable (:d fn-feed-apply-record) (:d fn-feedp)))))

; -----------------------------------------------------------------------------
; KEYSTONE: replay is a fold, so it is deterministic and order is all that
; matters -- replaying a journal in two pieces is replaying it whole.

; The same one-line closure as the two folds above: the fold is the
; induction and the record step is an opaque function of the feed, so the
; induction step is `(fn-feed-replay (step f e) (append es fs))' and the
; induction hypothesis closes it.  With the step OPEN the dispatcher
; re-splits under every arm and the induction does not finish
; (`Subgoal *1/2.490.3', measured 2026-09-20).
(defthm fn-feed-replay-is-the-fold
  (equal (fn-feed-replay f (append es fs))
         (fn-feed-replay (fn-feed-replay f es) fs))
  :hints (("Goal" :in-theory (disable (:d fn-feed-apply-record))
           :induct (fn-feed-replay f es))))

; -----------------------------------------------------------------------------
; KEYSTONE: a finished entry is never offered again
;
; `fn-feed-tick-step' is the function the host calls once per scheduler tick.
; Its only effect is one `:command' offering the selection, and the selection
; is a `:queued' entry, so an entry that is `:done' or `(:dropped r)' is never
; the subject of a command.

; `(:d fn-feed-state-of)' is closed for the reason the whole cluster keeps
; relearning: `fn-feed-head-queued-is-queued' is keyed on
; `(fn-feed-state-of (fn-feed-head-queued xs) xs)', and with the definition
; open the conclusion becomes
; `(fn-feed-entry-state (fn-feed-find (fn-feed-head-queued ...) ...))'
; before the rule can fire -- which is exactly the `Subgoal 6'' the previous
; lane measured.  Distinctness, which the rule needs, comes from `fn-feedp',
; which stays open.
(defthm fn-feed-selection-is-queued
  (implies (and (fn-feedp f) (fn-feed-selection f obs))
           (equal (fn-feed-state-of (fn-feed-selection f obs)
                                    (fn-feed-queue f))
                  :queued))
  :hints (("Goal" :in-theory (disable (:d fn-feed-state-of)))))

; `(fn-feed-selection f obs)' is a HYPOTHESIS, and it is not decoration: the
; statement without it is FALSE, and the prover found the counterexample --
; `Subgoal 73'', measured 2026-09-20 in lane w6/peering-feed-4.  Take
; `msgid' to be NIL and a feed with no selectable entry (no connection, say).
; Then `(fn-feed-selection f obs)' is NIL, `(fn-feed-state-of nil
; (fn-feed-queue f))' is NIL and so is not `:queued', and the conclusion
; `(not (equal nil nil))' is false.  Nothing is offered in that state, which
; is what `fn-feed-tick-step-is-silent-without-a-selection' says, so the
; hypothesis holds on exactly the states where the keystone has content: the
; ones where the host emits a command.  `fn-feed-tick-step-offers-the-
; selection' already carries the same hypothesis, so the pair composes
; unchanged.
(defthm fn-feed-done-is-never-selected
  (implies (and (fn-feedp f)
                (fn-feed-selection f obs)
                (not (equal (fn-feed-state-of msgid (fn-feed-queue f))
                            :queued)))
           (not (equal (fn-feed-selection f obs) msgid)))
  :hints (("Goal" :use ((:instance fn-feed-selection-is-queued))
           :in-theory (disable fn-feed-selection-is-queued
                               (:d fn-feed-state-of)))))

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

; No `fn-feedp' hypothesis: it has no violating value, which the micro
; discipline's fourth rule says is a hypothesis to delete rather than to
; decorate.  `fn-feed-send' refuses a feed it does not recognize on its own,
; and `fn-feed-restart' returns such a feed unchanged, so both sides are nil
; there too.  Measured 2026-09-20: the tooth in the test book asserted the
; opposite -- that a forged two-in-flight feed still emits a transfer -- and
; had never been evaluated, because the root had no certificate.
(defthm fn-feed-restart-emits-no-transfer
  (equal (mv-nth 1 (fn-feed-send (fn-feed-restart f) msgid article))
         nil)
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

; The offer-state vocabulary is closed at every form from here to the end of
; the book, and nothing else is: the dispatcher and its arms stay OPEN (this
; is a theorem about ONE record, so the case split is the content), and the
; queue lemmas above -- `fn-feed-state-of-of-set-state-other',
; `-of-settle-when-not-inflight', `fn-feed-find-of-append-when-present' --
; are stated in that vocabulary and can only match while it is closed.  With
; it open the goal reaches `fn-feed-entry-state' of `fn-feed-find' of
; `fn-feed-queue-settle' and no rule applies (`Subgoal 103.59''').
(defthm fn-feed-done-survives-a-driven-record
  (implies (and (fn-feedp f)
                (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done)
                (fn-feed-record-drivenp f kind values))
           (equal (fn-feed-state-of
                   msgid (fn-feed-queue (fn-feed-apply-record f kind values)))
                  :done))
  :hints (("Goal"
           ; Whether the record names THIS entry is the content, and the
           ; prover cannot get the disequality by itself: in the arms that
           ; write a state, `fn-feed-record-drivenp' says the written entry
           ; is `:queued', in flight, or not `:done', while this one is
           ; `:done' -- joining those two is a case split, not a rewrite.
           ; Split once here and every arm closes from the queue lemmas.
           :cases ((equal msgid (fn-feed-record-msgid values)))
           :in-theory (disable (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped)))))

; Stated over the journal ENTRY, not over a loose `(kind values)' pair: the
; fold's induction step carries `(car es)', and a rule whose conclusion is
; `(not (equal kind :feed-outcome))' has `f' and `msgid' free, so it never
; fires there (ACL2 says so: `Warning [Free]').  Same content -- a driven
; record cannot be an accepted outcome for an entry that is already `:done',
; because only an in-flight entry admits an outcome -- in the shape the
; keystone below needs.
(defthm fn-feed-done-is-not-an-accepted-outcome-record
  (implies (and (fn-feedp f)
                (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done)
                (fn-feed-record-drivenp f (fn-feed-journal-kind e)
                                        (fn-feed-journal-values e)))
           (not (fn-feed-accepted-outcomep (fn-feed-peer f) msgid e)))
  :hints (("Goal" :in-theory (disable (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped)))))

(defthm fn-feed-done-means-no-more-accepted-outcomes
  (implies (and (fn-feedp f)
                (equal (fn-feed-state-of msgid (fn-feed-queue f)) :done)
                (fn-feed-drivenp f es))
           (and (equal (fn-feed-state-of
                        msgid (fn-feed-queue (fn-feed-replay f es)))
                       :done)
                (equal (fn-feed-count-accepted (fn-feed-peer f) msgid es) 0)))
  :hints (("Goal" :induct (fn-feed-drivenp f es)
           :in-theory (disable (:d fn-feed-apply-record)
                               (:d fn-feed-record-drivenp) (:d fn-feedp)
                               (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped)))))

; Over the journal ENTRY, for the same reason as the lemma above: the fold
; carries `(car es)', and a statement over a loose `(kind values)' pair asks
; the prover for `(fn-feed-journal-entry (fn-feed-journal-kind e)
; (fn-feed-journal-values e)) = e', which is true only for a well-formed
; entry and is not the content of anything here.
(defthm fn-feed-accepted-outcome-makes-it-done
  (implies (and (fn-feedp f)
                (fn-feed-record-drivenp f (fn-feed-journal-kind e)
                                        (fn-feed-journal-values e))
                (fn-feed-accepted-outcomep (fn-feed-peer f) msgid e))
           (equal (fn-feed-state-of
                   msgid
                   (fn-feed-queue
                    (fn-feed-apply-record f (fn-feed-journal-kind e)
                                          (fn-feed-journal-values e))))
                  :done))
  :hints (("Goal" :in-theory (disable (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped)))))

; The head step of the keystone below, and the one thing its induction
; cannot do by itself.  In the arm where the head record IS an accepted
; outcome for this (peer, Message-ID), the induction hypothesis gives only
; `<= 1' over the tail, and one plus one is two; what closes it is that the
; head makes the entry `:done', after which the tail holds NO accepted
; outcome at all.  Chaining those two is a `:use' of the two theorems above
; at one instance, not a rule: stated as a rewrite on the tail's count, with
; the two named instances cited, so nothing new fires anywhere else.  It is
; `local' and it is the whole content of `Subgoal *1/2.3''''.
(local
 (defthm fn-feed-count-accepted-after-an-accepted-head
   (implies (and (fn-feedp f)
                 (fn-feed-record-drivenp f (fn-feed-journal-kind (car es))
                                         (fn-feed-journal-values (car es)))
                 (fn-feed-drivenp
                  (fn-feed-apply-record f (fn-feed-journal-kind (car es))
                                        (fn-feed-journal-values (car es)))
                  (cdr es))
                 (fn-feed-accepted-outcomep (fn-feed-peer f) msgid (car es)))
            (equal (fn-feed-count-accepted (fn-feed-peer f) msgid (cdr es))
                   0))
   :hints (("Goal"
            :use ((:instance fn-feed-accepted-outcome-makes-it-done
                             (e (car es)))
                  (:instance fn-feed-done-means-no-more-accepted-outcomes
                             (f (fn-feed-apply-record
                                 f (fn-feed-journal-kind (car es))
                                 (fn-feed-journal-values (car es))))
                             (es (cdr es))))
            :in-theory (disable fn-feed-accepted-outcome-makes-it-done
                                fn-feed-done-means-no-more-accepted-outcomes
                                (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped))))))

(defthm fn-feed-at-most-one-accepted-outcome
  (implies (and (fn-feedp f) (fn-feed-drivenp f es))
           (<= (fn-feed-count-accepted (fn-feed-peer f) msgid es) 1))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-feed-drivenp f es)
           :in-theory (disable (:d fn-feed-apply-record)
                               (:d fn-feed-record-drivenp) (:d fn-feedp)
                               (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped)))))

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
                  (fn-feed-queue (fn-feed-apply-record f kind values))))))
  :hints (("Goal" :in-theory (disable (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped)))))

(defthm fn-feed-drop-needs-a-drop-record
  (implies (and (fn-feedp f)
                (not (fn-feed-droppedp (fn-feed-state-of msgid
                                                         (fn-feed-queue f))))
                (fn-feed-droppedp
                 (fn-feed-state-of msgid
                                   (fn-feed-queue (fn-feed-replay f es)))))
           (fn-feed-has-drop-recordp (fn-feed-peer f) msgid es))
  :hints (("Goal" :induct (fn-feed-replay f es)
           :in-theory (disable (:d fn-feed-apply-record) (:d fn-feedp)
                               (:d fn-feed-state-of) (:d fn-feed-offeredp)
                               (:d fn-feed-sentp) (:d fn-feed-droppedp)
                               (:d fn-feed-state-inflightp)
                               (:d fn-feed-offered) (:d fn-feed-sent)
                               (:d fn-feed-dropped)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md sec. 2)

(deftheory fn-feed-invariants-vocabulary
  '(fn-feed-state-of-of-set-state-same fn-feed-state-of-of-set-state-other
    fn-feed-state-of-of-requeue-other
    fn-feed-find-of-append-when-present
    fn-feed-state-of-of-append-when-present
    fn-feed-state-of-of-requeue-same
    fn-feed-state-of-of-requeue-inflight-when-inflight
    fn-feed-state-of-of-settle-when-inflight
    fn-feed-droppedp-of-the-offer-states
    fn-feed-droppedp-of-state-of-set-state
    fn-feed-droppedp-of-state-of-requeue
    fn-feed-droppedp-of-state-of-requeue-inflight
    fn-feed-droppedp-of-state-of-settle
    fn-feed-droppedp-of-state-of-append-one
    fn-feed-peer-of-with-queue fn-feed-peer-of-with-conn
    fn-feed-peer-of-with-contact fn-feed-peer-of-with-backoff
    fn-feed-enqueue-preserves-peer fn-feed-offer-preserves-peer
    fn-feed-send-preserves-peer fn-feed-done-preserves-peer
    fn-feed-back-off-preserves-peer fn-feed-lost-preserves-peer
    fn-feed-give-up-preserves-peer fn-feed-restart-preserves-peer
    fn-feed-settle-preserves-peer fn-feed-observe-preserves-peer
    fn-feed-tick-step-preserves-peer
    fn-feed-state-of-of-requeue-inflight-when-not-inflight
    fn-feed-state-of-of-settle-when-not-inflight
    fn-feed-find-of-append-when-absent
    fn-feed-head-queued-is-in-msgids fn-feed-find-of-a-member-is-consp
    fn-feed-find-is-consp-when-the-state-is-a-state
    fn-feed-inflight-count-of-set-state-from-queued
    fn-feed-head-queued-is-queued fn-feed-head-queued-is-a-member
    fn-feed-inflight-count-of-settle fn-feed-inflight-count-of-requeue-inflight
    fn-feed-entry-listp-of-set-state fn-feed-entry-listp-of-requeue
    fn-feed-entry-listp-of-requeue-inflight fn-feed-entry-listp-of-settle
    fn-feed-msgids-of-set-state fn-feed-msgids-of-requeue
    fn-feed-msgids-of-requeue-inflight fn-feed-msgids-of-settle
    fn-feed-state-okp-of-offered fn-feed-state-okp-of-sent
    fn-feed-state-okp-of-dropped fn-feed-inflight-count-of-set-state-exact
    fn-feed-state-inflightp-of-offered fn-feed-state-inflightp-of-sent
    fn-feed-state-inflightp-of-dropped
    fn-feed-state-attempt-of-offered fn-feed-state-attempt-of-sent
    fn-feed-offer-states-forward-consp fn-feed-offer-states-forward-natp
    fn-feed-attempts-belowp-of-set-state-open-inflight
    fn-feed-attempts-belowp-monotone
    fn-feed-attempts-belowp-of-set-state-inflight
    fn-feed-msgids-of-append fn-feed-member-of-append
    fn-feed-not-member-when-find-is-not-consp
    fn-feed-entry-listp-of-append-one fn-feed-distinctp-of-append-one
    fn-feed-inflight-count-of-append-one
    fn-feed-attempts-belowp-of-append-one fn-feed-len-of-append-one
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
