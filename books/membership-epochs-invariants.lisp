; Keystones for the membership-epoch admissibility policy.
;
; The four properties C3-08 asks for, in the order they appear below:
;
;   1. A revoked member's post-revocation messages are never admitted once the
;      revocation epoch is known locally, and that refusal SURVIVES learning
;      more (`fn-me-revoked-refusal-is-monotone`).  The content is
;      `fn-me-revoked-scan-stable-under-prefix`: the first removal of a member
;      in an adopted chain is the first removal in every extension of it.
;   2. A message from an epoch the site has not reached is held, not dropped,
;      and the hold is bounded (`fn-me-ahead-message-is-held`,
;      `fn-me-hold-count-bounded`), and a held message has a future
;      (`fn-me-hold-resolves-on-reaching-epoch`).
;   3. The decision is monotone in local knowledge: refusal on revocation
;      grounds is upward closed, adoption extends knowledge, and merging a
;      peer's evidence revises no verdict at all.
;   4. The partition merge is a set union of commits with explicit conflict
;      evidence: the ids of a merge are exactly the union of the two id sets,
;      the union is order independent as an id set, two commits premised on the
;      same epoch both survive the merge and are reported as a fork, and
;      `fn-me-site-merge` never revises the adopted chain.  That last one is
;      what "never last-writer-wins" means as a theorem rather than a slogan.
;
; None of these is a cryptographic claim.  See the header of
; books/membership-epochs.lisp for what the model assumes rather than proves.

(in-package "ACL2")
(include-book "membership-epochs")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; List plumbing

(defthm fn-me-len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-me-member-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b))))

(defthm fn-me-member-of-remove-equal
  (implies (not (member-equal m r))
           (not (member-equal m (remove-equal s r)))))

(defthm fn-me-commit-ids-of-append
  (equal (fn-me-commit-ids (append a b))
         (append (fn-me-commit-ids a) (fn-me-commit-ids b))))

; -----------------------------------------------------------------------------
; 1. Revocation

; The first `:remove` of a member in a chain is the first `:remove` of that
; member in every chain that extends it.  This is the whole reason a refusal
; on revocation grounds can be permanent under disconnection: a site that later
; learns more of the chain computes the same revocation epoch, never a later
; one and never none.
(local
 (defun fn-me-revoked-induct (a b member index)
   (declare (xargs :guard t :measure (acl2-count a)))
   (if (consp a)
       (fn-me-revoked-induct (cdr a) (cdr b) member (+ 1 (nfix index)))
     (list a b member index))))

(defthm fn-me-revoked-scan-stable-under-prefix
  (implies (and (fn-me-chain-prefixp a b)
                (< 0 (fn-me-revoked-scan a member index)))
           (equal (fn-me-revoked-scan b member index)
                  (fn-me-revoked-scan a member index)))
  :hints (("Goal" :induct (fn-me-revoked-induct a b member index))))

; A member the site knows was removed at epoch r is absent from every roster
; the site computes from a chain segment that does not add it back.  The
; re-admission policy of the definitions book is exactly what makes the
; hypothesis `(not (fn-me-addsp member chain))` discharegable for the segment
; after r.
(defthm fn-me-roster-fold-omits-removed
  (implies (and (not (fn-me-addsp member chain))
                (not (member-equal member roster)))
           (not (member-equal member (fn-me-roster-fold roster chain)))))

; The direct statement: once the revocation epoch is known locally, no message
; the revoked member produced at or after it is admitted.
(defthm fn-me-revoked-sender-is-not-admitted
  (implies (and (fn-me-sitep site)
                (fn-me-messagep msg)
                (< 0 (fn-me-revoked-at site (fn-me-msg-sender msg)))
                (<= (fn-me-revoked-at site (fn-me-msg-sender msg))
                    (fn-me-msg-epoch msg)))
           (not (equal (fn-me-decide site msg) :admit))))

; And the monotone form: a site that knows strictly more still refuses.  This
; is the property a disconnected deployment needs, because the refusing site
; will keep receiving chain segments for months afterwards.
(defthm fn-me-revoked-refusal-is-monotone
  (implies (and (fn-me-sitep a)
                (fn-me-sitep b)
                (fn-me-messagep msg)
                (fn-me-knowledge-extendsp a b)
                (< 0 (fn-me-revoked-at a (fn-me-msg-sender msg)))
                (<= (fn-me-revoked-at a (fn-me-msg-sender msg))
                    (fn-me-msg-epoch msg)))
           (equal (fn-me-decide b msg) :refuse))
  :hints (("Goal"
           :use ((:instance fn-me-revoked-scan-stable-under-prefix
                            (a (fn-me-chain a))
                            (b (fn-me-chain b))
                            (member (fn-me-msg-sender msg))
                            (index 0))))))

; -----------------------------------------------------------------------------
; 2. Bounded hold

(defthm fn-me-decide-outcome
  (implies (and (fn-me-sitep site) (fn-me-messagep msg))
           (member-equal (fn-me-decide site msg) *fn-me-outcomes*)))

(defthm fn-me-receive-preserves-sitep
  (implies (and (fn-me-sitep site) (fn-me-messagep msg))
           (fn-me-sitep (fn-me-receive site msg))))

(defthm fn-me-receive-preserves-chain
  (implies (and (fn-me-sitep site) (fn-me-messagep msg))
           (equal (fn-me-chain (fn-me-receive site msg))
                  (fn-me-chain site))))

; A message from an epoch the site has not reached is retained, not dropped:
; it is a member of the held list afterwards and the held count grows by
; exactly one.
(defthm fn-me-ahead-message-is-held
  (implies (and (fn-me-sitep site)
                (fn-me-messagep msg)
                (equal (fn-me-decide site msg) :hold))
           (and (member-equal msg (fn-me-held (fn-me-receive site msg)))
                (equal (len (fn-me-held (fn-me-receive site msg)))
                       (+ 1 (len (fn-me-held site)))))))

; The hold is bounded: a site whose held count is within its limit still is
; after receiving anything at all.  This is RFC 9420 section 15.3's "maximum
; number to keep" as a state invariant rather than as advice.
(defthm fn-me-hold-count-bounded
  (implies (and (fn-me-sitep site)
                (fn-me-messagep msg)
                (<= (len (fn-me-held site)) (fn-me-hold-limit site)))
           (<= (len (fn-me-held (fn-me-receive site msg)))
               (fn-me-hold-limit site))))

; A held message has a future.  A site that has reached the message's epoch,
; is still inside its window, knows of no revocation of the sender and finds
; the sender on the roster of that very epoch, admits it.  Each hypothesis has
; a `must-fail` case in the test book.
(defthm fn-me-hold-resolves-on-reaching-epoch
  (implies (and (fn-me-sitep a)
                (fn-me-sitep b)
                (fn-me-messagep msg)
                (equal (fn-me-decide a msg) :hold)
                (<= (fn-me-msg-epoch msg) (fn-me-epoch b))
                (<= (fn-me-epoch b) (+ (fn-me-msg-epoch msg) (fn-me-window b)))
                (equal (fn-me-revoked-at b (fn-me-msg-sender msg)) 0)
                (member-equal (fn-me-msg-sender msg)
                              (fn-me-roster-at b (fn-me-msg-epoch msg))))
           (and (member-equal msg (fn-me-held (fn-me-receive a msg)))
                (equal (fn-me-decide b msg) :admit))))

; -----------------------------------------------------------------------------
; 3. Monotonicity of knowledge

(defthm fn-me-chain-prefixp-of-append
  (fn-me-chain-prefixp a (append a b)))

(defthm fn-me-adopt-extends-chain
  (implies (and (fn-me-sitep site) (fn-me-commitp commit))
           (fn-me-chain-prefixp (fn-me-chain site)
                                (fn-me-chain (fn-me-adopt site commit)))))

(defthm fn-me-adopt-advances-epoch
  (implies (and (fn-me-sitep site)
                (fn-me-commitp commit)
                (equal (fn-me-commit-base commit) (fn-me-epoch site)))
           (equal (fn-me-epoch (fn-me-adopt site commit))
                  (+ 1 (fn-me-epoch site)))))

; -----------------------------------------------------------------------------
; 4. The partition merge

(defthm fn-me-merge-keeps-left-ids
  (implies (member-equal id (fn-me-commit-ids a))
           (member-equal id (fn-me-commit-ids (fn-me-merge a b)))))

(defthm fn-me-new-keeps-unknown-ids
  (implies (and (member-equal id (fn-me-commit-ids b))
                (not (member-equal id (fn-me-commit-ids a))))
           (member-equal id (fn-me-commit-ids (fn-me-new a b)))))

(defthm fn-me-merge-keeps-right-ids
  (implies (member-equal id (fn-me-commit-ids b))
           (member-equal id (fn-me-commit-ids (fn-me-merge a b)))))

(defthm fn-me-new-ids-come-from-delta
  (implies (member-equal id (fn-me-commit-ids (fn-me-new a b)))
           (member-equal id (fn-me-commit-ids b))))

(defthm fn-me-merge-invents-no-ids
  (implies (member-equal id (fn-me-commit-ids (fn-me-merge a b)))
           (or (member-equal id (fn-me-commit-ids a))
               (member-equal id (fn-me-commit-ids b))))
  :rule-classes nil)

; The observable of the merge does not depend on which side a site happened to
; be.  Two partitioned sites that exchange commit sets in either direction see
; the same ids; the set union is the CRDT observable, as in books/lace.lisp.
(defthm fn-me-merge-ids-are-order-independent
  (implies (member-equal id (fn-me-commit-ids (fn-me-merge a b)))
           (member-equal id (fn-me-commit-ids (fn-me-merge b a))))
  :hints (("Goal" :use ((:instance fn-me-merge-invents-no-ids)))))

; Conflict evidence.

(defthm fn-me-commitsp-of-merge
  (implies (and (fn-me-commitsp a) (fn-me-commitsp b))
           (fn-me-commitsp (fn-me-merge a b))))

; `fn-me-conflict-with` reports the conflicting commit itself, so the list has
; to be commits: a `nil` element would be a conflict that reads as none found.
(defthm fn-me-conflict-with-finds-a-conflict
  (implies (and (fn-me-commitsp commits)
                (member-equal other commits)
                (equal (fn-me-commit-base other) (fn-me-commit-base c))
                (not (equal (fn-me-commit-id other) (fn-me-commit-id c))))
           (fn-me-conflict-with c commits)))

(defthm fn-me-fork-scan-detects-a-conflict
  (implies (and (member-equal c rest)
                (fn-me-conflict-with c commits))
           (fn-me-fork-scan rest commits)))

(defthm fn-me-new-retains-unknown-commits
  (implies (and (member-equal c delta)
                (not (member-equal (fn-me-commit-id c) (fn-me-commit-ids commits))))
           (member-equal c (fn-me-new commits delta))))

; The partition property.  Two sites partitioned at the same epoch each adopt a
; different commit; when their evidence sets meet, BOTH commits are still
; there and the merge reports the fork.  Nothing picked a winner, and no
; timestamp was consulted.
(defthm fn-me-merge-exposes-the-partition
  (implies (and (fn-me-commitsp a)
                (fn-me-commitsp b)
                (member-equal ca a)
                (member-equal cb b)
                (equal (fn-me-commit-base ca) (fn-me-commit-base cb))
                (not (equal (fn-me-commit-id ca) (fn-me-commit-id cb)))
                (not (member-equal (fn-me-commit-id cb) (fn-me-commit-ids a))))
           (and (member-equal ca (fn-me-merge a b))
                (member-equal cb (fn-me-merge a b))
                (fn-me-forkedp (fn-me-merge a b))))
  :hints (("Goal"
           :use ((:instance fn-me-conflict-with-finds-a-conflict
                            (c ca) (other cb) (commits (fn-me-merge a b)))
                 (:instance fn-me-fork-scan-detects-a-conflict
                            (c ca) (rest (fn-me-merge a b))
                            (commits (fn-me-merge a b)))
                 (:instance fn-me-new-retains-unknown-commits
                            (c cb) (delta b) (commits a))))))

; And the anti-last-writer-wins property: taking a peer's evidence changes the
; evidence set and NOTHING else.  No adopted chain, no epoch, and no
; admissibility verdict moves because a batch arrived.
(defthm fn-me-site-merge-preserves-sitep
  (implies (and (fn-me-sitep site) (fn-me-commitsp delta))
           (fn-me-sitep (fn-me-site-merge site delta))))

(defthm fn-me-site-merge-preserves-chain
  (implies (and (fn-me-sitep site) (fn-me-commitsp delta))
           (and (equal (fn-me-chain (fn-me-site-merge site delta))
                       (fn-me-chain site))
                (equal (fn-me-epoch (fn-me-site-merge site delta))
                       (fn-me-epoch site)))))

(defthm fn-me-site-merge-never-revises-admissibility
  (implies (and (fn-me-sitep site)
                (fn-me-commitsp delta)
                (fn-me-messagep msg))
           (equal (fn-me-decide (fn-me-site-merge site delta) msg)
                  (fn-me-decide site msg))))
