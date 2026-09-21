; fn: the monotone-anchor rule for restore, clone and incarnation advance.
;
; The keystones here are the four facts FLR-003 and D10 ask for:
;
;   fn-anchor-accepted-anchor-is-strictly-newer   a node never accepts an
;       anchor that is not strictly later than the one it already holds
;   fn-anchor-accept-list-latest-never-goes-back  and therefore its durable
;       anchor is monotone across any sequence of responses
;   fn-anchor-restore-refuses-image-it-cannot-outdate   an image whose newest
;       referenced anchor is not outdated by the presented anchor is refused,
;       with `:possibly-stale' as its own reason
;   fn-anchor-fork-admits-neither-image            two images of one
;       incarnation with different newest anchors are both refused, and the
;       outcome carries both of them
;
; Every one of them is conditional on `fn-anchor-verifiedp' -- the two
; constrained Ed25519 checks and the delegation window -- and, since
; 2026-09-20, on `fn-anchor-one-nonce-p', which says the response covers one
; nonce and it is this node's.  A response that fails the second is reported
; `:uncertain :unmodelled-tree' and never reaches the rules above; see
; `fn-anchor-unmodelled-tree-is-uncertain'.  None of them claims a signature
; cannot be forged, that a Merkle path binds a nonce to a root, or that a
; Roughtime server is honest; specs/anchor.md carries that trust.
;
; Style: docs/proof-style.md.  This is the properties book of the anchor
; cluster, so it opens the definitions `books/anchor.lisp' withdrew, locally
; and by name, and ends with its own export theory.

(in-package "ACL2")
; `anchor-record' is `anchor' plus the FNAN durable record family; this book
; needs both, and never opens frame's grammar itself.
(include-book "anchor-record")
(local (include-book "arithmetic/top" :dir :system))

; Local vocabulary re-enable (docs/proof-style.md sec. 2): this book is about
; the anchor transitions, so it opens every definition `books/anchor.lisp'
; withdrew, plus the octet-width facts it withdrew with them.  Nothing here
; leaves those runes enabled for an includer.
(local (in-theory (enable fn-anchor-vocabulary fn-anchor-octet-vocabulary
                          fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The interval order

(defthm fn-anchor-earliest-not-after-latest
  (implies (fn-anchor-p a)
           (<= (fn-anchor-earliest a) (fn-anchor-latest a)))
  :rule-classes :linear)

(defthm fn-anchor-newerp-is-irreflexive
  (not (fn-anchor-newerp a a)))

(defthm fn-anchor-newerp-is-asymmetric
  (implies (fn-anchor-newerp a b)
           (not (fn-anchor-newerp b a))))

(defthm fn-anchor-newerp-is-transitive
  (implies (and (fn-anchor-newerp c b)
                (fn-anchor-newerp b a))
           (fn-anchor-newerp c a)))

(local (in-theory (disable (:d fn-anchor-newerp) (:d fn-anchor-earliest)
                           (:d fn-anchor-latest))))

; -----------------------------------------------------------------------------
; Acceptance into the node's durable state

(defthm fn-anchor-node-accept-preserves-nodep
  (implies (fn-anchor-nodep node)
           (fn-anchor-nodep (fn-anchor-payload (fn-anchor-node-accept node a)))))

(defthm fn-anchor-node-accept-outcomep
  (fn-anchor-outcomep (fn-anchor-node-accept node a)))

(verify-guards fn-anchor-node-accept-list)

; KEYSTONE.  A node that already holds an anchor accepts a new one only when
; the new one is strictly newer: its whole admissible interval lies after the
; held anchor's.  This is the rule that a replayed old response cannot pass.
(defthm fn-anchor-accepted-anchor-is-strictly-newer
  (implies (and (fn-anchor-nodep node)
                (fn-anchor-node-latest node)
                (equal (fn-anchor-status (fn-anchor-node-accept node a))
                       :accepted))
           (fn-anchor-newerp a (fn-anchor-node-latest node))))

; The accepted node holds exactly the anchor it accepted, so the rule above is
; about the state a later acceptance will be compared against.
(defthm fn-anchor-accepted-node-holds-the-anchor
  (implies (equal (fn-anchor-status (fn-anchor-node-accept node a)) :accepted)
           (equal (fn-anchor-node-latest
                   (fn-anchor-payload (fn-anchor-node-accept node a)))
                  a)))

; A refusal or an uncertain outcome changes nothing durable.
(defthm fn-anchor-unaccepted-leaves-the-node-alone
  (implies (not (equal (fn-anchor-status (fn-anchor-node-accept node a))
                       :accepted))
           (equal (fn-anchor-payload (fn-anchor-node-accept node a)) node)))

; An unverified response is refused, never accepted, whatever else it claims.
(defthm fn-anchor-unverified-is-refused
  (implies (and (fn-anchor-p a) (not (fn-anchor-verifiedp a)))
           (and (equal (fn-anchor-status (fn-anchor-node-accept node a))
                       :refused)
                (equal (fn-anchor-reason (fn-anchor-node-accept node a))
                       :unverified))))

; -----------------------------------------------------------------------------
; A response this model cannot describe is an uncertainty, not an acceptance
;
; These unfold `fn-anchor-node-accept'/`fn-anchor-restore' and
; `fn-anchor-one-nonce-p', so they are definitional consequences and NOT
; registry events (docs/proof-style.md sec. 7, AGENTS.md "cite keystones").
; They are here because they are the sentence the fix is for, in one line
; each, at the two decisions that write durable state: nothing the node
; accepts, and nothing it restores under, is a response whose nonce binding
; this book cannot state.  The teeth are the evidence
; (tests/acl2/anchor-teeth-tests.lisp: a concrete batched anchor, and the
; real batched capture in tests/test_anchor.py).

(defthm fn-anchor-accepted-anchor-covers-one-nonce
  (implies (equal (fn-anchor-status (fn-anchor-node-accept node a)) :accepted)
           (fn-anchor-one-nonce-p a)))

(defthm fn-anchor-accepted-restore-anchor-covers-one-nonce
  (implies (equal (fn-anchor-status (fn-anchor-restore node image presented))
                  :accepted)
           (fn-anchor-one-nonce-p presented)))

; D13, at the new branch: an unfoldable tree is `:uncertain', which is
; neither of the other two.  A verified, pinned, strictly newer response
; whose PATH fn cannot walk leaves the freshness question open and says so.
(defthm fn-anchor-unmodelled-tree-is-uncertain
  (implies (and (fn-anchor-p a)
                (fn-anchor-verifiedp a)
                (not (fn-anchor-one-nonce-p a)))
           (and (equal (fn-anchor-status (fn-anchor-node-accept node a))
                       :uncertain)
                (equal (fn-anchor-reason (fn-anchor-node-accept node a))
                       :unmodelled-tree)
                (not (equal (fn-anchor-status (fn-anchor-node-accept node a))
                            :refused))
                (not (equal (fn-anchor-status (fn-anchor-node-accept node a))
                            :accepted)))))

(defthm fn-anchor-restore-under-an-unmodelled-tree-is-uncertain
  (implies (and (fn-anchor-p presented)
                (fn-anchor-verifiedp presented)
                (not (fn-anchor-one-nonce-p presented)))
           (and (equal (fn-anchor-status
                        (fn-anchor-restore node image presented))
                       :uncertain)
                (equal (fn-anchor-reason
                        (fn-anchor-restore node image presented))
                       :unmodelled-tree)
                (not (equal (fn-anchor-status
                             (fn-anchor-restore node image presented))
                            :accepted)))))

; Three outcomes stay distinct: no anchor at all is `:uncertain', and an
; uncertain outcome is neither a refusal nor an acceptance.
(defthm fn-anchor-absent-anchor-is-uncertain
  (implies (not (fn-anchor-p a))
           (and (equal (fn-anchor-status (fn-anchor-node-accept node a))
                       :uncertain)
                (not (equal (fn-anchor-status (fn-anchor-node-accept node a))
                            :refused))
                (not (equal (fn-anchor-status (fn-anchor-node-accept node a))
                            :accepted)))))

; KEYSTONE.  The durable anchor is monotone across any sequence of responses:
; after any run of acceptances the node's anchor is the one it started with or
; one strictly newer.  Nothing in the sequence can move it backwards.
(defthm fn-anchor-accept-list-latest-never-goes-back
  (implies (and (fn-anchor-nodep node)
                (fn-anchor-node-latest node))
           (or (equal (fn-anchor-node-latest
                       (fn-anchor-node-accept-list node anchors))
                      (fn-anchor-node-latest node))
               (fn-anchor-newerp (fn-anchor-node-latest
                                  (fn-anchor-node-accept-list node anchors))
                                 (fn-anchor-node-latest node))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-anchor-node-accept-list node anchors))))

; -----------------------------------------------------------------------------
; Incarnation advance

(defthm fn-anchor-node-advance-preserves-nodep
  (implies (fn-anchor-nodep node)
           (fn-anchor-nodep (fn-anchor-payload (fn-anchor-node-advance node a)))))

; KEYSTONE.  An incarnation advances only under an anchor strictly newer than
; the one the node holds.  OBJ-006's "an origin's incarnation cannot be reused
; for a different event" is enforced by a measured signed interval, never by
; the local wall clock.
(defthm fn-anchor-incarnation-advances-only-under-a-newer-anchor
  (implies (and (fn-anchor-nodep node)
                (fn-anchor-node-latest node)
                (not (equal (fn-anchor-node-incarnation
                             (fn-anchor-payload (fn-anchor-node-advance node a)))
                            (fn-anchor-node-incarnation node))))
           (fn-anchor-newerp a (fn-anchor-node-latest node))))

(defthm fn-anchor-advance-increments-by-one
  (implies (equal (fn-anchor-status (fn-anchor-node-advance node a)) :accepted)
           (equal (fn-anchor-node-incarnation
                   (fn-anchor-payload (fn-anchor-node-advance node a)))
                  (+ 1 (fn-anchor-node-incarnation node)))))

; -----------------------------------------------------------------------------
; Restore

(defthm fn-anchor-restore-outcomep
  (fn-anchor-outcomep (fn-anchor-restore node image presented)))

; KEYSTONE.  An image that refers to an anchor the presented anchor does not
; outdate is refused as possibly stale.  This is FLR-003's "an old valid
; snapshot" case: every checksum in the image is intact and the restore still
; does not happen.
(defthm fn-anchor-restore-refuses-image-it-cannot-outdate
  (implies (and (fn-anchor-imagep image)
                (fn-anchor-image-referenced image)
                (not (fn-anchor-newerp presented
                                       (fn-anchor-image-referenced image))))
           (and (not (equal (fn-anchor-status
                             (fn-anchor-restore node image presented))
                            :accepted))
                (implies (fn-anchor-acceptablep
                          presented (fn-anchor-node-pinned node))
                         (and (equal (fn-anchor-status
                                      (fn-anchor-restore node image presented))
                                     :refused)
                              (equal (fn-anchor-reason
                                      (fn-anchor-restore node image presented))
                                     :possibly-stale))))))

; An accepted restore did outdate everything the image refers to, and the node
; it produces holds the presented anchor.
(defthm fn-anchor-accepted-restore-outdates-the-image
  (implies (and (fn-anchor-imagep image)
                (fn-anchor-image-referenced image)
                (equal (fn-anchor-status (fn-anchor-restore node image presented))
                       :accepted))
           (and (fn-anchor-newerp presented (fn-anchor-image-referenced image))
                (fn-anchor-acceptablep presented (fn-anchor-node-pinned node))
                (equal (fn-anchor-node-latest
                        (fn-anchor-payload
                         (fn-anchor-restore node image presented)))
                       presented))))

; An accepted restore never continues the image's incarnation; it opens the
; next one, so no counter of the restored incarnation can be issued twice.
(defthm fn-anchor-accepted-restore-opens-a-new-incarnation
  (implies (and (fn-anchor-imagep image)
                (equal (fn-anchor-status (fn-anchor-restore node image presented))
                       :accepted))
           (not (equal (fn-anchor-node-incarnation
                        (fn-anchor-payload
                         (fn-anchor-restore node image presented)))
                       (fn-anchor-image-incarnation image)))))

; With no anchor in hand the restore is `:uncertain', which is not a refusal:
; the node does not know the image is stale, and reporting either certainty
; would be a lie in one direction or the other.
(defthm fn-anchor-restore-without-an-anchor-is-uncertain
  (implies (not (fn-anchor-p presented))
           (and (equal (fn-anchor-status (fn-anchor-restore node image presented))
                       :uncertain)
                (not (equal (fn-anchor-status
                             (fn-anchor-restore node image presented))
                            :refused))
                (not (equal (fn-anchor-status
                             (fn-anchor-restore node image presented))
                            :accepted)))))

; -----------------------------------------------------------------------------
; Fork evidence

; KEYSTONE.  Two images claiming one incarnation but referring to different
; newest anchors are a fork.  Neither is admitted as that incarnation, and the
; outcome carries both images unchanged, so the conflicting evidence survives
; the decision instead of being resolved away.
(defthm fn-anchor-fork-admits-neither-image
  (implies (and (equal (fn-anchor-image-incarnation left)
                       (fn-anchor-image-incarnation right))
                (not (equal (fn-anchor-image-referenced left)
                            (fn-anchor-image-referenced right))))
           (and (equal (fn-anchor-status (fn-anchor-pair-admit left right))
                       :refused)
                (equal (fn-anchor-reason (fn-anchor-pair-admit left right))
                       :fork)
                (not (fn-anchor-pair-admittedp
                      (fn-anchor-pair-admit left right)))
                (equal (fn-anchor-payload (fn-anchor-pair-admit left right))
                       (list left right)))))

; The complement: an admitted pair is one image seen twice, not two histories.
(defthm fn-anchor-admitted-pair-agrees-on-its-anchor
  (implies (fn-anchor-pair-admittedp (fn-anchor-pair-admit left right))
           (and (equal (fn-anchor-image-incarnation left)
                       (fn-anchor-image-incarnation right))
                (equal (fn-anchor-image-referenced left)
                       (fn-anchor-image-referenced right)))))

; -----------------------------------------------------------------------------
; The host entries are the theorems' subjects
;
; AGENTS.md: "The theorem subject is the function the host calls."  The host
; calls `fn-anchor-node-accept-observed', `fn-anchor-node-advance-observed' and
; `fn-anchor-restore-observed' (`tools/run_store.py anchor` and `recover`,
; through `host/anchor-host.lisp`).  These equalities are the named theorems
; that make every keystone above a statement about those calls, under one
; hypothesis PER A-CRYPTO SEAM and nothing else: the host's `verdict' is
; `fn-anchor-signatures-okp' (the two constrained Ed25519 checks) and its
; `one-nonce' is `fn-anchor-one-nonce-p' (the constrained leaf digest).  The
; delegation window is not among them: `fn-anchor-verifiedp-observed'
; applies it inside the entry, so it is ACL2's and no host has to agree
; about it.

; KEYSTONE.  The Ed25519 half is discharged once, here, and every entry
; equality below uses it: a verdict that is the seam's value makes the
; entry's own verification test `fn-anchor-verifiedp' exactly, window and
; all.
(defthm fn-anchor-verifiedp-observed-is-verifiedp
  (implies (equal (and verdict t) (fn-anchor-signatures-okp a))
           (equal (fn-anchor-verifiedp-observed a verdict)
                  (fn-anchor-verifiedp a))))

(defthm fn-anchor-node-accept-observed-is-node-accept
  (implies (and (equal (and verdict t) (fn-anchor-signatures-okp a))
                (equal (and one-nonce t) (fn-anchor-one-nonce-p a)))
           (equal (fn-anchor-node-accept-observed node a verdict one-nonce)
                  (fn-anchor-node-accept node a))))

(defthm fn-anchor-node-advance-observed-is-node-advance
  (implies (and (equal (and verdict t) (fn-anchor-signatures-okp a))
                (equal (and one-nonce t) (fn-anchor-one-nonce-p a)))
           (equal (fn-anchor-node-advance-observed node a verdict one-nonce)
                  (fn-anchor-node-advance node a))))

(defthm fn-anchor-restore-observed-is-restore
  (implies (and (equal (and verdict t) (fn-anchor-signatures-okp presented))
                (equal (and one-nonce t) (fn-anchor-one-nonce-p presented)))
           (equal (fn-anchor-restore-observed node image presented verdict
                                              one-nonce)
                  (fn-anchor-restore node image presented))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md sec. 2)
;
; What leaves this book enabled: the keystones above, the three host-entry
; equalities, the outcome and node preservation facts and the three order
; properties of `fn-anchor-newerp'.  Withdrawn: the linear rule relating the
; interval endpoints, which is proof vocabulary for those order properties and
; backchains into `fn-anchor-earliest'/`fn-anchor-latest' from every
; arithmetic goal above this book.

(deftheory fn-anchor-invariants-vocabulary
  '(fn-anchor-earliest-not-after-latest))

(in-theory (disable fn-anchor-earliest-not-after-latest))
