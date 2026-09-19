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
; Every one of them is conditional on `fn-anchor-verifiedp', which is the
; constrained Ed25519 check.  None of them claims a signature cannot be forged
; or that a Roughtime server is honest; specs/anchor.md carries that trust.
;
; Style: docs/proof-style.md.  This is the properties book of the anchor
; cluster, so it opens the definitions `books/anchor.lisp' withdrew, locally
; and by name, and ends with its own export theory.

(in-package "ACL2")
(include-book "anchor")
; The FNAN round trip at the end of this book rests on frame's own round trip,
; `fn-frame-decode-of-encode' (books/frame-invariants.lisp).
(include-book "frame-invariants")
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
; through `host/anchor-host.lisp`).  These three equalities are the named
; theorems that make every keystone above a statement about those calls, under
; exactly one hypothesis: that the host's Ed25519 verdict is the value the
; constrained seam names for that anchor.

(defthm fn-anchor-node-accept-observed-is-node-accept
  (implies (equal (and verdict t) (fn-anchor-verifiedp a))
           (equal (fn-anchor-node-accept-observed node a verdict)
                  (fn-anchor-node-accept node a))))

(defthm fn-anchor-node-advance-observed-is-node-advance
  (implies (equal (and verdict t) (fn-anchor-verifiedp a))
           (equal (fn-anchor-node-advance-observed node a verdict)
                  (fn-anchor-node-advance node a))))

(defthm fn-anchor-restore-observed-is-restore
  (implies (equal (and verdict t) (fn-anchor-verifiedp presented))
           (equal (fn-anchor-restore-observed node image presented verdict)
                  (fn-anchor-restore node image presented))))

; -----------------------------------------------------------------------------
; The durable record family
;
; Local vocabulary re-enable: the FNAN round trip is the only place in this
; book that opens frame's grammar and its two result records, so the enable
; sits here rather than at the top (docs/deputies BOARD, 2026-09-19 codecs).

(local (in-theory (enable fn-frame-codec-vocabulary
                          fn-frame-record-vocabulary
                          fn-frame-fields-vocabulary
                          fn-frame-invariants-vocabulary
                          fn-frame-octet-vocabulary
                          (:d fn-frame-split) (:d fn-frame-u64-bytes))))

; `fn-anchor-record-anchor-is-an-anchor' is the third conjunct of
; `fn-anchor-record-okp' restated with that predicate as its hypothesis: it is
; true by definition and is not a registry event (docs/proof-style.md sec. 7).
(defthm fn-anchor-record-anchor-is-an-anchor
  (implies (fn-anchor-record-okp kind values)
           (fn-anchor-p (fn-anchor-record-anchor kind values)))
  :rule-classes nil)

; The value direction for FNAN: everything the host encodes decodes back to the
; kind and the field values it started from.
(defthm fn-anchor-decode-of-encode
  (implies (and (fn-anchor-record-okp kind values)
                (fn-frame-digestp digest)
                (not (equal (fn-anchor-encode kind values digest) :bad)))
           (equal (fn-anchor-decode (fn-anchor-encode kind values digest)
                                    digest)
                  (fn-frame-ok *fn-anchor-magic* *fn-frame-version* kind
                               values)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-anchor-encode fn-anchor-decode
                            fn-frame-inputp fn-frame-magicp fn-frame-item)
                           (fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets)))))

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
