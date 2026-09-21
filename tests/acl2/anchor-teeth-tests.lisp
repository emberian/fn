; Teeth for the monotone-anchor rule.
;
; One concrete violating value per hypothesis of each keystone in
; books/anchor-invariants.lisp, as an `assert-event' on the negated
; conclusion, plus a reachable non-degenerate witness for each keystone.  A
; general negated `must-fail' is never used here: it proves that the prover
; could not find a proof, which is not a counterexample (docs/proof-style.md
; sec. 5).  Where a hypothesis has NO violating value the fact is recorded
; open in a comment, with the reason, rather than the theorem being weakened.
;
; The keystones are about `fn-anchor-node-accept', `fn-anchor-node-advance'
; and `fn-anchor-restore', which call the constrained Ed25519 seam and so
; cannot be evaluated as they stand.  This book therefore attaches a test-only
; realiser to each of the two A-CRYPTO seams, so every witness below is a
; value of the keystone's own subject and not of a sibling.  The realisers are
; the encapsulates' own local witnesses (widths only, no unforgeability), so
; nothing here strengthens what the books assume.

(in-package "ACL2")

; The captured Roughtime vector and the derived anchors, nodes and images.
(include-book "anchor-tests")

(local (in-theory (enable fn-anchor-vocabulary)))

;; -----------------------------------------------------------------------------
;; The test-only realisers for the two A-CRYPTO seams

;; The captured response has one nonce, so its tree has one leaf and the root
;; is that leaf digest: the realiser returns the captured ROOT for the nonce
;; this node chose, and a different 64 octets for any other nonce.  It
;; satisfies both constraints of the encapsulate (64 octets) and claims
;; nothing else -- in particular nothing about collisions.  It DISCRIMINATES
;; on the nonce on purpose: a realiser constant in its argument would make
;; `fn-anchor-one-nonce-p' true of every root that happened to match, and the
;; separating witnesses below would separate nothing.
(defconst *anchor-foreign-root* (cons 7 (cdr *anchor-root*)))

(defun fn-t-anchor-leaf-digest (nonce)
  (declare (xargs :guard t))
  (if (equal nonce *anchor-nonce*) *anchor-root* *anchor-foreign-root*))

;; The Ed25519 realiser is the encapsulate's own local witness: it refuses a
;; key or a signature of the wrong width and otherwise accepts.  That is
;; exactly what the seam constrains, and the pair of witnesses at the end of
;; this book shows what it does NOT constrain.
(defun fn-t-anchor-sig-verify (key message signature)
  (declare (xargs :guard t))
  (and (fn-anchor-octets-of-lengthp key *fn-anchor-key-octets*)
       (fn-anchor-octets-of-lengthp signature *fn-anchor-sig-octets*)
       (consp message)
       t))

(defattach fn-anchor-leaf-digest fn-t-anchor-leaf-digest)
(defattach fn-anchor-sig-verify fn-t-anchor-sig-verify)

;; With the realisers in place the captured vector verifies, so every witness
;; below reaches the branch it is meant to reach.
(assert-event (fn-anchor-verifiedp *anchor-live*))
(assert-event (fn-anchor-acceptablep *anchor-live* *anchor-pinned*))
(assert-event (fn-anchor-one-nonce-p *anchor-live*))
(assert-event (fn-anchor-signatures-okp *anchor-live*))
(assert-event (fn-anchor-window-okp *anchor-live*))

;; -----------------------------------------------------------------------------
;; A batched response is UNCERTAIN, which is what w11/anchor-root bought
;;
;; `*anchor-batched*' (tests/acl2/anchor-tests.lisp) is a well-formed anchor
;; whose ROOT is not the leaf digest of this node's nonce: exactly what a
;; Roughtime server answering a batch of clients sends, and exactly what
;; tests/vectors/roughtime-int08h-2026-09-19-later2.json really is (PATH one
;; node, INDX 1).  Before the root was a record field the model could not
;; tell it from `*anchor-live*', because `fn-anchor-root' RECOMPUTED the root
;; from the nonce; the host verified one message and the keystones described
;; another.  Now the model sees the real signed octets, cannot fold the tree,
;; and says so -- as an UNCERTAINTY, because every signature in it is good
;; and fn simply cannot tell whether it covers this node's nonce.

(assert-event (fn-anchor-p *anchor-batched*))
(assert-event (not (fn-anchor-one-nonce-p *anchor-batched*)))
;; Its signatures are fine, which is why `:refused :unverified' would be a
;; false statement about it.
(assert-event (fn-anchor-signatures-okp *anchor-batched*))
(assert-event (fn-anchor-verifiedp *anchor-batched*))
(assert-event (not (fn-anchor-acceptablep *anchor-batched* *anchor-pinned*)))

;; At the acceptance decision: uncertain, with its own reason, and the node's
;; durable anchor is untouched.
(assert-event
 (equal (fn-anchor-status (fn-anchor-node-accept *anchor-node-held*
                                                 *anchor-batched*))
        :uncertain))
(assert-event
 (equal (fn-anchor-reason (fn-anchor-node-accept *anchor-node-held*
                                                 *anchor-batched*))
        :unmodelled-tree))
(assert-event
 (not (equal (fn-anchor-status (fn-anchor-node-accept *anchor-node-held*
                                                      *anchor-batched*))
             :refused)))
(assert-event
 (equal (fn-anchor-payload (fn-anchor-node-accept *anchor-node-held*
                                                  *anchor-batched*))
        *anchor-node-held*))

;; At the restore decision, where the same batched response would otherwise
;; have outdated the image and opened a new incarnation: uncertain.
(assert-event
 (fn-anchor-newerp *anchor-batched-newer* (fn-anchor-image-referenced
                                           *anchor-image-old*)))
(assert-event
 (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                             *anchor-image-old*
                                             *anchor-batched-newer*))
        :uncertain))
(assert-event
 (equal (fn-anchor-reason (fn-anchor-restore *anchor-node-fresh*
                                             *anchor-image-old*
                                             *anchor-batched-newer*))
        :unmodelled-tree))

;; And the separation is the ROOT and nothing else: the one-nonce twin of the
;; same response, identical in its other nine fields, is accepted.
(assert-event
 (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                             *anchor-image-old*
                                             *anchor-newer*))
        :accepted))

;; The nonce is load-bearing, concretely: a response carrying a FOREIGN nonce
;; under this node's signed root does not cover one nonce of ours either.
;; This is the witness for
;; `fn-anchor-one-nonce-signed-octets-determine-the-leaf-digest'.
(assert-event (not (fn-anchor-one-nonce-p *anchor-foreign-nonce*)))
;; Its signatures and its window are fine; it is the binding that is not.
(assert-event (fn-anchor-verifiedp *anchor-foreign-nonce*))
(assert-event
 (not (fn-anchor-acceptablep *anchor-foreign-nonce* *anchor-pinned*)))
(assert-event
 (equal (fn-anchor-reason (fn-anchor-node-accept *anchor-node-held*
                                                 *anchor-foreign-nonce*))
        :unmodelled-tree))
(assert-event
 (not (equal (fn-anchor-leaf-digest (fn-anchor-nonce *anchor-foreign-nonce*))
             (fn-anchor-leaf-digest (fn-anchor-nonce *anchor-live*)))))

;; -----------------------------------------------------------------------------
;; The delegation window is ACL2's, not the host's
;;
;; `*anchor-out-of-window*' has MINT one microsecond after MIDP.  Its seam
;; verdict is T -- the two Ed25519 checks pass and the response covers one
;; nonce, which is everything the host is asked for -- and the entry the host
;; calls still refuses it, because `fn-anchor-verifiedp-observed' applies
;; `fn-anchor-window-okp' inside.  Before 2026-09-20 this refusal existed
;; only in `tools/roughtime.py:258'.
(assert-event (fn-anchor-signatures-okp *anchor-out-of-window*))
(assert-event (not (fn-anchor-window-okp *anchor-out-of-window*)))
(assert-event (not (fn-anchor-verifiedp *anchor-out-of-window*)))
(assert-event
 (equal (fn-anchor-reason (fn-anchor-node-accept-observed
                           *anchor-node-held* *anchor-out-of-window* t t))
        :unverified))
;; Non-degenerate: with the window intact and the same two seam values, it
;; accepts.
(assert-event
 (equal (fn-anchor-status (fn-anchor-node-accept-observed
                           *anchor-node-held* *anchor-live* t t))
        :accepted))
;; And the two seam arguments are not interchangeable: a good signature with
;; an unfoldable tree is uncertain, a bad signature is a refusal.
(assert-event
 (equal (fn-anchor-status (fn-anchor-node-accept-observed
                           *anchor-node-held* *anchor-live* t nil))
        :uncertain))
(assert-event
 (equal (fn-anchor-status (fn-anchor-node-accept-observed
                           *anchor-node-held* *anchor-live* nil t))
        :refused))

;; -----------------------------------------------------------------------------
;; fn-anchor-accepted-anchor-is-strictly-newer
;;
;; Hypotheses: (fn-anchor-nodep node), the node holds an anchor, and the
;; outcome is `:accepted'.

;; Non-degenerate witness: a node holding the older reading accepts the live
;; one, and the live one really is strictly newer.
(assert-event
 (and (equal (fn-anchor-status (fn-anchor-node-accept *anchor-node-held*
                                                      *anchor-live*))
             :accepted)
      (fn-anchor-newerp *anchor-live*
                        (fn-anchor-node-latest *anchor-node-held*))))

;; Without "the node holds an anchor": a node with none accepts its first
;; response, and there is nothing for it to be newer than.
(assert-event
 (and (equal (fn-anchor-status (fn-anchor-node-accept *anchor-node-fresh*
                                                      *anchor-live*))
             :accepted)
      (not (fn-anchor-node-latest *anchor-node-fresh*))
      (not (fn-anchor-newerp *anchor-live*
                             (fn-anchor-node-latest *anchor-node-fresh*)))))

;; Without "the outcome is accepted": a refused stale response would have to
;; be newer than the anchor it failed to outdate.
(assert-event
 (and (not (equal (fn-anchor-status (fn-anchor-node-accept
                                     *anchor-node-current* *anchor-older*))
                  :accepted))
      (fn-anchor-node-latest *anchor-node-current*)
      (not (fn-anchor-newerp *anchor-older*
                             (fn-anchor-node-latest *anchor-node-current*)))))

;; OPEN: `(fn-anchor-nodep node)' has no violating value.  Whatever the node
;; is, `fn-anchor-node-accept' reaches `:accepted' only through the branch
;; that tested `(fn-anchor-newerp a (fn-anchor-node-latest node))', so the
;; conclusion follows from the other two hypotheses alone.  The hypothesis is
;; kept (it is the guard the host carries) and recorded here, not deleted.

;; -----------------------------------------------------------------------------
;; fn-anchor-accept-list-latest-never-goes-back
;;
;; Hypotheses: (fn-anchor-nodep node) and the node holds an anchor.

;; Non-degenerate witness: a run of three responses, one of them stale and one
;; overlapping, leaves the node on the newest reading.
(assert-event
 (equal (fn-anchor-node-latest
         (fn-anchor-node-accept-list
          *anchor-node-held*
          (list *anchor-overlapping* *anchor-live* *anchor-older*
                *anchor-newer*)))
        *anchor-newer*))

;; Without "the node holds an anchor" the disjunction is false: the run moves
;; the node off NIL, and nothing is `fn-anchor-newerp' than NIL.
(assert-event
 (let ((after (fn-anchor-node-latest
               (fn-anchor-node-accept-list *anchor-node-fresh*
                                           (list *anchor-live*)))))
   (and (not (fn-anchor-node-latest *anchor-node-fresh*))
        (not (equal after (fn-anchor-node-latest *anchor-node-fresh*)))
        (not (fn-anchor-newerp after
                               (fn-anchor-node-latest *anchor-node-fresh*))))))

;; -----------------------------------------------------------------------------
;; fn-anchor-incarnation-advances-only-under-a-newer-anchor
;;
;; Hypotheses: (fn-anchor-nodep node), the node holds an anchor, and the
;; incarnation moved.

;; Non-degenerate witness: the advance really does move the incarnation, and
;; only under a strictly newer anchor.
(assert-event
 (and (equal (fn-anchor-node-incarnation
              (fn-anchor-payload (fn-anchor-node-advance *anchor-node-held*
                                                         *anchor-live*)))
             8)
      (not (equal 8 (fn-anchor-node-incarnation *anchor-node-held*)))
      (fn-anchor-newerp *anchor-live*
                        (fn-anchor-node-latest *anchor-node-held*))))

;; Without "the node holds an anchor": a node with none advances on its first
;; response and the conclusion is false.
(assert-event
 (and (not (equal (fn-anchor-node-incarnation
                   (fn-anchor-payload (fn-anchor-node-advance
                                       *anchor-node-fresh* *anchor-live*)))
                  (fn-anchor-node-incarnation *anchor-node-fresh*)))
      (not (fn-anchor-newerp *anchor-live*
                             (fn-anchor-node-latest *anchor-node-fresh*)))))

;; Without "the incarnation moved": an overlapping reading is refused, the
;; incarnation stays where it was, and the anchor is not newer.
(assert-event
 (and (equal (fn-anchor-node-incarnation
              (fn-anchor-payload (fn-anchor-node-advance *anchor-node-current*
                                                         *anchor-overlapping*)))
             (fn-anchor-node-incarnation *anchor-node-current*))
      (not (fn-anchor-newerp *anchor-overlapping*
                             (fn-anchor-node-latest *anchor-node-current*)))))

;; -----------------------------------------------------------------------------
;; fn-anchor-restore-refuses-image-it-cannot-outdate
;;
;; Hypotheses: (fn-anchor-imagep image), the image refers to an anchor, and
;; the presented anchor does not outdate it.

;; Non-degenerate witness: the FLR-003 case.  Every checksum in the image is
;; intact, the presented anchor verifies and is pinned, and the restore is
;; refused with its own reason.
(assert-event
 (and (fn-anchor-imagep *anchor-image-old*)
      (fn-anchor-acceptablep *anchor-older* *anchor-pinned*)
      (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-old*
                                                  *anchor-older*))
             :refused)
      (equal (fn-anchor-reason (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-old*
                                                  *anchor-older*))
             :possibly-stale)))

;; Without "the image refers to an anchor": an image carrying no freshness
;; evidence at all is accepted, so the conclusion fails.
(assert-event
 (and (not (fn-anchor-image-referenced *anchor-image-unanchored*))
      (not (fn-anchor-newerp *anchor-older*
                             (fn-anchor-image-referenced
                              *anchor-image-unanchored*)))
      (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-unanchored*
                                                  *anchor-older*))
             :accepted)))

;; Without "the presented anchor does not outdate it": a genuinely fresh
;; restore is accepted, so the conclusion fails.
(assert-event
 (and (fn-anchor-newerp *anchor-newer*
                        (fn-anchor-image-referenced *anchor-image-old*))
      (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-old*
                                                  *anchor-newer*))
             :accepted)))

;; OPEN: `(fn-anchor-imagep image)' has no violating value here either.  The
;; refusal branch is reached on the two remaining hypotheses alone, whatever
;; the image is.  Recorded, not deleted: the host's guard carries it.

;; -----------------------------------------------------------------------------
;; fn-anchor-accepted-restore-opens-a-new-incarnation

;; Non-degenerate witness: an accepted restore opens the next incarnation.
(assert-event
 (and (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-old*
                                                  *anchor-newer*))
             :accepted)
      (equal (fn-anchor-node-incarnation
              (fn-anchor-payload (fn-anchor-restore *anchor-node-fresh*
                                                    *anchor-image-old*
                                                    *anchor-newer*)))
             8)
      (not (equal 8 (fn-anchor-image-incarnation *anchor-image-old*)))))

;; OPEN: neither hypothesis of this theorem has a violating value, and the
;; reason is the same for both.  On the accepted branch the payload's
;; incarnation is `(+ 1 (fn-anchor-image-incarnation image))', and `(+ 1 x)'
;; is never `x' in ACL2 (a non-number `x' gives 1); on every other branch the
;; payload IS the image, whose fourth slot is NIL for any `fn-anchor-imagep',
;; while its incarnation is a natural.  Both hypotheses are kept as stated and
;; recorded open here.

;; -----------------------------------------------------------------------------
;; fn-anchor-restore-without-an-anchor-is-uncertain
;;
;; Hypothesis: nothing was presented.

;; Non-degenerate witness: with nothing in hand the answer is `:uncertain',
;; which is neither of the other two outcomes (D13).
(assert-event
 (and (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-old* nil))
             :uncertain)
      (equal (fn-anchor-reason (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-old* nil))
             :no-anchor)))

;; Without it, a presented anchor that outdates the image is accepted, so the
;; status is not `:uncertain'.
(assert-event
 (and (fn-anchor-p *anchor-newer*)
      (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                                  *anchor-image-old*
                                                  *anchor-newer*))
             :accepted)
      (not (equal (fn-anchor-status (fn-anchor-restore *anchor-node-fresh*
                                                       *anchor-image-old*
                                                       *anchor-newer*))
                  :uncertain))))

;; -----------------------------------------------------------------------------
;; fn-anchor-fork-admits-neither-image
;;
;; Hypotheses: the incarnations agree, and the referenced anchors differ.

;; Non-degenerate witness: two histories of incarnation 7 are a fork, neither
;; is admitted, and both survive in the payload.
(assert-event
 (and (equal (fn-anchor-status (fn-anchor-pair-admit *anchor-image-old*
                                                     *anchor-image-fork*))
             :refused)
      (equal (fn-anchor-reason (fn-anchor-pair-admit *anchor-image-old*
                                                     *anchor-image-fork*))
             :fork)
      (not (fn-anchor-pair-admittedp
            (fn-anchor-pair-admit *anchor-image-old* *anchor-image-fork*)))
      (equal (fn-anchor-payload (fn-anchor-pair-admit *anchor-image-old*
                                                      *anchor-image-fork*))
             (list *anchor-image-old* *anchor-image-fork*))))

;; Without "the incarnations agree": two ordinary successive incarnations of
;; one origin are `:distinct', not a fork.
(assert-event
 (let ((next (fn-anchor-image 8 *anchor-newer*)))
   (and (not (equal (fn-anchor-image-incarnation *anchor-image-old*)
                    (fn-anchor-image-incarnation next)))
        (not (equal (fn-anchor-image-referenced *anchor-image-old*)
                    (fn-anchor-image-referenced next)))
        (not (equal (fn-anchor-status (fn-anchor-pair-admit
                                       *anchor-image-old* next))
                    :refused)))))

;; Without "the referenced anchors differ": one image seen twice is `:same',
;; so no restore could ever be readmitted if this were a fork.
(assert-event
 (and (equal (fn-anchor-image-incarnation *anchor-image-old*)
             (fn-anchor-image-incarnation *anchor-image-old*))
      (not (equal (fn-anchor-status (fn-anchor-pair-admit *anchor-image-old*
                                                          *anchor-image-old*))
                  :refused))
      (fn-anchor-pair-admittedp (fn-anchor-pair-admit *anchor-image-old*
                                                      *anchor-image-old*))))

;; -----------------------------------------------------------------------------
;; The three host-entry equalities
;;
;; Two hypotheses, one per A-CRYPTO seam: the host's `verdict' is
;; `fn-anchor-signatures-okp' and its `one-nonce' is
;; `fn-anchor-one-nonce-p'.  Without either, the host entry and the theorems'
;; subject come apart, and a host that answers NIL to everything (or T to
;; everything) is computing neither.

;; Without the Ed25519 half.
(assert-event
 (and (fn-anchor-verifiedp *anchor-live*)
      (not (equal (fn-anchor-node-accept-observed *anchor-node-held*
                                                  *anchor-live* nil t)
                  (fn-anchor-node-accept *anchor-node-held* *anchor-live*)))))

(assert-event
 (not (equal (fn-anchor-node-advance-observed *anchor-node-held*
                                              *anchor-live* nil t)
             (fn-anchor-node-advance *anchor-node-held* *anchor-live*))))

(assert-event
 (not (equal (fn-anchor-restore-observed *anchor-node-fresh*
                                         *anchor-image-old* *anchor-newer*
                                         nil t)
             (fn-anchor-restore *anchor-node-fresh* *anchor-image-old*
                                *anchor-newer*))))

;; Without the SHA-512 half, and this is the one this lane added.  A host
;; that reports the two Ed25519 checks ALONE -- T for a batched response,
;; which is what `anchor_verdict' did before this lane -- hands `t' for an
;; anchor whose `fn-anchor-one-nonce-p' is NIL, and the entry and the
;; keystones' subject come apart: the entry accepts and the subject does not.
(assert-event
 (and (fn-anchor-signatures-okp *anchor-batched*)
      (not (fn-anchor-one-nonce-p *anchor-batched*))
      (equal (fn-anchor-status (fn-anchor-node-accept-observed
                                *anchor-node-held* *anchor-batched* t t))
             :accepted)
      (not (equal (fn-anchor-status (fn-anchor-node-accept
                                     *anchor-node-held* *anchor-batched*))
                  :accepted))
      (not (equal (fn-anchor-node-accept-observed *anchor-node-held*
                                                  *anchor-batched* t t)
                  (fn-anchor-node-accept *anchor-node-held*
                                         *anchor-batched*)))))

;; And with both seam values, the two agree, which is the equality the
;; keystones are carried across.  Neither is `fn-anchor-verifiedp': the
;; window conjunct is applied by the entry itself.
(assert-event
 (equal (fn-anchor-node-accept-observed
         *anchor-node-held* *anchor-live*
         (fn-anchor-signatures-okp *anchor-live*)
         (fn-anchor-one-nonce-p *anchor-live*))
        (fn-anchor-node-accept *anchor-node-held* *anchor-live*)))
(assert-event
 (equal (fn-anchor-node-accept-observed
         *anchor-node-held* *anchor-batched*
         (fn-anchor-signatures-okp *anchor-batched*)
         (fn-anchor-one-nonce-p *anchor-batched*))
        (fn-anchor-node-accept *anchor-node-held* *anchor-batched*)))
(assert-event
 (equal (fn-anchor-restore-observed
         *anchor-node-fresh* *anchor-image-old* *anchor-batched-newer*
         (fn-anchor-signatures-okp *anchor-batched-newer*)
         (fn-anchor-one-nonce-p *anchor-batched-newer*))
        (fn-anchor-restore *anchor-node-fresh* *anchor-image-old*
                           *anchor-batched-newer*)))

;; -----------------------------------------------------------------------------
;; What the crypto seam does and does not constrain
;;
;; It constrains widths, and that constraint has teeth: a 63-octet signature
;; never verifies, so a truncated response cannot be accepted.
(assert-event
 (not (fn-anchor-sig-verify *anchor-key*
                            (fn-anchor-signed-octets *anchor-live*)
                            (cdr *anchor-signature*))))
(assert-event
 (not (fn-anchor-sig-verify (cdr *anchor-key*)
                            (fn-anchor-signed-octets *anchor-live*)
                            *anchor-signature*)))

;; It does NOT constrain unforgeability, and this is the witness that says so
;; rather than a `must-fail': under a realiser that satisfies every constraint
;; of the encapsulate, two anchors with different signed messages both verify
;; under the same signature octets.  No theorem in this cluster may be read as
;; saying Ed25519 cannot be forged; specs/anchor.md carries that trust.
(assert-event
 (and (not (equal (fn-anchor-signed-octets *anchor-live*)
                  (fn-anchor-signed-octets *anchor-older*)))
      (fn-anchor-verifiedp *anchor-live*)
      (fn-anchor-verifiedp *anchor-older*)
      (equal (fn-anchor-signature *anchor-live*)
             (fn-anchor-signature *anchor-older*))))
