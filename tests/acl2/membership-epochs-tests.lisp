; Witnesses and teeth for the membership-epoch admissibility policy.
;
; The running witness is C3-08's partition design case, and specs/privacy.md's
; "Partitioned membership" agenda row: two sites remove different members while
; disconnected, and we ask what each may safely accept afterwards.
;
;   founding roster  alice bob carol dave
;   epoch 1          c1: alice adds erin        (base 0)
;   epoch 2          c2: alice rotates          (base 1)
;   --- partition ---
;   epoch 3 at A     ca: alice removes dave     (base 2)
;   epoch 3 at B     cb: bob removes carol      (base 2)
;
; Both sites reach epoch 3 and disagree about what epoch 3 IS.  Every
; assertion below is computed by ACL2; none is a hand-written expectation.

(in-package "ACL2")

(include-book "../../books/membership-epochs-invariants")

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-me-internals
                          fn-me-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The shared prefix

(defconst *me-founding* '("alice" "bob" "carol" "dave"))

(defconst *me-c1* (fn-me-commit "c1" 0 "alice" :add "erin"))
(defconst *me-c2* (fn-me-commit "c2" 1 "alice" :rotate "alice"))
(defconst *me-ca* (fn-me-commit "ca" 2 "alice" :remove "dave"))
(defconst *me-cb* (fn-me-commit "cb" 2 "bob" :remove "carol"))
(defconst *me-c4* (fn-me-commit "c4" 3 "alice" :rotate "bob"))

(assert-event (fn-me-commitp *me-c1*))
(assert-event (equal (fn-me-commit-epoch *me-c1*) 1))
(assert-event (equal (fn-me-commit-epoch *me-ca*) 3))

; Window 2 epochs behind, custody for at most 2 ahead-of-local messages.
(defconst *me-site-a*
  (fn-me-site "site-a" *me-founding*
              (list *me-c1* *me-c2* *me-ca*)
              (list *me-c1* *me-c2* *me-ca*)
              2 2 nil))

(defconst *me-site-b*
  (fn-me-site "site-b" *me-founding*
              (list *me-c1* *me-c2* *me-cb*)
              (list *me-c1* *me-c2* *me-cb*)
              2 2 nil))

(assert-event (fn-me-sitep *me-site-a*))
(assert-event (fn-me-sitep *me-site-b*))
(assert-event (equal (fn-me-epoch *me-site-a*) 3))
(assert-event (equal (fn-me-epoch *me-site-b*) 3))

; The two sites' epoch-3 rosters differ, and neither is a superset of the
; other.  This is the partition, not a race one of them lost.
(assert-event (equal (fn-me-roster-at *me-site-a* 3)
                     '("erin" "alice" "bob" "carol")))
(assert-event (equal (fn-me-roster-at *me-site-b* 3)
                     '("erin" "alice" "bob" "dave")))
(assert-event (equal (fn-me-roster-at *me-site-a* 2)
                     '("erin" "alice" "bob" "carol" "dave")))

; Adoption is knowledge growth; the fork is not.
(assert-event (not (fn-me-knowledge-extendsp *me-site-a* *me-site-b*)))
(assert-event (not (fn-me-knowledge-extendsp *me-site-b* *me-site-a*)))

; -----------------------------------------------------------------------------
; Revocation, per sender and per site

(defconst *me-dave-3* (fn-me-message "dave" 3 "cid-dave-3"))
(defconst *me-dave-2* (fn-me-message "dave" 2 "cid-dave-2"))
(defconst *me-dave-9* (fn-me-message "dave" 9 "cid-dave-9"))

(assert-event (equal (fn-me-revoked-at *me-site-a* "dave") 3))
(assert-event (equal (fn-me-revoked-at *me-site-b* "dave") 0))
(assert-event (equal (fn-me-revoked-at *me-site-b* "carol") 3))

; A refuses dave from epoch 3 onward, including epochs it has not itself
; reached: a known revocation decides ahead of the local epoch, so a held
; message can never later be admitted from a member already known removed.
(assert-event (equal (fn-me-decide *me-site-a* *me-dave-3*) :refuse))
(assert-event (equal (fn-me-decide *me-site-a* *me-dave-9*) :refuse))

; dave's epoch-2 letter, written before the removal it could not have known
; about, is still admissible at A.  SEC-004: a disconnected sender cannot act
; on a change it has not received.
(assert-event (equal (fn-me-decide *me-site-a* *me-dave-2*) :admit))

; B, which adopted the other epoch 3, admits what A refuses.  Neither site is
; wrong about its own state; the disagreement is real and is what
; `fn-me-fork-evidence` is for.
(assert-event (equal (fn-me-decide *me-site-b* *me-dave-3*) :admit))

; Non-members and out-of-window messages are refused, distinctly from a hold.
(assert-event (equal (fn-me-decide *me-site-a* (fn-me-message "mallory" 3 "x"))
                     :refuse))
(assert-event (equal (fn-me-decide *me-site-a* (fn-me-message "alice" 0 "x"))
                     :refuse))
(assert-event (equal (fn-me-decide *me-site-a* (fn-me-message "alice" 1 "x"))
                     :admit))

; -----------------------------------------------------------------------------
; Bounded hold, and its resolution

(defconst *me-erin-4* (fn-me-message "erin" 4 "cid-erin-4"))
(defconst *me-erin-5* (fn-me-message "erin" 5 "cid-erin-5"))
(defconst *me-erin-6* (fn-me-message "erin" 6 "cid-erin-6"))

(assert-event (equal (fn-me-decide *me-site-a* *me-erin-4*) :hold))

(defconst *me-a-held1* (fn-me-receive *me-site-a* *me-erin-4*))
(defconst *me-a-held2* (fn-me-receive *me-a-held1* *me-erin-5*))

(assert-event (equal (len (fn-me-held *me-a-held2*)) 2))
(assert-event (member-equal *me-erin-4* (fn-me-held *me-a-held2*)))
(assert-event (equal (fn-me-epoch *me-a-held2*) 3))

; Custody is bounded, and the fourth outcome is reached rather than silently
; becoming a drop: at the limit the site says `:capacity` and does not take
; the message, so the sender's obligation is not discharged.
(assert-event (equal (fn-me-decide *me-a-held2* *me-erin-6*) :capacity))
(assert-event (equal (fn-me-receive *me-a-held2* *me-erin-6*) *me-a-held2*))

; The held message has a future: A adopts the next commit and admits it.
(defconst *me-a-epoch4* (fn-me-adopt *me-a-held2* *me-c4*))

(assert-event (equal (fn-me-epoch *me-a-epoch4*) 4))
(assert-event (fn-me-knowledge-extendsp *me-a-held2* *me-a-epoch4*))
(assert-event (equal (fn-me-decide *me-a-epoch4* *me-erin-4*) :admit))

; And the refusal of a revoked sender survives that same step.
(assert-event (equal (fn-me-decide *me-a-epoch4* *me-dave-3*) :refuse))

; -----------------------------------------------------------------------------
; The merge: set union with explicit conflict evidence

(defconst *me-merged* (fn-me-merge (fn-me-commits *me-site-a*)
                                   (fn-me-commits *me-site-b*)))

(assert-event (equal (fn-me-commit-ids *me-merged*) '("c1" "c2" "ca" "cb")))
(assert-event (member-equal *me-ca* *me-merged*))
(assert-event (member-equal *me-cb* *me-merged*))
(assert-event (fn-me-forkedp *me-merged*))
(assert-event (equal (fn-me-fork-evidence *me-merged*) (cons *me-ca* *me-cb*)))

; Order independence of the observable.
(assert-event (fn-me-same-idsp *me-merged*
                               (fn-me-merge (fn-me-commits *me-site-b*)
                                            (fn-me-commits *me-site-a*))))

; Never last-writer-wins: A takes B's evidence and revises nothing.  Its epoch,
; its roster and its verdict on dave's epoch-3 letter are all unchanged, and
; the conflict is now visible in its evidence set.
(defconst *me-a-informed*
  (fn-me-site-merge *me-site-a* (fn-me-commits *me-site-b*)))

(assert-event (equal (fn-me-chain *me-a-informed*) (fn-me-chain *me-site-a*)))
(assert-event (equal (fn-me-epoch *me-a-informed*) 3))
(assert-event (equal (fn-me-roster-at *me-a-informed* 3)
                     (fn-me-roster-at *me-site-a* 3)))
(assert-event (equal (fn-me-decide *me-a-informed* *me-dave-3*) :refuse))
(assert-event (fn-me-forkedp (fn-me-commits *me-a-informed*)))

; -----------------------------------------------------------------------------
; The re-admission policy, and why it exists
;
; A chain that removes dave at epoch 3 and adds him back at epoch 4 fails
; `fn-me-no-readmissionp`.  With it, `fn-me-revoked-at` still reports 3 while
; the epoch-4 roster contains dave: the site would refuse a letter from a
; member its own roster says is present.  Re-admission under a fresh member
; identity has no such gap.

(defconst *me-readd* (fn-me-commit "c5" 3 "alice" :add "dave"))
(defconst *me-site-readd*
  (fn-me-site "site-r" *me-founding*
              (list *me-c1* *me-c2* *me-ca* *me-readd*)
              (list *me-c1* *me-c2* *me-ca* *me-readd*)
              2 2 nil))

(assert-event (fn-me-no-readmissionp (fn-me-chain *me-site-a*)))
(assert-event (not (fn-me-no-readmissionp (fn-me-chain *me-site-readd*))))
(assert-event (member-equal "dave" (fn-me-roster-at *me-site-readd* 4)))
(assert-event (equal (fn-me-revoked-at *me-site-readd* "dave") 3))
(assert-event (equal (fn-me-decide *me-site-readd*
                                   (fn-me-message "dave" 4 "cid"))
                     :refuse))

; -----------------------------------------------------------------------------
; Teeth (docs/proof-style.md section 5): one CONCRETE violating value per
; hypothesis.  Each block drops one hypothesis of a keystone and exhibits a
; ground state for which the conclusion is false; the previous `must-fail`
; forms proved only that the prover found no proof, and cost 220 s of the
; 221 s this book took to certify.

; A site that has adopted nothing after epoch 2: it revokes nobody, so it is
; the "a" side of every tooth that needs a hold without a revocation.
(defconst *me-site-early*
  (fn-me-site "site-early" *me-founding*
              (list *me-c1* *me-c2*) (list *me-c1* *me-c2*) 2 2 nil))

(assert-event (fn-me-sitep *me-site-early*))
(assert-event (equal (fn-me-epoch *me-site-early*) 2))

; -----------------------------------------------------------------------------
; `fn-me-revoked-scan-stable-under-prefix'

; Without `fn-me-chain-prefixp': B's chain is not an extension of A's, and the
; two scans disagree about dave.
(assert-event (not (fn-me-chain-prefixp (fn-me-chain *me-site-a*)
                                        (fn-me-chain *me-site-b*))))
(assert-event (equal (fn-me-revoked-scan (fn-me-chain *me-site-a*) "dave" 0) 3))
(assert-event (equal (fn-me-revoked-scan (fn-me-chain *me-site-b*) "dave" 0) 0))

; Without a revocation on the shorter chain: a genuine prefix, and the scan
; still moves, because the extension is where the removal happens.
(assert-event (fn-me-chain-prefixp (fn-me-chain *me-site-early*)
                                   (fn-me-chain *me-site-a*)))
(assert-event (equal (fn-me-revoked-scan (fn-me-chain *me-site-early*) "dave" 0) 0))
(assert-event (not (equal (fn-me-revoked-scan (fn-me-chain *me-site-a*) "dave" 0)
                          (fn-me-revoked-scan (fn-me-chain *me-site-early*)
                                              "dave" 0))))

; -----------------------------------------------------------------------------
; `fn-me-roster-fold-omits-removed'

; Without `fn-me-no-readmissionp': dave is absent from the starting roster and
; present in the fold, because the chain adds him back at epoch 4.
(assert-event (not (fn-me-no-readmissionp (fn-me-chain *me-site-readd*))))
(assert-event (not (member-equal "dave" '("alice"))))
(assert-event (member-equal "dave"
                            (fn-me-roster-fold '("alice")
                                               (fn-me-chain *me-site-readd*))))

; -----------------------------------------------------------------------------
; `fn-me-revoked-refusal-is-monotone'

; Without `fn-me-knowledge-extendsp': B is not an extension of A, and B admits
; exactly the letter A refuses.  This is the partition, stated as a value.
(assert-event (not (fn-me-knowledge-extendsp *me-site-a* *me-site-b*)))
(assert-event (< 0 (fn-me-revoked-at *me-site-a* "dave")))
(assert-event (<= (fn-me-revoked-at *me-site-a* "dave")
                  (fn-me-msg-epoch *me-dave-3*)))
(assert-event (equal (fn-me-decide *me-site-b* *me-dave-3*) :admit))

; Without a revocation at A: knowledge grows and the letter is admitted.
(assert-event (fn-me-knowledge-extendsp *me-a-held2* *me-a-epoch4*))
(assert-event (equal (fn-me-revoked-at *me-a-held2* "erin") 0))
(assert-event (equal (fn-me-decide *me-a-epoch4* *me-erin-4*) :admit))

; Without the epoch being at or after the revocation: dave's epoch-2 letter
; predates his removal at epoch 3, and B admits it.  SEC-004.
(assert-event (fn-me-knowledge-extendsp *me-site-a* *me-a-epoch4*))
(assert-event (< 0 (fn-me-revoked-at *me-site-a* "dave")))
(assert-event (< (fn-me-msg-epoch *me-dave-2*)
                 (fn-me-revoked-at *me-site-a* "dave")))
(assert-event (equal (fn-me-decide *me-a-epoch4* *me-dave-2*) :admit))

; -----------------------------------------------------------------------------
; `fn-me-ahead-message-is-held'

; Without the `:hold' verdict: a refused letter is not taken into custody, so
; the sender's obligation is not discharged by a site that said no.
(assert-event (equal (fn-me-decide *me-site-a* *me-dave-3*) :refuse))
(assert-event (not (member-equal *me-dave-3*
                                 (fn-me-held (fn-me-receive *me-site-a*
                                                            *me-dave-3*)))))

; -----------------------------------------------------------------------------
; `fn-me-hold-count-bounded'

; Without the incoming bound: a site handed a held list longer than its own
; limit stays over the limit.  The keystone bounds custody growth, not custody.
(defconst *me-site-over*
  (fn-me-site "site-over" *me-founding*
              (list *me-c1* *me-c2* *me-ca*) (list *me-c1* *me-c2* *me-ca*)
              2 1 (list *me-erin-4* *me-erin-5*)))

(assert-event (fn-me-sitep *me-site-over*))
(assert-event (< (fn-me-hold-limit *me-site-over*)
                 (len (fn-me-held *me-site-over*))))
(assert-event (equal (fn-me-decide *me-site-over* *me-erin-6*) :capacity))
(assert-event (< (fn-me-hold-limit *me-site-over*)
                 (len (fn-me-held (fn-me-receive *me-site-over* *me-erin-6*)))))

; -----------------------------------------------------------------------------
; `fn-me-hold-resolves-on-reaching-epoch'

; Without the receiver having reached the epoch: A holds erin's epoch-4 letter
; and, at epoch 3, holds it again rather than admitting it.
(assert-event (equal (fn-me-decide *me-site-a* *me-erin-4*) :hold))
(assert-event (< (fn-me-epoch *me-site-a*) (fn-me-msg-epoch *me-erin-4*)))
(assert-event (equal (fn-me-decide *me-site-a* *me-erin-4*) :hold))

; Without the window: a site five epochs along with a zero-epoch window
; refuses the same letter as too old.  The window is a bound on how far back
; a receiver will reach, and it is what makes custody finite.
(defconst *me-c5* (fn-me-commit "c5" 4 "alice" :rotate "carol"))
(defconst *me-site-far*
  (fn-me-site "site-far" *me-founding*
              (list *me-c1* *me-c2* *me-ca* *me-c4* *me-c5*)
              (list *me-c1* *me-c2* *me-ca* *me-c4* *me-c5*)
              0 2 nil))

(assert-event (fn-me-sitep *me-site-far*))
(assert-event (equal (fn-me-epoch *me-site-far*) 5))
(assert-event (< (+ (fn-me-msg-epoch *me-erin-4*)
                    (fn-me-window *me-site-far*))
                 (fn-me-epoch *me-site-far*)))
(assert-event (equal (fn-me-revoked-at *me-site-far* "erin") 0))
(assert-event (member-equal "erin" (fn-me-roster-at *me-site-far* 4)))
(assert-event (equal (fn-me-decide *me-site-far* *me-erin-4*) :refuse))

; Without `(equal (fn-me-revoked-at b sender) 0)': the re-admission chain is
; the only shape that satisfies every other hypothesis while the sender is
; revoked, and there the letter is refused.  This is the gap that makes
; `fn-me-no-readmissionp' a requirement and not a taste.
(defconst *me-dave-4* (fn-me-message "dave" 4 "cid-dave-4"))

(assert-event (equal (fn-me-decide *me-site-early* *me-dave-4*) :hold))
(assert-event (equal (fn-me-epoch *me-site-readd*) 4))
(assert-event (member-equal "dave" (fn-me-roster-at *me-site-readd* 4)))
(assert-event (not (equal (fn-me-revoked-at *me-site-readd* "dave") 0)))
(assert-event (equal (fn-me-decide *me-site-readd* *me-dave-4*) :refuse))

; Without membership at the letter's epoch: mallory is held while ahead and
; refused once the epoch is reached.  A hold is not a promise to admit.
(defconst *me-mallory-4* (fn-me-message "mallory" 4 "cid-mallory-4"))

(assert-event (equal (fn-me-decide *me-site-a* *me-mallory-4*) :hold))
(assert-event (not (member-equal "mallory" (fn-me-roster-at *me-a-epoch4* 4))))
(assert-event (equal (fn-me-decide *me-a-epoch4* *me-mallory-4*) :refuse))

; Without the `:hold' verdict at A: an admitted letter is never in custody.
(assert-event (equal (fn-me-decide *me-site-a* (fn-me-message "alice" 1 "x"))
                     :admit))
(assert-event (not (member-equal
                    (fn-me-message "alice" 1 "x")
                    (fn-me-held (fn-me-receive *me-site-a*
                                               (fn-me-message "alice" 1 "x"))))))

; -----------------------------------------------------------------------------
; `fn-me-merge-exposes-the-partition'

; Without the same base: two commits at different epochs are not a fork, and
; the merge of them is a plain union.
(assert-event (not (equal (fn-me-commit-base *me-c1*)
                          (fn-me-commit-base *me-c2*))))
(assert-event (not (fn-me-forkedp (fn-me-merge (list *me-c1*) (list *me-c2*)))))

; Without the right commit being new: an id already known is not merged, so a
; conflicting commit carrying a known id never reaches the evidence set.  The
; witness is an id collision, which is why ids are content ids and not names.
(defconst *me-cb-imposter* (fn-me-commit "cb" 0 "alice" :add "zed"))
(defconst *me-a-collided* (list *me-ca* *me-cb-imposter*))

(assert-event (member-equal (fn-me-commit-id *me-cb*)
                            (fn-me-commit-ids *me-a-collided*)))
(assert-event (equal (fn-me-commit-base *me-ca*) (fn-me-commit-base *me-cb*)))
(assert-event (not (fn-me-forkedp (fn-me-merge *me-a-collided* (list *me-cb*)))))

; The distinctness hypothesis of `fn-me-merge-exposes-the-partition' has no
; violating value: `(member-equal ca a)' puts ca's id in `(fn-me-commit-ids a)'
; and the last hypothesis keeps cb's id out of it, so the ids differ already.
; Recorded open rather than dropped: removing it re-proves the keystone, which
; this lane could not run (planning/deputies/substrate.md).
