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
(include-book "std/testing/must-fail" :dir :system)

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
; Teeth: one `must-fail` per hypothesis of each keystone.

; `fn-me-revoked-scan-stable-under-prefix` without the prefix hypothesis.
(must-fail
 (defthm teeth-stable-needs-prefix
   (implies (< 0 (fn-me-revoked-scan a member index))
            (equal (fn-me-revoked-scan b member index)
                   (fn-me-revoked-scan a member index)))
   :rule-classes nil))

; ... and without knowing that `a` records a revocation at all.
(must-fail
 (defthm teeth-stable-needs-a-revocation
   (implies (fn-me-chain-prefixp a b)
            (equal (fn-me-revoked-scan b member index)
                   (fn-me-revoked-scan a member index)))
   :rule-classes nil))

; `fn-me-roster-fold-omits-removed` without the no-re-admission hypothesis.
(must-fail
 (defthm teeth-roster-needs-no-readmission
   (implies (not (member-equal member roster))
            (not (member-equal member (fn-me-roster-fold roster chain))))
   :rule-classes nil))

; `fn-me-revoked-refusal-is-monotone`, one hypothesis at a time.
(must-fail
 (defthm teeth-monotone-needs-knowledge-extension
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (< 0 (fn-me-revoked-at a (fn-me-msg-sender msg)))
                 (<= (fn-me-revoked-at a (fn-me-msg-sender msg))
                     (fn-me-msg-epoch msg)))
            (equal (fn-me-decide b msg) :refuse))
   :rule-classes nil))

(must-fail
 (defthm teeth-monotone-needs-a-revocation
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (fn-me-knowledge-extendsp a b))
            (equal (fn-me-decide b msg) :refuse))
   :rule-classes nil))

(must-fail
 (defthm teeth-monotone-needs-the-epoch-to-be-at-or-after
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (fn-me-knowledge-extendsp a b)
                 (< 0 (fn-me-revoked-at a (fn-me-msg-sender msg))))
            (equal (fn-me-decide b msg) :refuse))
   :rule-classes nil))

; The ground counterexample behind the first of those three: B is not an
; extension of A, and B admits exactly the message A refuses.
(assert-event (and (equal (fn-me-decide *me-site-a* *me-dave-3*) :refuse)
                   (equal (fn-me-decide *me-site-b* *me-dave-3*) :admit)))

; `fn-me-ahead-message-is-held` without the `:hold` verdict.
(must-fail
 (defthm teeth-held-needs-the-hold-verdict
   (implies (and (fn-me-sitep site) (fn-me-messagep msg))
            (member-equal msg (fn-me-held (fn-me-receive site msg))))
   :rule-classes nil))

; `fn-me-hold-count-bounded` without the incoming bound.
(must-fail
 (defthm teeth-bound-needs-the-incoming-bound
   (implies (and (fn-me-sitep site) (fn-me-messagep msg))
            (<= (len (fn-me-held (fn-me-receive site msg)))
                (fn-me-hold-limit site)))
   :rule-classes nil))

; `fn-me-hold-resolves-on-reaching-epoch`, one hypothesis at a time.
(must-fail
 (defthm teeth-resolve-needs-the-epoch-reached
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (equal (fn-me-decide a msg) :hold)
                 (<= (fn-me-epoch b) (+ (fn-me-msg-epoch msg) (fn-me-window b)))
                 (equal (fn-me-revoked-at b (fn-me-msg-sender msg)) 0)
                 (member-equal (fn-me-msg-sender msg)
                               (fn-me-roster-at b (fn-me-msg-epoch msg))))
            (and (member-equal msg (fn-me-held (fn-me-receive a msg)))
                 (equal (fn-me-decide b msg) :admit)))
   :rule-classes nil))

(must-fail
 (defthm teeth-resolve-needs-the-window
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (equal (fn-me-decide a msg) :hold)
                 (<= (fn-me-msg-epoch msg) (fn-me-epoch b))
                 (equal (fn-me-revoked-at b (fn-me-msg-sender msg)) 0)
                 (member-equal (fn-me-msg-sender msg)
                               (fn-me-roster-at b (fn-me-msg-epoch msg))))
            (and (member-equal msg (fn-me-held (fn-me-receive a msg)))
                 (equal (fn-me-decide b msg) :admit)))
   :rule-classes nil))

(must-fail
 (defthm teeth-resolve-needs-no-revocation
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (equal (fn-me-decide a msg) :hold)
                 (<= (fn-me-msg-epoch msg) (fn-me-epoch b))
                 (<= (fn-me-epoch b) (+ (fn-me-msg-epoch msg) (fn-me-window b)))
                 (member-equal (fn-me-msg-sender msg)
                               (fn-me-roster-at b (fn-me-msg-epoch msg))))
            (and (member-equal msg (fn-me-held (fn-me-receive a msg)))
                 (equal (fn-me-decide b msg) :admit)))
   :rule-classes nil))

(must-fail
 (defthm teeth-resolve-needs-membership-at-that-epoch
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (equal (fn-me-decide a msg) :hold)
                 (<= (fn-me-msg-epoch msg) (fn-me-epoch b))
                 (<= (fn-me-epoch b) (+ (fn-me-msg-epoch msg) (fn-me-window b)))
                 (equal (fn-me-revoked-at b (fn-me-msg-sender msg)) 0))
            (and (member-equal msg (fn-me-held (fn-me-receive a msg)))
                 (equal (fn-me-decide b msg) :admit)))
   :rule-classes nil))

; `fn-me-merge-exposes-the-partition`, one hypothesis at a time.
(must-fail
 (defthm teeth-resolve-needs-the-hold-verdict
   (implies (and (fn-me-sitep a) (fn-me-sitep b) (fn-me-messagep msg)
                 (<= (fn-me-msg-epoch msg) (fn-me-epoch b))
                 (<= (fn-me-epoch b) (+ (fn-me-msg-epoch msg) (fn-me-window b)))
                 (equal (fn-me-revoked-at b (fn-me-msg-sender msg)) 0)
                 (member-equal (fn-me-msg-sender msg)
                               (fn-me-roster-at b (fn-me-msg-epoch msg))))
            (and (member-equal msg (fn-me-held (fn-me-receive a msg)))
                 (equal (fn-me-decide b msg) :admit)))
   :rule-classes nil))

(must-fail
 (defthm teeth-partition-needs-distinct-ids
   (implies (and (member-equal ca a)
                 (member-equal cb b)
                 (equal (fn-me-commit-base ca) (fn-me-commit-base cb))
                 (not (member-equal (fn-me-commit-id cb) (fn-me-commit-ids a))))
            (fn-me-forkedp (fn-me-merge a b)))
   :rule-classes nil))

(must-fail
 (defthm teeth-partition-needs-the-same-base
   (implies (and (member-equal ca a)
                 (member-equal cb b)
                 (not (equal (fn-me-commit-id ca) (fn-me-commit-id cb)))
                 (not (member-equal (fn-me-commit-id cb) (fn-me-commit-ids a))))
            (fn-me-forkedp (fn-me-merge a b)))
   :rule-classes nil))

(must-fail
 (defthm teeth-partition-needs-the-right-commit-to-be-new
   (implies (and (member-equal ca a)
                 (member-equal cb b)
                 (equal (fn-me-commit-base ca) (fn-me-commit-base cb))
                 (not (equal (fn-me-commit-id ca) (fn-me-commit-id cb))))
            (fn-me-forkedp (fn-me-merge a b)))
   :rule-classes nil))
