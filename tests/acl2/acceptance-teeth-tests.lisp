; Teeth for the acceptance keystones.
;
; The 2026-09-18 independent review names local-number freshness as genuinely
; strong: `fn-install-preserves-state' with `fn-watermark-does-not-conflict'
; and `fn-allocate-at-watermark' (books/acceptance-invariants.lisp:65-192).
; A keystone earns that name only with teeth: a reachable non-degenerate
; witness, and one case per hypothesis showing the conclusion fails without it.
;
; Every negative case below is a ground term.  ACL2 evaluates both sides and
; refuses the theorem; "the prover could not find a proof" is not the evidence,
; the computed counterexample is.  The `must-fail' forms are local because
; proofs are skipped during include-book, which would make a failing theorem
; appear to succeed (see :DOC must-fail).

(in-package "ACL2")
(include-book "../../books/acceptance-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.
;
; Two configured groups, two committed articles, and a third staged but not
; published.  Non-degenerate in the sense the review asks for: the state has
; more than one article, the articles hold more than one membership each, and
; the two articles differ in every field that the invariant constrains, so a
; predicate that separated them only by their weakest clause would not do.

(defconst *acc-teeth-groups* '("fn.letters" "fn.test"))
(defconst *acc-teeth-payload-a* '(72 105 13 10))
(defconst *acc-teeth-payload-b* '(66 121 101 13 10))
(defconst *acc-teeth-id-a* "<a@example.invalid>")
(defconst *acc-teeth-id-b* "<b@example.invalid>")

(defconst *acc-teeth-empty* (fn-initial-state *acc-teeth-groups*))
(assert-event (fn-statep *acc-teeth-empty*))
(assert-event (null (fn-state-pending *acc-teeth-empty*)))

(defconst *acc-teeth-prepared-a*
  (fn-accept-prepare *acc-teeth-empty* 7 *acc-teeth-id-a*
                     *acc-teeth-payload-a* *acc-teeth-groups*))
(defconst *acc-teeth-committed-a*
  (fn-accept-complete *acc-teeth-prepared-a* 0 7 :durable))
(defconst *acc-teeth-prepared-b*
  (fn-accept-prepare *acc-teeth-committed-a* 8 *acc-teeth-id-b*
                     *acc-teeth-payload-b* *acc-teeth-groups*))
(defconst *acc-teeth-committed-b*
  (fn-accept-complete *acc-teeth-prepared-b* 1 8 :durable))

; The witness is reached by actual transitions, not constructed by hand.
(assert-event (fn-statep *acc-teeth-prepared-a*))
(assert-event (fn-statep *acc-teeth-committed-a*))
(assert-event (fn-statep *acc-teeth-prepared-b*))
(assert-event (fn-statep *acc-teeth-committed-b*))

; It is non-degenerate: two articles, two memberships each, all four local
; numbers distinct within their group, and the second article strictly above
; the first in both groups.
(assert-event (equal (len (fn-state-articles *acc-teeth-committed-b*)) 2))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *acc-teeth-id-a*
                          (fn-state-articles *acc-teeth-committed-b*)))
        '(("fn.letters" . 1) ("fn.test" . 1))))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *acc-teeth-id-b*
                          (fn-state-articles *acc-teeth-committed-b*)))
        '(("fn.letters" . 2) ("fn.test" . 2))))
(assert-event
 (equal (fn-state-nexts *acc-teeth-committed-b*)
        '(("fn.letters" . 3) ("fn.test" . 3))))
(assert-event
 (not (equal (fn-article-payload
              (fn-find-article *acc-teeth-id-a*
                               (fn-state-articles *acc-teeth-committed-b*)))
             (fn-article-payload
              (fn-find-article *acc-teeth-id-b*
                               (fn-state-articles *acc-teeth-committed-b*))))))

; The staged article that `fn-install-pending' is about: pending is a cons and
; the state is still a state, which is exactly the keystone's premise pair.
(assert-event (consp (fn-state-pending *acc-teeth-prepared-b*)))
(assert-event (fn-statep (fn-install-pending *acc-teeth-prepared-b*)))
(assert-event
 (equal (len (fn-state-articles (fn-install-pending *acc-teeth-prepared-b*))) 2))

; -----------------------------------------------------------------------------
; Teeth for `fn-install-preserves-state'
;   (implies (and (fn-statep s) (consp (fn-state-pending s)))
;            (fn-statep (fn-install-pending s)))

; Hypothesis 1, `(fn-statep s)', dropped.  A forged state whose group list is
; the integer 7 still has a well-formed pending slot, so the second hypothesis
; holds; installing it publishes an article into a state with no group list.
(defconst *acc-teeth-forged*
  (list 7 nil nil 0
        (list *acc-teeth-id-a* *acc-teeth-payload-a* *acc-teeth-groups*
              '(("fn.letters" . 1) ("fn.test" . 1)) t)
        nil))
(assert-event (not (fn-statep *acc-teeth-forged*)))
(assert-event (consp (fn-state-pending *acc-teeth-forged*)))

(local
 (must-fail
  (defthm acc-teeth-install-without-statep
    (fn-statep (fn-install-pending *acc-teeth-forged*)))))

; Hypothesis 2, `(consp (fn-state-pending s))', dropped.  The empty state is a
; state; installing its absent pending slot publishes an article whose
; Message-ID is NIL, which `fn-articlep' rejects.
(local
 (must-fail
  (defthm acc-teeth-install-without-pending
    (fn-statep (fn-install-pending *acc-teeth-empty*)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-watermark-does-not-conflict'
;   (implies (and (fn-memberships-at-watermarkp memberships nexts)
;                 (fn-articles-below-nextsp articles nexts))
;            (not (fn-memberships-conflictsp memberships articles)))

; The conclusion mentions no next-number table, so each case has to be built
; from data that violates exactly one hypothesis while satisfying the other.

; Hypothesis 1, at-watermark, dropped.  A committed article already holds
; ("fn.test" . 1); the table has moved past it, so the article is below the
; watermark, but a stale allocation claims 1 again.
(defconst *acc-teeth-held-test*
  (list (fn-make-article *acc-teeth-id-a* *acc-teeth-payload-a*
                         '("fn.test") '(("fn.test" . 1)) t)))
(defconst *acc-teeth-stale-claim* '(("fn.test" . 1)))

(assert-event
 (not (fn-memberships-at-watermarkp *acc-teeth-stale-claim* '(("fn.test" . 2)))))
(assert-event (fn-articles-below-nextsp *acc-teeth-held-test* '(("fn.test" . 2))))

(local
 (must-fail
  (defthm acc-teeth-conflict-without-watermark
    (not (fn-memberships-conflictsp *acc-teeth-stale-claim*
                                    *acc-teeth-held-test*)))))

; Hypothesis 2, articles-below-nexts, dropped.  A different group and number:
; the allocation is exactly at the watermark, but a committed article was
; published at the watermark rather than below it, so it collides.
(defconst *acc-teeth-held-letters*
  (list (fn-make-article *acc-teeth-id-b* *acc-teeth-payload-b*
                         '("fn.letters") '(("fn.letters" . 5)) t)))
(defconst *acc-teeth-fresh-claim* '(("fn.letters" . 5)))

(assert-event
 (fn-memberships-at-watermarkp *acc-teeth-fresh-claim* '(("fn.letters" . 5))))
(assert-event
 (not (fn-articles-below-nextsp *acc-teeth-held-letters* '(("fn.letters" . 5)))))

(local
 (must-fail
  (defthm acc-teeth-conflict-without-below-nexts
    (not (fn-memberships-conflictsp *acc-teeth-fresh-claim*
                                    *acc-teeth-held-letters*)))))

; -----------------------------------------------------------------------------
; `fn-allocate-at-watermark': two hypotheses could not be given teeth.
;
;   (implies (and (fn-nexts-for-p configured nexts)      ; H1
;                 (fn-subsetp groups configured)         ; H2
;                 (fn-no-duplicatesp groups))            ; H3
;            (fn-memberships-at-watermarkp
;             (fn-allocate-memberships groups nexts) nexts))
;
; H3 has teeth, below.  H1 and H2 appear to be unnecessary, and no witness
; violating them was constructible, so none is forged here.  The argument, for
; the record: `fn-allocate-memberships' assigns group G the value
; `(fn-next-number G nexts)' for the FIRST group and
; `(fn-next-number G (fn-bump-number ... nexts))' thereafter, while
; `fn-memberships-at-watermarkp' compares against `(fn-next-number G nexts)'
; for every group.  `fn-bump-number' rebuilds its argument unchanged when the
; group is absent (books/acceptance.lisp:163-182) and otherwise changes only
; that group's entry, and `fn-next-number' returns 0 for an absent group
; (:146-159), so under H3 the two agree whatever `configured' is and whether or
; not `nexts' is well formed.  Reported as a finding in HANDOFF.md; the right
; repair is to drop the two hypotheses or to state the theorem about a
; representation where they matter, not to add a witness that does not exist.

; Hypothesis 3, no-duplicatesp, dropped: a repeated group is allocated twice,
; and the second copy sits one above the watermark it is compared to.
(defconst *acc-teeth-dup-groups* '("fn.test" "fn.test"))
(defconst *acc-teeth-nexts-one* '(("fn.test" . 1)))
(assert-event (not (fn-no-duplicatesp *acc-teeth-dup-groups*)))
(assert-event (fn-nexts-for-p '("fn.test") *acc-teeth-nexts-one*))
(assert-event (fn-subsetp *acc-teeth-dup-groups* '("fn.test")))
(assert-event
 (equal (fn-allocate-memberships *acc-teeth-dup-groups* *acc-teeth-nexts-one*)
        '(("fn.test" . 1) ("fn.test" . 2))))

(local
 (must-fail
  (defthm acc-teeth-allocate-without-no-duplicates
    (fn-memberships-at-watermarkp
     (fn-allocate-memberships *acc-teeth-dup-groups* *acc-teeth-nexts-one*)
     *acc-teeth-nexts-one*))))
