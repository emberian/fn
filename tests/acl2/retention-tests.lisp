; Retention test book: executable ledger scenarios and the teeth of the
; retention keystones.
;
; Folded from retention-tests and retention-teeth-tests (2026-09-19).  Every
; negative case is a concrete violating value that ACL2 evaluates.  A call
; outside a transition's guard is made under `with-guard-checking :none'.
(in-package "ACL2")
(include-book "../../books/retention-invariants")

; -----------------------------------------------------------------------------
; Executable scenarios for the finite-capacity retention ledger.

(defconst *retention-empty* (fn-retain-initial-state 10))
(assert-event (fn-retain-statep *retention-empty*))
(assert-event (equal (fn-retain-reserved *retention-empty*) 0))

; The three ledger transitions carry `fn-retain-statep'; records are total.
(assert-event (equal (guard 'fn-retain-admissiblep nil (w state)) '(fn-retain-statep s)))
(assert-event (equal (guard 'fn-retain-admit nil (w state)) '(fn-retain-statep s)))
(assert-event (equal (guard 'fn-retain-release nil (w state)) '(fn-retain-statep s)))
(assert-event (equal (guard 'fn-retain-obligation-id nil (w state)) ''t))
(assert-event (equal (guard 'fn-retain-matching-releasep nil (w state)) ''t))
(assert-event (equal (fn-retain-obligation-charge 7) nil))
(assert-event (equal (fn-retain-releases '(10 0 . tail)) nil))

; One archive pin reserves its own charge.
(defconst *retention-archive*
  (fn-retain-admit *retention-empty* "archive-1" "object-a" :archive
                   "operator-release-a" 6))
(assert-event (fn-retain-statep *retention-archive*))
(assert-event (equal (fn-retain-reserved *retention-archive*) 6))
(assert-event (equal (len (fn-retain-pins *retention-archive*)) 1))

; Capacity refusal leaves the whole ledger unchanged before it overcommits.
(assert-event
 (equal (fn-retain-admit *retention-archive* "forward-1" "object-a" :forward
                        "receipt-from-successor" 5)
        *retention-archive*))

; Two independent roots for the same immutable subject have independent charges.
(defconst *retention-two-pins*
  (fn-retain-admit *retention-archive* "forward-1" "object-a" :forward
                   "receipt-from-successor" 4))
(assert-event (fn-retain-statep *retention-two-pins*))
(assert-event (equal (fn-retain-reserved *retention-two-pins*) 10))
(assert-event (equal (len (fn-retain-pins *retention-two-pins*)) 2))

; A successor receipt cannot discharge the archive pin, and wrong subject or
; evidence cannot discharge the forwarding pin.
(assert-event
 (equal (fn-retain-release *retention-two-pins* "archive-1" "object-a" :archive
                          "receipt-from-successor")
        *retention-two-pins*))
(assert-event
 (equal (fn-retain-release *retention-two-pins* "forward-1" "object-b" :forward
                          "receipt-from-successor")
        *retention-two-pins*))
(assert-event
 (equal (fn-retain-release *retention-two-pins* "forward-1" "object-a" :forward
                          "stale-or-unauthorized")
        *retention-two-pins*))

; A matching forwarding receipt frees only its allocation and records release.
(defconst *retention-forward-released*
  (fn-retain-release *retention-two-pins* "forward-1" "object-a" :forward
                     "receipt-from-successor"))
(assert-event (fn-retain-statep *retention-forward-released*))
(assert-event (equal (fn-retain-reserved *retention-forward-released*) 7))
(assert-event (equal (len (fn-retain-pins *retention-forward-released*)) 1))
(assert-event (equal (len (fn-retain-releases *retention-forward-released*)) 1))

; A release record prevents reuse of an obligation identity with another subject.
(assert-event
 (equal (fn-retain-admit *retention-forward-released* "forward-1" "object-b"
                        :forward "other-receipt" 1)
        *retention-forward-released*))

; Archive release is separate and has no clock or automatic-expiry input.
(defconst *retention-all-released*
  (fn-retain-release *retention-forward-released* "archive-1" "object-a"
                     :archive "operator-release-a"))
(assert-event (fn-retain-statep *retention-all-released*))
(assert-event (equal (fn-retain-reserved *retention-all-released*) 2))
(assert-event (equal (len (fn-retain-pins *retention-all-released*)) 0))

; A charge of one is a history-only obligation: release retains that unit.  At
; fixed capacity, repeated admissions and releases eventually refuse new work.
(defconst *retention-history-empty* (fn-retain-initial-state 3))
(defconst *retention-history-one*
  (fn-retain-admit *retention-history-empty* "history-1" "object-1" :archive
                   "release-1" 1))
(defconst *retention-history-one-released*
  (fn-retain-release *retention-history-one* "history-1" "object-1" :archive
                     "release-1"))
(assert-event (equal (fn-retain-reserved *retention-history-one-released*) 1))
(defconst *retention-history-two*
  (fn-retain-admit *retention-history-one-released* "history-2" "object-2"
                   :archive "release-2" 1))
(defconst *retention-history-two-released*
  (fn-retain-release *retention-history-two* "history-2" "object-2" :archive
                     "release-2"))
(defconst *retention-history-three*
  (fn-retain-admit *retention-history-two-released* "history-3" "object-3"
                   :archive "release-3" 1))
(defconst *retention-history-full*
  (fn-retain-release *retention-history-three* "history-3" "object-3" :archive
                     "release-3"))
(assert-event (fn-retain-statep *retention-history-full*))
(assert-event (equal (fn-retain-reserved *retention-history-full*) 3))
(assert-event
 (equal (fn-retain-admit *retention-history-full* "history-4" "object-4"
                        :archive "release-4" 1)
        *retention-history-full*))

; -----------------------------------------------------------------------------
; Teeth for the retention keystones.
;
; `fn-retain-wrong-evidence-does-not-release' is the else-branch of the
; definition with the branch test as its hypothesis; it is `:rule-classes nil'
; and not a registry event.  The keystones with content are the two below: a
; matching release RECORDS its evidence, and releasing one obligation leaves
; every other pin alone.

; A reachable, non-degenerate witness: two independent pins on the SAME
; immutable content subject with different kinds, identities, evidence and
; charges.  A predicate that compared only the subject would identify them,
; and the point of RET-004 is that a forwarding receipt cannot discharge an
; archive pin over the same bytes.
(defconst *ret-teeth-empty* (fn-retain-initial-state 10))
(defconst *ret-teeth-archive*
  (fn-retain-admit *ret-teeth-empty* "archive-1" "object-a" :archive
                   "operator-release-a" 6))
(defconst *ret-teeth-two-pins*
  (fn-retain-admit *ret-teeth-archive* "forward-1" "object-a" :forward
                   "receipt-from-successor" 4))

(assert-event (fn-retain-statep *ret-teeth-two-pins*))
(assert-event (equal (len (fn-retain-pins *ret-teeth-two-pins*)) 2))
(assert-event (equal (fn-retain-reserved *ret-teeth-two-pins*) 10))
(assert-event (null (fn-retain-releases *ret-teeth-two-pins*)))

; The two pins agree on the subject and differ in every other field.
(assert-event
 (equal (fn-retain-obligation-subject
         (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-two-pins*)))
        (fn-retain-obligation-subject
         (fn-retain-find-id "forward-1" (fn-retain-pins *ret-teeth-two-pins*)))))
(assert-event
 (not (equal (fn-retain-obligation-kind
              (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-two-pins*)))
             (fn-retain-obligation-kind
              (fn-retain-find-id "forward-1" (fn-retain-pins *ret-teeth-two-pins*))))))
(assert-event
 (not (equal (fn-retain-obligation-evidence
              (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-two-pins*)))
             (fn-retain-obligation-evidence
              (fn-retain-find-id "forward-1" (fn-retain-pins *ret-teeth-two-pins*))))))

; The exact release is reachable and records its evidence.
(defconst *ret-teeth-released*
  (fn-retain-release *ret-teeth-two-pins* "forward-1" "object-a" :forward
                     "receipt-from-successor"))
(assert-event (fn-retain-statep *ret-teeth-released*))
(assert-event
 (equal (car (fn-retain-releases *ret-teeth-released*))
        (fn-retain-make-release "forward-1" "object-a" :forward
                                "receipt-from-successor")))

; Teeth for `fn-retain-exact-release-records-its-evidence'
;   (implies (and (fn-retain-statep s)
;                 (fn-retain-matching-releasep
;                  (fn-retain-find-id id (fn-retain-pins s)) id subject kind evidence))
;            (equal (car (fn-retain-releases (fn-retain-release s id subject kind evidence)))
;                   (fn-retain-make-release id subject kind evidence)))

; Hypothesis 1, `(fn-retain-statep s)', dropped.  A forged ledger whose release
; history holds a non-release value carries a perfectly matching pin, so the
; second hypothesis holds; `fn-retain-release' refuses a non-state outright, so
; the release history it returns is the forged one, not the new record.  The
; call is outside the guard, so it runs in the logic.
(defconst *ret-teeth-forged*
  (list 10 6 (list (fn-retain-make-obligation "archive-1" "object-a" :archive
                                              "operator-release-a" 6))
        (list :not-a-release-record)))
(assert-event (not (fn-retain-statep *ret-teeth-forged*)))
(assert-event
 (fn-retain-matching-releasep
  (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-forged*))
  "archive-1" "object-a" :archive "operator-release-a"))
(assert-event
 (with-guard-checking :none
  (not (equal (car (fn-retain-releases
                    (fn-retain-release *ret-teeth-forged* "archive-1" "object-a"
                                       :archive "operator-release-a")))
              (fn-retain-make-release "archive-1" "object-a" :archive
                                      "operator-release-a")))))

; Hypothesis 2, the matching-release test, dropped.  A real ledger, a real pin,
; and evidence that does not match it: nothing is recorded, so the head of the
; release history is not the record the theorem names.
(assert-event
 (not (fn-retain-matching-releasep
       (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-two-pins*))
       "archive-1" "object-a" :archive "stale-or-unauthorized")))
(assert-event
 (not (equal (car (fn-retain-releases
                   (fn-retain-release *ret-teeth-two-pins* "archive-1" "object-a"
                                      :archive "stale-or-unauthorized")))
             (fn-retain-make-release "archive-1" "object-a" :archive
                                     "stale-or-unauthorized"))))

; Teeth for `fn-retain-release-preserves-independent-pin'
;   (implies (not (equal other id))
;            (equal (fn-retain-find-id
;                    other (fn-retain-pins (fn-retain-release s id subject kind evidence)))
;                   (fn-retain-find-id other (fn-retain-pins s))))

; The only hypothesis, `(not (equal other id))', dropped: the released pin is
; exactly the one that does not survive, which is the whole point.
(assert-event
 (not (equal (fn-retain-find-id
              "forward-1"
              (fn-retain-pins
               (fn-retain-release *ret-teeth-two-pins* "forward-1" "object-a"
                                  :forward "receipt-from-successor")))
             (fn-retain-find-id "forward-1" (fn-retain-pins *ret-teeth-two-pins*)))))

; And the positive side, so the case above is not passing for a shallow reason:
; the archive pin is untouched by the forwarding release.
(assert-event
 (equal (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-released*))
        (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-two-pins*))))

; `fn-retain-known-obligation-id-is-not-reused' now has one hypothesis.
;
;   (implies (fn-retain-known-idp id (fn-retain-pins s) (fn-retain-releases s))
;            (equal (fn-retain-admit s id subject kind evidence charge) s))
;
; Its former `(fn-retain-statep s)' hypothesis was unnecessary: admission
; refuses every non-state whatever the identity, so no violating value existed
; and the hypothesis was dropped from the theorem.

; The remaining hypothesis, known-idp, dropped: a fresh identity is admitted,
; so admission is not a no-op.
(assert-event
 (not (fn-retain-known-idp "archive-2" (fn-retain-pins *ret-teeth-two-pins*)
                           (fn-retain-releases *ret-teeth-two-pins*))))
(assert-event
 (not (equal (fn-retain-admit *ret-teeth-empty* "archive-2" "object-b" :archive
                              "operator-release-b" 3)
             *ret-teeth-empty*)))

; -----------------------------------------------------------------------------
; Teeth for `fn-retain-admit-refuses-unaffordable-obligation'
; (books/retention-invariants.lisp), RET-002's keystone:
;
;   (implies (> (+ (fn-retain-reserved s) charge) (fn-retain-capacity s))
;            (equal (fn-retain-admit s id subject kind evidence charge) s))
;
; A reachable, non-degenerate witness: an archive pin already holds 6 of a
; capacity-10 ledger, leaving 4 of room.  A forwarding obligation charged 5
; is past the room and hits the theorem's one hypothesis; the same obligation
; charged 4 fits it exactly.
(defconst *ret-cap-teeth-empty* (fn-retain-initial-state 10))
(defconst *ret-cap-teeth-near*
  (fn-retain-admit *ret-cap-teeth-empty* "archive-1" "object-a" :archive
                   "operator-release-a" 6))
(assert-event (equal (fn-retain-reserved *ret-cap-teeth-near*) 6))
(assert-event (equal (fn-retain-capacity *ret-cap-teeth-near*) 10))

; The hypothesis holds at charge 5 (6 + 5 = 11 > 10): the admit is refused,
; and the ledger returned is the exact input, pins and all.
(assert-event
 (> (+ (fn-retain-reserved *ret-cap-teeth-near*) 5)
    (fn-retain-capacity *ret-cap-teeth-near*)))
(assert-event
 (equal (fn-retain-admit *ret-cap-teeth-near* "forward-1" "object-a" :forward
                        "receipt-from-successor" 5)
        *ret-cap-teeth-near*))

; The one hypothesis dropped: charge 4 fits the remaining room exactly
; (6 + 4 = 10 = capacity), so admission is not a no-op and the conclusion --
; the ledger unchanged -- fails without the capacity hypothesis.
(assert-event
 (not (> (+ (fn-retain-reserved *ret-cap-teeth-near*) 4)
         (fn-retain-capacity *ret-cap-teeth-near*))))
(assert-event
 (not (equal (fn-retain-admit *ret-cap-teeth-near* "forward-1" "object-a" :forward
                             "receipt-from-successor" 4)
             *ret-cap-teeth-near*)))
