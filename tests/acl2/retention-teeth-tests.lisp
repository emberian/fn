; Teeth for the retention keystones.
;
; The 2026-09-18 review's first §4 row is about this book:
; `fn-retain-wrong-evidence-does-not-release' is the else-branch of the
; definition with the branch test as its hypothesis, and `tools/ledger.py'
; flags it SUSPECT for exactly that shape.  The keystones with content are the
; two below: the one that says a matching release RECORDS its evidence, and the
; one that says releasing one obligation leaves every other pin alone.
;
; Negative cases are ground; ACL2 computes the counterexample.

(in-package "ACL2")
(include-book "../../books/retention-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.
;
; Two independent pins on the SAME immutable content subject with different
; kinds, identities, evidence and charges.  Separating them by their weakest
; clause is not enough: a predicate that compared only the subject would
; identify them, and the point of RET-004 is that a forwarding receipt cannot
; discharge an archive pin over the same bytes.

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

; -----------------------------------------------------------------------------
; Teeth for `fn-retain-exact-release-records-its-evidence'
;   (implies (and (fn-retain-statep s)
;                 (fn-retain-matching-releasep
;                  (fn-retain-find-id id (fn-retain-pins s)) id subject kind evidence))
;            (equal (car (fn-retain-releases (fn-retain-release s id subject kind evidence)))
;                   (fn-retain-make-release id subject kind evidence)))

; Hypothesis 1, `(fn-retain-statep s)', dropped.  A forged ledger whose release
; history holds a non-release value carries a perfectly matching pin, so the
; second hypothesis holds; `fn-retain-release' refuses a non-state outright, so
; the release history it returns is the forged one, not the new record.
(defconst *ret-teeth-forged*
  (list 10 6 (list (fn-retain-make-obligation "archive-1" "object-a" :archive
                                              "operator-release-a" 6))
        (list :not-a-release-record)))
(assert-event (not (fn-retain-statep *ret-teeth-forged*)))
(assert-event
 (fn-retain-matching-releasep
  (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-forged*))
  "archive-1" "object-a" :archive "operator-release-a"))

(local
 (must-fail
  (defthm ret-teeth-records-evidence-without-statep
    (equal (car (fn-retain-releases
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

(local
 (must-fail
  (defthm ret-teeth-records-evidence-without-match
    (equal (car (fn-retain-releases
                 (fn-retain-release *ret-teeth-two-pins* "archive-1" "object-a"
                                    :archive "stale-or-unauthorized")))
           (fn-retain-make-release "archive-1" "object-a" :archive
                                   "stale-or-unauthorized")))))

; -----------------------------------------------------------------------------
; Teeth for `fn-retain-release-preserves-independent-pin'
;   (implies (not (equal other id))
;            (equal (fn-retain-find-id
;                    other (fn-retain-pins (fn-retain-release s id subject kind evidence)))
;                   (fn-retain-find-id other (fn-retain-pins s))))

; The only hypothesis, `(not (equal other id))', dropped: the released pin is
; exactly the one that does not survive, which is the whole point.
(local
 (must-fail
  (defthm ret-teeth-independent-pin-without-distinctness
    (equal (fn-retain-find-id
            "forward-1"
            (fn-retain-pins
             (fn-retain-release *ret-teeth-two-pins* "forward-1" "object-a"
                                :forward "receipt-from-successor")))
           (fn-retain-find-id "forward-1" (fn-retain-pins *ret-teeth-two-pins*))))))

; And the positive side, so the case above is not passing for a shallow reason:
; the archive pin is untouched by the forwarding release.
(assert-event
 (equal (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-released*))
        (fn-retain-find-id "archive-1" (fn-retain-pins *ret-teeth-two-pins*))))

; -----------------------------------------------------------------------------
; `fn-retain-known-obligation-id-is-not-reused': one hypothesis has no teeth.
;
;   (implies (and (fn-retain-statep s)                       ; H1
;                 (fn-retain-known-idp id (fn-retain-pins s)
;                                      (fn-retain-releases s)))  ; H2
;            (equal (fn-retain-admit s id subject kind evidence charge) s))
;
; H1 is unnecessary.  `fn-retain-admit' refuses unless
; `fn-retain-admissiblep' holds, and that predicate's first conjunct is
; `(fn-retain-statep s)' (books/retention.lisp:202-213), so admission is
; already a no-op on every non-state whatever H2 says.  No violating witness
; exists and none is forged here; recorded as a finding in HANDOFF.md.

; Hypothesis 2, known-idp, dropped: a fresh identity is admitted, so admission
; is not a no-op.
(assert-event
 (not (fn-retain-known-idp "archive-2" (fn-retain-pins *ret-teeth-two-pins*)
                           (fn-retain-releases *ret-teeth-two-pins*))))

(local
 (must-fail
  (defthm ret-teeth-not-reused-without-known-id
    (equal (fn-retain-admit *ret-teeth-empty* "archive-2" "object-b" :archive
                            "operator-release-b" 3)
           *ret-teeth-empty*))))
