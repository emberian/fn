; SCN-1013, PRF-1101: the retained ledger component of W8.
; These witnesses build nonempty ledgers through actual admission; they do
; not claim that a complete served owner has reached a reclaimable state.
(in-package "ACL2")
(include-book "../../books/history-resource-refinement")

(defconst *hrf-before*
  (fn-retain-admit (fn-retain-initial-state 9)
                  "archive-a" "content-a" :archive "release-a" 8))
(defconst *hrf-after* (fn-hkn-release-retention *hrf-before* "archive-a"))
(defconst *hrf-other*
  (fn-retain-admit (fn-retain-initial-state 9)
                  "archive-b" "content-b" :forward "release-b" 1))

; Positive: complete antecedent and conclusion of the maintenance square,
; with a real resource difference, not an empty or absent-id case.
(assert-event
 (and (fn-retain-statep *hrf-before*) (fn-retain-statep *hrf-after*)
      (consp (fn-retain-pins *hrf-before*))
      (alistp (fn-retain-pins *hrf-before*))
      (equal (fn-hrf-alpha *hrf-after*)
             (fn-hrf-maintain (fn-hrf-alpha *hrf-before*) "archive-a"))
      (equal (fn-hrf-logical *hrf-after*) (fn-hrf-logical *hrf-before*))
      (equal (fn-retain-reserved *hrf-before*) 8)
      (equal (fn-retain-reserved *hrf-after*) 1)
      (not (equal (fn-hrf-resource *hrf-after*)
                  (fn-hrf-resource *hrf-before*)))))

; Corrupted-state hypothesis removal: a non-cons pin whose id is NIL.
; An untyped assoc charge entry can pretend this is a found pin, while the
; concrete release deliberately requires a cons pin.  No other premise.
(defconst *hrf-bad-pins* (fn-retain-make-state 9 8 '(7) nil))
(assert-event
 (with-guard-checking :none
   (and (not (alistp (fn-retain-pins *hrf-bad-pins*)))
        (not (equal
              (fn-hrf-alpha (fn-hkn-release-retention *hrf-bad-pins* nil))
              (fn-hrf-maintain (fn-hrf-alpha *hrf-bad-pins*) nil))))))

; Positive for the literal common-admission theorem.  Both admit; each
; keeps its own charge while adding the same logical obligation.
(assert-event
 (and (equal (fn-hrf-logical *hrf-before*) (fn-hrf-logical *hrf-after*))
      (fn-retain-admissiblep *hrf-before* "next" "next-subject" :forward "next-evidence" 1)
      (fn-retain-admissiblep *hrf-after* "next" "next-subject" :forward "next-evidence" 1)
      (equal
       (fn-hrf-logical (fn-retain-admit *hrf-before* "next" "next-subject" :forward "next-evidence" 1))
       (fn-hrf-logical (fn-retain-admit *hrf-after* "next" "next-subject" :forward "next-evidence" 1)))))

; Remove logical equivalence, affirm both admission hypotheses, refute
; the conclusion.  Both ledgers are nonempty reachable admission states.
(assert-event
 (and (not (equal (fn-hrf-logical *hrf-before*) (fn-hrf-logical *hrf-other*)))
      (fn-retain-admissiblep *hrf-before* "next" "next-subject" :forward "next-evidence" 1)
      (fn-retain-admissiblep *hrf-other* "next" "next-subject" :forward "next-evidence" 1)
      (not (equal
       (fn-hrf-logical (fn-retain-admit *hrf-before* "next" "next-subject" :forward "next-evidence" 1))
       (fn-hrf-logical (fn-retain-admit *hrf-other* "next" "next-subject" :forward "next-evidence" 1))))))

; Removing LEFT admission: only freed resources admit the two-unit request.
; The refused event remains present and must not be erased by a checker.
(assert-event
 (and (equal (fn-hrf-logical *hrf-before*) (fn-hrf-logical *hrf-after*))
      (not (fn-retain-admissiblep *hrf-before* "next" "next-subject" :forward "next-evidence" 2))
      (fn-retain-admissiblep *hrf-after* "next" "next-subject" :forward "next-evidence" 2)
      (not (equal
       (fn-hrf-logical (fn-retain-admit *hrf-before* "next" "next-subject" :forward "next-evidence" 2))
       (fn-hrf-logical (fn-retain-admit *hrf-after* "next" "next-subject" :forward "next-evidence" 2))))))

; Removing RIGHT admission, with every retained hypothesis affirmed.
(assert-event
 (and (equal (fn-hrf-logical *hrf-after*) (fn-hrf-logical *hrf-before*))
      (fn-retain-admissiblep *hrf-after* "next" "next-subject" :forward "next-evidence" 2)
      (not (fn-retain-admissiblep *hrf-before* "next" "next-subject" :forward "next-evidence" 2))
      (not (equal
       (fn-hrf-logical (fn-retain-admit *hrf-after* "next" "next-subject" :forward "next-evidence" 2))
       (fn-hrf-logical (fn-retain-admit *hrf-before* "next" "next-subject" :forward "next-evidence" 2))))))

; Positive release: actual matching evidence discharges the same pin and
; retains the same release history, while the resource refunds differ.
(assert-event
 (and (fn-retain-statep *hrf-before*) (fn-retain-statep *hrf-after*)
      (equal (fn-hrf-logical *hrf-before*) (fn-hrf-logical *hrf-after*))
      (consp (fn-retain-pins *hrf-before*))
      (not (fn-retain-pins
            (fn-retain-release *hrf-before* "archive-a" "content-a" :archive "release-a")))
      (equal
       (fn-hrf-logical (fn-retain-release *hrf-before* "archive-a" "content-a" :archive "release-a"))
       (fn-hrf-logical (fn-retain-release *hrf-after* "archive-a" "content-a" :archive "release-a")))))

; Corrupted-state removals: wrong accounting makes a ledger invalid while
; its logical projection still equals the valid counterpart.
(defconst *hrf-bad-accounting*
 (fn-retain-make-state 9 0 (fn-retain-pins *hrf-before*) nil))
(assert-event
 (with-guard-checking :none
  (and (not (fn-retain-statep *hrf-bad-accounting*))
       (fn-retain-statep *hrf-before*)
       (equal (fn-hrf-logical *hrf-bad-accounting*) (fn-hrf-logical *hrf-before*))
       (not (equal
        (fn-hrf-logical (fn-retain-release *hrf-bad-accounting* "archive-a" "content-a" :archive "release-a"))
        (fn-hrf-logical (fn-retain-release *hrf-before* "archive-a" "content-a" :archive "release-a")))))))
(assert-event
 (with-guard-checking :none
  (and (fn-retain-statep *hrf-before*)
       (not (fn-retain-statep *hrf-bad-accounting*))
       (equal (fn-hrf-logical *hrf-before*) (fn-hrf-logical *hrf-bad-accounting*))
       (not (equal
        (fn-hrf-logical (fn-retain-release *hrf-before* "archive-a" "content-a" :archive "release-a"))
        (fn-hrf-logical (fn-retain-release *hrf-bad-accounting* "archive-a" "content-a" :archive "release-a")))))))

; Remove release equivalence, retain both valid-ledger premises.
(assert-event
 (and (fn-retain-statep *hrf-before*) (fn-retain-statep *hrf-other*)
      (not (equal (fn-hrf-logical *hrf-before*) (fn-hrf-logical *hrf-other*)))
      (not (equal
       (fn-hrf-logical (fn-retain-release *hrf-before* "archive-a" "content-a" :archive "release-a"))
       (fn-hrf-logical (fn-retain-release *hrf-other* "archive-a" "content-a" :archive "release-a"))))))

; Mutation: a maintenance implementation that drops an obligation's
; evidence does not preserve L, even when it reduces the charge correctly.
(defconst *hrf-mutated*
 (fn-retain-make-state 9 1
  (list (fn-retain-make-obligation "archive-a" "content-a" :archive "wrong-evidence" 1)) nil))
(assert-event
 (and (fn-retain-statep *hrf-mutated*)
      (equal (fn-hrf-resource *hrf-mutated*) (fn-hrf-resource *hrf-after*))
      (not (equal (fn-hrf-logical *hrf-mutated*) (fn-hrf-logical *hrf-before*)))))
