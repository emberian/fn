; W9: two independent obligations, one subject; duplicate release does nothing.
; Quantified correspondence is proof-only: complete positive antecedents are
; ground ACL2 theorems, paired with executable oracle/effect assertions below.
; No attachment substitutes a boolean for the quantified predicate.
(in-package "ACL2")
(include-book "../../books/retention-obligation-view")
(include-book "must-fail-checked")
(in-theory (disable (:executable-counterpart fn-rov-correspondp)
                    (:executable-counterpart fn-vdc-correspondp)))
(defconst *rov-t-l0* (fn-retain-initial-state 100))
(defconst *rov-t-v0* (fn-rov-build (fn-retain-pins *rov-t-l0*)))
(defconst *rov-t-l1* (fn-retain-admit *rov-t-l0* "hold-a" "subject-a" :archive "a" 7))
(defconst *rov-t-v1* (fn-rov-update *rov-t-l0* *rov-t-l1* *rov-t-v0*))
(defconst *rov-t-l2* (fn-retain-admit *rov-t-l1* "hold-b" "subject-a" :forward "b" 11))
(defconst *rov-t-v2* (fn-rov-update *rov-t-l1* *rov-t-l2* *rov-t-v1*))
(defconst *rov-t-l3* (fn-retain-admit *rov-t-l2* "hold-c" "subject-b" :archive "c" 3))
(defconst *rov-t-v3* (fn-rov-update *rov-t-l2* *rov-t-l3* *rov-t-v2*))
(defconst *rov-t-l4* (fn-retain-release *rov-t-l3* "hold-a" "subject-a" :archive "a"))
(defconst *rov-t-v4* (fn-rov-update *rov-t-l3* *rov-t-l4* *rov-t-v3*))
(defconst *rov-t-dup* (fn-retain-release *rov-t-l4* "hold-a" "subject-a" :archive "a"))
(defconst *rov-t-vdup* (fn-rov-update *rov-t-l4* *rov-t-dup* *rov-t-v4*))

; fn-rov-build-corresponds, fn-rov-update-admit-preserves-correspondence and
; fn-rov-update-release-preserves-correspondence: full quantified relation at
; each reachable prefix. The assertion evaluator cannot run a defun-sk witness.
(defthm rov-t-initial-relation
 (and (fn-retain-obligation-listp (fn-retain-pins *rov-t-l0*))
      (fn-rov-correspondp *rov-t-v0* (fn-retain-pins *rov-t-l0*)))
 :hints (("Goal" :use ((:instance fn-rov-build-corresponds
                        (pins (fn-retain-pins *rov-t-l0*)))))))
(defthm rov-t-arrival-relation
 (and (fn-retain-statep *rov-t-l0*)
      (fn-rov-correspondp *rov-t-v0* (fn-retain-pins *rov-t-l0*))
      (fn-rov-correspondp *rov-t-v1* (fn-retain-pins *rov-t-l1*)))
 :hints (("Goal" :use (rov-t-initial-relation (:instance fn-rov-update-admit-preserves-correspondence
                        (ledger *rov-t-l0*) (view *rov-t-v0*)
                        (id "hold-a") (subject "subject-a") (kind :archive)
                        (evidence "a") (charge 7))))))
(defthm rov-t-two-independent-holds-relation
 (and (fn-retain-statep *rov-t-l1*)
      (fn-rov-correspondp *rov-t-v1* (fn-retain-pins *rov-t-l1*))
      (fn-rov-correspondp *rov-t-v2* (fn-retain-pins *rov-t-l2*)))
 :hints (("Goal" :use (rov-t-arrival-relation (:instance fn-rov-update-admit-preserves-correspondence
                        (ledger *rov-t-l1*) (view *rov-t-v1*)
                        (id "hold-b") (subject "subject-a") (kind :forward)
                        (evidence "b") (charge 11))))))
(defthm rov-t-other-subject-relation
 (and (fn-retain-statep *rov-t-l2*)
      (fn-rov-correspondp *rov-t-v2* (fn-retain-pins *rov-t-l2*))
      (fn-rov-correspondp *rov-t-v3* (fn-retain-pins *rov-t-l3*)))
 :hints (("Goal" :use (rov-t-two-independent-holds-relation (:instance fn-rov-update-admit-preserves-correspondence
                        (ledger *rov-t-l2*) (view *rov-t-v2*)
                        (id "hold-c") (subject "subject-b") (kind :archive)
                        (evidence "c") (charge 3))))))
(defthm rov-t-release-relation
 (and (fn-retain-statep *rov-t-l3*)
      (fn-rov-correspondp *rov-t-v3* (fn-retain-pins *rov-t-l3*))
      (fn-rov-correspondp *rov-t-v4* (fn-retain-pins *rov-t-l4*)))
 :hints (("Goal" :use (rov-t-other-subject-relation (:instance fn-rov-update-release-preserves-correspondence
                        (ledger *rov-t-l3*) (view *rov-t-v3*)
                        (id "hold-a") (subject "subject-a") (kind :archive)
                        (evidence "a"))))))

; Actual arms and complete executable effects, including both contributions.
(assert-event
 (and (fn-retain-statep *rov-t-l0*)
      (fn-retain-admissiblep *rov-t-l0* "hold-a" "subject-a" :archive "a" 7)
      (equal (fn-rov-update-arm *rov-t-l0* *rov-t-l1*) :arrival)
      (equal *rov-t-v1* (fn-rov-arrive (car (fn-retain-pins *rov-t-l1*)) *rov-t-v0*))
      (equal (fn-rov-count *rov-t-v3*) 3)
      (equal (fn-rov-subject "subject-a" *rov-t-v3*) '(2 . 18))
      (equal (fn-rov-subject "subject-b" *rov-t-v3*) '(1 . 3))
      (equal (fn-rov-subject "absent" *rov-t-v3*) '(0 . 0))))
(assert-event
 (and (fn-retain-statep *rov-t-l3*)
      (fn-retain-matching-releasep (fn-retain-find-id "hold-a" (fn-retain-pins *rov-t-l3*))
                                   "hold-a" "subject-a" :archive "a")
      (equal (fn-rov-update-arm *rov-t-l3* *rov-t-l4*) :release)
      (equal *rov-t-v4* (fn-rov-retract (fn-retain-find-id "hold-a" (fn-retain-pins *rov-t-l3*))
                                      *rov-t-v3*))
      (equal (fn-rov-count *rov-t-v4*) (len (fn-retain-pins *rov-t-l4*)))
      (equal (fn-rov-subject "subject-a" *rov-t-v4*) '(1 . 11))
      (equal (fn-rov-subject "subject-b" *rov-t-v4*) '(1 . 3))))
(assert-event
 (and (not (fn-retain-matching-releasep (fn-retain-find-id "hold-a" (fn-retain-pins *rov-t-l4*))
                                       "hold-a" "subject-a" :archive "a"))
      (equal *rov-t-dup* *rov-t-l4*)
      (equal (fn-rov-update-arm *rov-t-l4* *rov-t-dup*) :same)
      (equal *rov-t-vdup* *rov-t-v4*)
      (equal (fn-rov-subject "subject-a" *rov-t-vdup*) '(1 . 11))))
; Mutation witness: a boolean release that clears the subject loses hold-b.
(must-fail-checked (assert-event (equal (fn-rov-subject "subject-a" *rov-t-v4*) '(0 . 0))))
; Corrupted-state witness for count-is-pin-count: replacing the maintained
; count by zero falsifies the conclusion at a reachable nonempty ledger.
(assert-event (not (equal (fn-rov-count (cons 0 (cdr *rov-t-v4*)))
                          (len (fn-retain-pins *rov-t-l4*)))))
