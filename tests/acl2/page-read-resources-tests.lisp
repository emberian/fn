; Admission algebra witnesses, not a served allocator completion claim.
(in-package "ACL2")
(include-book "../../books/page-read-resources")
(include-book "std/testing/assert-bang" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-prs-issue (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prs-worker-demand (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-prs-release-reusable (w state)) :common-lisp-compliant)))

(defconst *prs-budget* '(10000000 4096 4 2 3))
(defconst *prs-used* '(10 0 1 0 0))
(defconst *prs-rescue* '(20 4096 1 1 1))
(defconst *prs-empty* '(0 0 0 0 0))
(defconst *prs-worker* (fn-prs-worker-demand 1 0 1 0))
(defconst *prs-first*
  (mv-list 3 (fn-prs-issue *prs-budget* *prs-used* *prs-rescue* *prs-empty* 0 3 *prs-worker*)))

; Actual constructor units: 2*(1 protected octet + 32 trailer) + 1KiB stack.
(assert! (equal *prs-worker* '(1090 0 0 1 1)))
(assert! (equal (fn-prs-incarnation-demand 8) '(16 0 1 0 0)))
(assert! (fn-prs-fundedp *prs-budget* *prs-used* *prs-rescue* *prs-empty*))
(assert!
 (and (equal (mv-nth 0 *prs-first*) :admitted)
      (fn-prs-fundedp *prs-budget* *prs-used* *prs-rescue* (mv-nth 2 *prs-first*))
      (natp (mv-nth 1 *prs-first*))
      (<= (mv-nth 1 *prs-first*) 3)))
(assert! (equal *prs-first* '(:admitted 1 (1090 0 0 1 1))))

; The rescue worker slot cannot be borrowed by a second ordinary worker.
(defconst *prs-second*
  (mv-list 3 (fn-prs-issue *prs-budget* *prs-used* *prs-rescue* (mv-nth 2 *prs-first*)
                1 3 *prs-worker*)))
(assert!
 (and (not (equal (mv-nth 0 *prs-second*) :admitted))
      (equal (mv-nth 0 *prs-second*) :read-resources-unavailable)
      (equal (mv-nth 1 *prs-second*) 1)
      (equal (mv-nth 2 *prs-second*) (mv-nth 2 *prs-first*))))
(assert!
 (and (not (equal (mv-nth 0 *prs-second*) :admitted))
      (equal (mv-list 2 (fn-prs-repeat 64 *prs-budget* *prs-used* *prs-rescue*
                            (mv-nth 2 *prs-first*) 1 3 *prs-worker*))
             (list 1 (mv-nth 2 *prs-first*)))))

; Hypothesis removal: omitting refusal from the repeated-state theorem
; fails with the actually admitted first request; no retained hypotheses.
(assert!
 (and (equal (mv-nth 0 *prs-first*) :admitted)
      (not (equal (mv-list 2 (fn-prs-repeat 1 *prs-budget* *prs-used* *prs-rescue*
                                 *prs-empty* 0 3 *prs-worker*))
                  (list 0 *prs-empty*)))))

; Identity exhaustion is terminal by name with no wraparound or allocation.
(assert!
 (equal (mv-list 3 (fn-prs-issue *prs-budget* *prs-used* *prs-rescue* *prs-empty* 3 3 *prs-worker*))
        (list :read-identities-exhausted 3 *prs-empty*)))

; Matching real completion may refund reusable coordinates, never IDs.
; This test is not authorization to settle cancellation or stale callbacks.
(assert!
 (equal (fn-prs-release-reusable (mv-nth 2 *prs-first*) *prs-worker*)
        '(0 0 0 0 1)))
(assert!
 (equal (nth 4 (fn-prs-release-reusable (mv-nth 2 *prs-first*) *prs-worker*))
        (nfix (nth 4 (mv-nth 2 *prs-first*)))))

; Corrupted-state witness: a malformed dimension does not issue.
(assert!
 (equal (mv-list 3 (fn-prs-issue '(10) *prs-used* *prs-rescue* *prs-empty* 0 3 *prs-worker*))
        (list :invalid-resource-state 0 *prs-empty*)))

; Mutation witness: spending the reserved execution slot is outside funding.
(assert!
 (not (fn-prs-fundedp *prs-budget* *prs-used* *prs-rescue*
                      (fn-prs-plus (mv-nth 2 *prs-first*) *prs-worker*))))
