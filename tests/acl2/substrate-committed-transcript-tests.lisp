; Literal resume/publication witnesses. Toy crypto is not cryptographic evidence.
(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/codec-attach")
(include-book "../../books/substrate-committed-transcript")
(defun fn-stcet-run (evidence cursor authority keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (mv-let (next cursor2 verdict) (fn-stce-resume evidence cursor authority keyring)
    (list next cursor2 verdict)))
(defconst *stcet-key* (make-list 32 :initial-element 11))
(make-event (list 'defconst '*stcet-pk* (list 'quote (fn-sig-public-key *stcet-key*))))
(make-event (list 'defconst '*stcet-authority* (list 'quote (fn-prin-id *stcet-pk* '(9)))))
(make-event (list 'defconst '*stcet-keyring* (list 'quote (list (cons *stcet-authority* *stcet-pk*)))))
(make-event (list 'defconst '*stcet-c1* (list 'quote (fn-me-commit '(1) 0 *stcet-authority* :remove '(2)))))
(make-event (list 'defconst '*stcet-c2* (list 'quote (fn-me-commit '(1) 0 *stcet-authority* :remove '(3)))))
(make-event (list 'defconst '*stcet-s1* (list 'quote (fn-stmt-sign *stcet-key* *stcet-authority* 0 1 nil :policy (fn-stx-commit-encode *stcet-c1*)))))
(make-event (list 'defconst '*stcet-s2* (list 'quote (fn-stmt-sign *stcet-key* *stcet-authority* 0 2 nil :policy (fn-stx-commit-encode *stcet-c2*)))))
(make-event (list 'defconst '*stcet-e1* (list 'quote (fn-stce-entry "fn.test" *stcet-authority* *stcet-s1* *stcet-c1*))))
(make-event (list 'defconst '*stcet-e2* (list 'quote (fn-stce-entry "fn.test" *stcet-authority* *stcet-s2* *stcet-c2*))))
(defconst *stcet-next* '(:select nil nil nil))
(make-event (list 'defconst '*stcet-scan* (list 'quote (list :scan *stcet-e2* (list *stcet-e1*) nil nil (list *stcet-e1*) *stcet-next*))))
(make-event (list 'defconst '*stcet-publish* (list 'quote (nth 1 (fn-stcet-run (list *stcet-e1*) *stcet-scan* *stcet-authority* *stcet-keyring*)))))
; Nondegenerate carrier/collision premises, not just a refusal token.
(assert-event (fn-stce-entryp *stcet-e1*))
(assert-event (fn-stce-entryp *stcet-e2*))
(assert-event (fn-prin-keyringp *stcet-keyring*))
(assert-event (fn-prin-verifiedp *stcet-s1* *stcet-keyring*))
(assert-event (fn-prin-verifiedp *stcet-s2* *stcet-keyring*))
(assert-event (not (equal *stcet-c1* *stcet-c2*)))
(assert-event (equal (fn-me-commit-id *stcet-c1*) (fn-me-commit-id *stcet-c2*)))
(assert-event (fn-stce-id-collisionp *stcet-e2* (list *stcet-e1*) *stcet-keyring*))
(assert-event (equal (nth 2 (fn-stcet-run (list *stcet-e1*) *stcet-publish* *stcet-authority* *stcet-keyring*)) :commit-id-conflict))
; PRF-1176: full literal antecedent/conclusion of existing-evidence retention.
(assert-event
 (let ((evidence (list *stcet-e1*)) (old *stcet-e1*))
   (and (member-equal old evidence)
        (member-equal old (nth 0 (fn-stcet-run evidence *stcet-publish* *stcet-authority* *stcet-keyring*))))))
; Publication theorem: duplicate implication affirmatively checked.
(assert-event
 (and (fn-stce-scan-cursorp *stcet-publish*)
      (atom (nth 2 *stcet-publish*))
      (implies (nth 3 *stcet-publish*) (member-equal (nth 1 *stcet-publish*) (list *stcet-e1*)))
      (member-equal (nth 1 *stcet-publish*)
                    (nth 0 (fn-stcet-run (list *stcet-e1*) *stcet-publish* *stcet-authority* *stcet-keyring*)))))
; Exact retransmission: scanning the identical envelope yields a duplicate
; witness and adds no bytes or authority effects.
(make-event (list 'defconst '*stcet-repeat-scan* (list 'quote (list :scan *stcet-e1* (list *stcet-e1*) nil nil (list *stcet-e1*) *stcet-next*))))
(make-event (list 'defconst '*stcet-repeat-publish* (list 'quote (nth 1 (fn-stcet-run (list *stcet-e1*) *stcet-repeat-scan* *stcet-authority* *stcet-keyring*)))))
(assert-event (nth 3 *stcet-repeat-publish*))
(assert-event (not (nth 4 *stcet-repeat-publish*)))
(assert-event (equal (nth 0 (fn-stcet-run (list *stcet-e1*) *stcet-repeat-publish* *stcet-authority* *stcet-keyring*)) (list *stcet-e1*)))
(assert-event (equal (nth 2 (fn-stcet-run (list *stcet-e1*) *stcet-repeat-publish* *stcet-authority* *stcet-keyring*)) :retransmission))
; Hypothesis-removal witness, corrupted cursor: every retained premise holds,
; the omitted duplicate-witness premise and conclusion both fail.
(make-event (list 'defconst '*stcet-corrupt* (list 'quote (list :scan *stcet-e2* nil t nil nil *stcet-next*))))
(assert-event
 (and (fn-stce-scan-cursorp *stcet-corrupt*)
      (atom (nth 2 *stcet-corrupt*))
      (not (implies (nth 3 *stcet-corrupt*) (member-equal (nth 1 *stcet-corrupt*) nil)))
      (not (member-equal (nth 1 *stcet-corrupt*)
                         (nth 0 (fn-stcet-run nil *stcet-corrupt* *stcet-authority* *stcet-keyring*))))))

(assert-event
 (and (fn-stce-scan-cursorp *stcet-publish*)
      (atom (nth 2 *stcet-publish*)) (nth 4 *stcet-publish*)
      (not (equal (nth 4 *stcet-publish*) :equivocation))
      (fn-prin-verifiedp (nth 2 (nth 1 *stcet-publish*)) *stcet-keyring*)
      (nth 1 (nth 1 *stcet-publish*))
      (equal (fn-stmt-creator (nth 2 (nth 1 *stcet-publish*)))
             (nth 1 (nth 1 *stcet-publish*)))
      (equal (fn-me-commit-actor (nth 3 (nth 1 *stcet-publish*)))
             (nth 1 (nth 1 *stcet-publish*)))
      (equal (nth 2 (fn-stcet-run (list *stcet-e1*) *stcet-publish*
                                  *stcet-authority* *stcet-keyring*))
             :commit-id-conflict)))
(assert-event
 (and (fn-stce-cursor-shapep *stcet-scan*)
      (fn-stce-cursor-witnessp *stcet-scan* (list *stcet-e1*))
      (fn-stce-cursor-witnessp
       (nth 1 (fn-stcet-run (list *stcet-e1*) *stcet-scan* *stcet-authority* *stcet-keyring*))
       (nth 0 (fn-stcet-run (list *stcet-e1*) *stcet-scan* *stcet-authority* *stcet-keyring*)))))
(assert-event
 (and (fn-stce-statementsp (list *stcet-s1*))
      (fn-stce-cursor-shapep (fn-stce-start (list *stcet-s1*) '("fn.test")))))
(assert-event
 (and (true-listp (list *stcet-e1*))
      (fn-stce-cursor-shapep (fn-stce-start (list *stcet-s1*) '("fn.test")))
      (fn-stce-cursor-shapep
       (nth 1 (fn-stcet-run (list *stcet-e1*)
                            (fn-stce-start (list *stcet-s1*) '("fn.test"))
                            *stcet-authority* *stcet-keyring*)))))
; Shape hypothesis-removal teeth: malformed evidence is not a legitimate
; saved transcript; its dotted tail fails the newly constructed scan shape.
(assert-event
 (let ((bad (cons *stcet-e1* :dotted)))
   (and (not (true-listp bad))
        (fn-stce-cursor-shapep (fn-stce-start (list *stcet-s1*) '("fn.test")))
        (not (fn-stce-cursor-shapep
              (nth 1 (fn-stcet-run bad
                                   (fn-stce-start (list *stcet-s1*) '("fn.test"))
                                   *stcet-authority* *stcet-keyring*)))))))
(assert-event
 (and (not (fn-stce-statementsp '(bad)))
      (not (fn-stce-cursor-shapep (fn-stce-start '(bad) '("fn.test"))))))

(make-event (list 'defconst '*stcet-sfork* (list 'quote (fn-stmt-sign *stcet-key* *stcet-authority* 0 1 nil :policy (fn-stx-commit-encode *stcet-c2*)))))
(make-event (list 'defconst '*stcet-efork* (list 'quote (fn-stce-entry "fn.test" *stcet-authority* *stcet-sfork* *stcet-c2*))))
(make-event (list 'defconst '*stcet-fork-scan* (list 'quote (list :scan *stcet-efork* (list *stcet-e1*) nil nil (list *stcet-e1*) *stcet-next*))))
(assert-event
 (and (fn-stce-scan-cursorp *stcet-fork-scan*) (consp (nth 2 *stcet-fork-scan*))
      (fn-stce-slot-conflictp (nth 1 *stcet-fork-scan*) (car (nth 2 *stcet-fork-scan*)) *stcet-keyring*)
      (equal (nth 4 (nth 1 (fn-stcet-run (list *stcet-e1*) *stcet-fork-scan* *stcet-authority* *stcet-keyring*))) :equivocation)))
