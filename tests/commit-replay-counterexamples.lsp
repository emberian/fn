; Reproduce both counterexamples against the two transaction obligations.
; Load from the repository root. Either event becomes false when its example
; is excluded or the replay supplies the evidence the obligation requires.
(in-package "ACL2")
(include-book "tests/commit-txn-unit")

(defthm fn2-commit-outcome-refuted-by-bypassed-notify
  (not (fn2-commit-txn-outcome-evidence$owed
        (list (list (fn2-ctu-acceptance 0)))
        '((:admit 0) (:bypass-notify 0))
        0))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (union-theories '(fn2-commit-txn-outcome-evidence$owed
                             (:e fn2-ctu-acceptance) (:e fn2-commit-txn-proof-run)
                             (:e fn2-ctp-initialized) (:e fn2-commit-txn-outcome-evidencep))
                           (theory 'minimal-theory)))))

(defthm fn2-commit-records-refuted-by-keyed-start
  (not (fn2-commit-txn-records-verbatim$owed
        (list (list (fn2-ctu-acceptance 0)))
        (cons '(:start 0 1 1 0) (make-list 65 :initial-element '(:auto 26)))
        0))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (union-theories '(fn2-commit-txn-records-verbatim$owed
                             (:e fn2-ctu-acceptance) (:e make-list-ac)
                             (:e fn2-commit-txn-proof-run) (:e fn2-ctp-initialized)
                             (:e fn2-commit-txn-records-verbatimp))
                           (theory 'minimal-theory)))))
