; The owed Q1 rows must bind their roles without relying on proof attachment.
(in-package "ACL2")
(include-book "q1-bindings")
(include-book "std/testing/must-fail" :dir :system)

(make-event
 (value
  `(must-fail
    (defsquare sq-q1-role-divergence
      :template :q1-loop-iteration :cases-from (list (car *fn2-e1-labels*))
      :bindings
      (list (cons (car *fn2-e1-labels*)
                  (sq-put :id 'sq-q1-role-divergence-row
                    (cdar (sq-q1-bind-cases (list (car *fn2-e1-labels*)) 0
                                           *sq-q1-contract* *sq-q1-sides*)))))
      :contract ,(sq-put :relation 'sq-q1-loop-relatedp *sq-q1-contract*)
      :sides ,*sq-q1-sides*)
    :with-output-off nil)))

(assert-event
 (and (not (assoc-eq 'sq-q1-role-divergence-row
                     (table-alist 'sq-squares (w state))))
      (not (assoc-eq 'sq-q1-role-divergence
                     (table-alist 'sq-coverage (w state))))))
