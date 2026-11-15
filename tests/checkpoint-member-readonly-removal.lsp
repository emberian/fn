; Retained-member-world probe ONLY, after loading the companion .lisp source.
; Success proves the concrete original-H / not-original-C ground witness.
; Failure remains unresolved and must not be reported as a counterexample.
(defthm fn2-checkpoint-member-fields-type-readonly-removal-ground
 (fn2-checkpoint-member-fields-type-readonly-removal-check)
 :rule-classes nil
 :hints (("Goal" :in-theory
          (union-theories
           '((:definition fn2-checkpoint-member-fields-type-readonly-removal-check))
           (executable-counterpart-theory :here)))))
