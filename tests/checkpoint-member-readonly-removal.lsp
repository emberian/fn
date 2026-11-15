; Retained-member-world probe ONLY, after loading the companion .lisp source.
; Success proves the concrete original-H / not-original-C ground witness.
; Failure remains unresolved and must not be reported as a counterexample.
(defthm fn2-checkpoint-member-fields-type-readonly-removal-ground
 (fn2-checkpoint-member-fields-type-readonly-removal-check)
 :rule-classes nil
 :hints (("Goal" :in-theory
          (union-theories
           '((:definition fn2-checkpoint-member-fields-type-readonly-removal-check)
             (:definition create-fn2-checkpoints)
             (:definition create-fn2-checkpoint-refs)
             (:definition create-fn2-checkpoint-bytes)
             (:definition create-fn2-fields)
             (:definition create-fn2-pool))
           (set-difference-theories
            (executable-counterpart-theory :here)
            '((:executable-counterpart create-fn2-checkpoints)
              (:executable-counterpart create-fn2-checkpoint-refs)
              (:executable-counterpart create-fn2-checkpoint-bytes)
              (:executable-counterpart create-fn2-fields)
              (:executable-counterpart create-fn2-pool)))))))
