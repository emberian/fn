; Retained-world ground probe; same theorem as the evidence book.
(defthm fn2-checkpoint-member-fields-type-readonly-removal-ground
 (fn2-checkpoint-member-fields-type-readonly-removal-check)
 :rule-classes nil
 :hints (("Goal" :in-theory
  (set-difference-theories
   (union-theories (function-theory :here)
    (union-theories (executable-counterpart-theory :here) (theory 'minimal-theory)))
   '((:executable-counterpart fn2-checkpoint-member-fields-type-readonly-removal-check)
     (:executable-counterpart create-fn2-checkpoints)
     (:executable-counterpart create-fn2-checkpoint-refs)
     (:executable-counterpart create-fn2-checkpoint-bytes)
     (:executable-counterpart create-fn2-fields)
     (:executable-counterpart create-fn2-pool)
     (:executable-counterpart fn2-checkpoints-set-checkpoint)
     (:executable-counterpart update-fn2-checkpoints-checkpoint$ai)
     (:executable-counterpart fn2-checkpoints-checkpoint)
     (:executable-counterpart fn2-checkpoints-checkpoint$ai)
     (:executable-counterpart fn2-checkpoint-installation-pack-member)
     (:executable-counterpart fn2-fields-set-value)
     (:executable-counterpart update-fn2-fields-value$ai))))))
