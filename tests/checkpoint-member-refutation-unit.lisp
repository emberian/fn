; Registry bridge only: actual counterexample and positive fixture remain unchanged.
(in-package "ACL2")
(include-book "checkpoint-member-readonly-removal")
(include-book "../books/assurance-completion")

(defun-nx fn2-checkpoint-member-refutation-arguments ()
 (let* ((fn2-checkpoints (fn2-checkpoints-init 1 (create-fn2-checkpoints)))
        (fn2-checkpoints (fn2-checkpoints-set-state 0 *fn2-checkpoint-state-checked* fn2-checkpoints))
        ; Only the readonly checkpoint value loses its u60 recognizer.
        ; The actual accessor/setter retain this logical value; no twin packer.
        (fn2-checkpoints (fn2-checkpoints-set-checkpoint 0 -1 fn2-checkpoints))
        (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 (create-fn2-checkpoint-refs)))
        (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 (create-fn2-checkpoint-bytes)))
        (fn2-fields (fn2-fields-init
                     (+ *fn2-format-txn-record-num-fields* *fn2-format-checkpoint-installation-num-fields*)
                     (create-fn2-fields)))
        (fn2-pool (fn2-pool-columns-init 1 (create-fn2-pool)))
        (fn2-pool (resize-fn2-pool-data (fn2-checkpoint-installation-member-capacity) fn2-pool))
        (fn2-pool (fn2-pool-set-cap 0 (fn2-checkpoint-installation-member-capacity) fn2-pool))
        (fn2-pool (fn2-pool-set-state 0 *fn2-pool-state-workspace* fn2-pool)))
  (list 0 0 0 0 0 0 0 fn2-checkpoints fn2-checkpoint-refs
        fn2-checkpoint-bytes fn2-fields fn2-pool)))

; This is an exact closed instance of the original statement, not its guarded
; replacement and not an arbitrary predicate named "counterexample".
(defthm fn2-checkpoint-member-original-refuted-instance
 (not (fn2-checkpoint-installation-pack-member-fields-type$owed
        (nth 0 (fn2-checkpoint-member-refutation-arguments))
        (nth 1 (fn2-checkpoint-member-refutation-arguments))
        (nth 2 (fn2-checkpoint-member-refutation-arguments))
        (nth 3 (fn2-checkpoint-member-refutation-arguments))
        (nth 4 (fn2-checkpoint-member-refutation-arguments))
        (nth 5 (fn2-checkpoint-member-refutation-arguments))
        (nth 6 (fn2-checkpoint-member-refutation-arguments))
        (nth 7 (fn2-checkpoint-member-refutation-arguments))
        (nth 8 (fn2-checkpoint-member-refutation-arguments))
        (nth 9 (fn2-checkpoint-member-refutation-arguments))
        (nth 10 (fn2-checkpoint-member-refutation-arguments))
        (nth 11 (fn2-checkpoint-member-refutation-arguments))
))
 :rule-classes nil
 :hints (("Goal"
          :use fn2-checkpoint-member-fields-type-readonly-removal-ground
          :in-theory (e/d (fn2-checkpoint-member-refutation-arguments
                            fn2-checkpoint-member-fields-type-readonly-removal-check
                            fn2-checkpoint-installation-pack-member-fields-type$owed)
                           (fn2-checkpoint-installation-pack-member)))))

(defsquare-refuted fn2-checkpoint-installation-pack-member-fields-type
 fn2-checkpoint-member-original-refuted-instance
 fn2-checkpoint-installation-pack-member-fields-type-under-guard)
(assert-event
 (member-eq 'fn2-checkpoint-installation-pack-member-fields-type
            (fn2-owed-names (w state))))

; Refutation is an established failure of the original, not a green completion.
(assert-event
 (let* ((name 'fn2-checkpoint-installation-pack-member-fields-type)
        (row (fn2-decl-row (list :square name) (w state)))
        (problems (fn2-assurance-row-problems name nil (w state))))
  (and (member-equal (list name :unproved) problems)
       (member-equal
        (list name :refuted-original :candidate-replacement-link-unverified
              'fn2-checkpoint-installation-pack-member-fields-type-under-guard)
        problems)
       (equal (nth 2 (fn2-square-counts (list (cons name row)))) 0))))
