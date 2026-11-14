; Reprove an actual generated arm contract after the executor presentation
; rewrite is installed.  The original contract must not prove itself.
(in-package "ACL2")
(include-book "machine-budget-turn-fixture")
(include-book "std/testing/must-fail" :dir :system)

(local (in-theory (disable fn2-scribe-run-success-charge)))
(assert-event
 (getpropc 'fn2-core-stopped-p-is-exec-stop 'theorem nil (w state)))

(make-event
 (let* ((event
         (fn2-machine-success-charge-event
          'fn2-scribe-run 'fn2-scribe-arm-charge-ok-p
          (getpropc 'fn2-scribe-run 'guard t (w state))
          '(fn2-machine-contract-check fn2-machine-refuse-phase fn2-machine-idle
            fn2-machine-finish fn2-machine-charge fn2-machine-charge-kindp
            fn2-machine-refuse-charge fn2-machine-refuse-write fn2-machine-phase
            fn2-scribe-arm-ok-p fn2-scribe-row-phase fn2-scribe-charge)))
        (goal (car (cadr (member-eq :hints event))))
        (theory (cadr (member-eq :in-theory (cdr goal)))))
  (if (not (and (eq (car theory) 'remove-equal)
                (equal (cadr theory)
                       '(quote (:rewrite fn2-core-stopped-p-is-exec-stop)))))
      (er soft 'machine-success-charge-context-unit
          "Expected the generated core stop theory cut.")
    (value
     `(progn
        ; Remove only the proposed cut.  Same formula, same run function,
        ; same guard: the old consumer-polluted hint must refuse.
        (must-fail
         (defthm fn2-scribe-success-charge-old-theory-control
          ,(caddr event)
          :hints (("Goal" :in-theory ,(caddr theory)))))
        (defthm fn2-scribe-success-charge-after-executor
         ,@(cddr event)))))))

; Lower-layer declarations precede executor-access.  Removing a quoted rune
; must also work when that rune does not exist in the current world.
(assert-event
 (not (getpropc 'fn2-success-charge-never-declared 'theorem nil (w state))))
(defthm fn2-success-charge-absent-rune-control
 (equal (car (cons x y)) x)
 :hints (("Goal" :in-theory
          (remove-equal '(:rewrite fn2-success-charge-never-declared)
                        (current-theory :here)))))
