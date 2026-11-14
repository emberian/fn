; Q1/reference imports belong only to this composition control leaf.
(in-package "ACL2")
(include-book "cns-draining-contract-unit")
(include-book "../sim/check-trace")

; Q1 is exercised separately from the independent oracle, using its real
; per-case lockstep checker and a reference copied before the transition.
(defun fn2-cns-drain-q1-run (fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* (((mv setup id & fn2-core) (fn2-cns-drain-setup nil fn2-core))
       (fn2-core (fn2-exec-wake id fn2-core))
       (fn2-ref-core (fn2-ref-reset *fn2-cns-drain-profile* fn2-core fn2-ref-core))
       (lists (fn2-ref-lists-of-core (fn2-profile-weights *fn2-cns-drain-profile*) fn2-core))
       ((mv verdict & & & & & & tallies fn2-core fn2-ref-core)
        (fn2-check-trace-cases-turn *fn2-cns-drain-profile* (nth 1 lists) (nth 2 lists)
                                  fn2-core fn2-ref-core)))
    (mv (list setup verdict (cdr (assoc-equal '(:run fn2-cns :draining) (car tallies))))
        fn2-core fn2-ref-core)))
(defun fn2-cns-drain-q1-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (with-local-stobj fn2-ref-core
        (mv-let (result fn2-core fn2-ref-core) (fn2-cns-drain-q1-run fn2-core fn2-ref-core)
          (mv result fn2-core))) result)))
(assert-event (let ((r (fn2-cns-drain-q1-control)))
                (and (car r) (eq (cadr r) :pass) (posp (caddr r)))))
