; Existing generated Close subarm violates the universal residual claim at budget zero.
; All child recognizers, guards and natural-budget hypotheses hold. Both the returned
; descriptor and physical outbox/free-list/row effects are observed, without a stop.
(in-package "ACL2")
(include-book "machine-arms-probe-fixture")

(make-event
 (mv-let (errs subs events)
   (fn2-arms-subs 'fn2-arms-probe (fn2-machine-declared 'fn2-arms-probe :subarms (w state)) nil nil nil :children (w state))
   (declare (ignore subs))
   (if errs (er soft 'assurance-budget "~x0" errs) (value (cons 'progn events)))))

(defun fn2-budget-counterexample-run (budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) :verify-guards nil))
 (b* ((fn2-arms-probe (fn2-arms-probe-prepare 1 0 1 fn2-arms-probe))
      (fn2-arms-probe (fn2-arms-probe-put 0 (generation 1) (phase *fn2-arms-probe-state-work*) (cap-index 7) (cap-nonce 9)))
      (fn2-machines (fn2-machines-columns-init 1 fn2-machines))
      (fn2-machines (fn2-machines-put 0 (kind 4) (slot 0)))
      (fn2-pool (fn2-pool-init '((2 . 64)) 1 100 fn2-pool))
      (fn2-ops (fn2-ops-init *fn2-profile-tiny* fn2-ops))
      (fn2-control (fn2-control-init *fn2-profile-tiny* fn2-control))
      (hyps (and (natp budget) (fn2-arms-probep fn2-arms-probe) (fn2-machinesp fn2-machines)
                 (fn2-poolp fn2-pool) (fn2-opsp fn2-ops) (fn2-controlp fn2-control)
                 (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines)
                 (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control)
                 (< 0 (fn2-arms-probe-rows fn2-arms-probe)) (< 0 (fn2-machines-rows fn2-machines))))
      (before (list (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines)
                    (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control)
                    (fn2-ops-queued fn2-ops) (fn2-ops-free-count fn2-ops)
                    (fn2-arms-probe-phase 0 fn2-arms-probe) (fn2-arms-probe-pending 0 fn2-arms-probe)))
      ((mv bytes steps descriptors runnable fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)
       (fn2-arms-probe-sub-close-children 0 0 4 0 budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control))
      ((mv peek op gen) (fn2-outbox-peek 0 fn2-ops)))
  (mv (list budget hyps before (list bytes steps descriptors runnable)
            (list (fn2-arms-probe-wfp fn2-arms-probe) (fn2-machines-wfp fn2-machines)
                    (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control)
                    (fn2-ops-queued fn2-ops) (fn2-ops-free-count fn2-ops)
                    (fn2-arms-probe-phase 0 fn2-arms-probe) (fn2-arms-probe-pending 0 fn2-arms-probe)
                    (fn2-control-stop-reason fn2-control))
            (list peek op gen)) fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control)))

(defun fn2-budget-counterexample (budget) (declare (xargs :verify-guards nil)) (with-local-stobj fn2-arms-probe (mv-let (answer fn2-arms-probe) (with-local-stobj fn2-machines (mv-let (answer fn2-arms-probe fn2-machines) (with-local-stobj fn2-pool (mv-let (answer fn2-arms-probe fn2-machines fn2-pool) (with-local-stobj fn2-ops (mv-let (answer fn2-arms-probe fn2-machines fn2-pool fn2-ops) (with-local-stobj fn2-control (mv-let (answer fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) (fn2-budget-counterexample-run budget fn2-arms-probe fn2-machines fn2-pool fn2-ops fn2-control) (mv answer fn2-arms-probe fn2-machines fn2-pool fn2-ops))) (mv answer fn2-arms-probe fn2-machines fn2-pool))) (mv answer fn2-arms-probe fn2-machines))) (mv answer fn2-arms-probe))) answer)))
(assert-event
 (equal (fn2-budget-counterexample 0)
        '(0 t (t t t t t 0 8 1 0) (0 12 1 nil) (t t t t t 1 7 2 1 0) (:ok 0 1))))
(assert-event
 (equal (fn2-budget-counterexample 1)
        '(1 t (t t t t t 0 8 1 0) (0 12 1 nil) (t t t t t 1 7 2 1 0) (:ok 0 1))))
