(in-package "ACL2")
(include-book "machine-budget-core-fixture")

; The real closing callback: all typed guard antecedents, declared charge,
; unconditional residual bound, and physical queue delta are checked together.
(defun fn2-budget-core-witness-run (budget fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
      (id (fn2-machine-global-id *fn2-echo-kind* 0 *fn2-profile-tiny*))
      (fn2-core (fn2-echo-put-core id (phase *fn2-echo-state-closing*) (cap-index 7) (cap-nonce 9)))
      (hyps (and (natp budget) (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (fn2-machine-idp id fn2-core) (equal (fn2-machine-kind id fn2-core) *fn2-echo-kind*)))
      (phase (fn2-machine-phase id fn2-core))
      ((mv bytes steps descriptors runnable fn2-core) (fn2-echo-run id budget fn2-core))
      (charged (fn2-echo-arm-charge-ok-p phase bytes steps descriptors))
      (quantities (fn2-run-quantitiesp bytes steps descriptors budget 4128))
      (queued (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (q) (fn2-ops-queued fn2-ops) q)))
  (mv (list hyps (list bytes steps descriptors runnable) quantities charged queued
            (fn2-machine-phase id fn2-core) (fn2-machine-pending id fn2-core)
            (fn2-core-success-p fn2-core)) fn2-core)))
(defun fn2-budget-core-witness (budget)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (answer fn2-core)
   (fn2-budget-core-witness-run budget fn2-core) answer)))
(assert-event
 (equal (fn2-budget-core-witness 0) '(t (0 1 0 t) t t 0 3 0 t)))
(assert-event
 (equal (fn2-budget-core-witness 1) '(t (0 8 1 nil) t t 1 3 1 t)))

; Structural WFP does not imply stop/reason coherence. A clear reason alone
; is not success; quantitative contracts still cover this admitted state.
(defun fn2-budget-core-stopped-control-run (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
      (fn2-core (stobj-let ((fn2-control (fn2-core-control fn2-core)))
                  (fn2-control) (update-fn2-control-stop 1 fn2-control) fn2-core)))
  (mv (list (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
            (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*)
            (fn2-core-success-p fn2-core)) fn2-core)))
(defun fn2-budget-core-stopped-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (answer fn2-core)
   (fn2-budget-core-stopped-control-run fn2-core) answer)))
(assert-event (equal (fn2-budget-core-stopped-control) '(t t t nil)))
