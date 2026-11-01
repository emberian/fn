; Controlled client environment for the real layer-A machines.  Unlike the
; A3 pool workload, accept does not invent client bytes and advance does not
; drain them invisibly: the independent client oracle supplies/checks both.
(in-package "ACL2")
(include-book "sim")

; Shape contracts already describe every adapter boundary; tau would repeat
; compound type propagation across every nested state in all six projections.
(local (in-theory (disable (tau-system))))

(defun fn2-sim-echo-network-reset (fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
    (fn2-sim-network) (fn2-network-restart fn2-sim-network) fn2-sim))
(fn2-sim-preserves fn2-sim-echo-network-reset (fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-sim-echo-network-reset) (w state)))
