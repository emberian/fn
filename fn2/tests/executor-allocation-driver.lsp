; Scoped steady echo meter: concrete geometry, TRACE on, adapter faults off.
; Clients retain random fragmentation and orderly/random disconnects. The
; sampled region is only fn2-turn, excluding init, clients and all checkers.
(in-package "ACL2")
(set-prover-step-limit 300000)
(set-cbd "fn2/tests/")
(ld "sim-layer-a.lisp" :ld-error-action :error)
(set-guard-checking nil)
:q
(load "turn-meter.lsp")
(handler-case
    (progn
      (fn2-meter-install)
      (unwind-protect
          (progn
            (fn2-meter-control)
            (let ((result (fn2-sim-run-echo-profile 20261029 1000 *fn2-echo-profile* :none)))
              (assert (eq (car result) :pass))
              (assert (= (second result) 1000))
              (assert (= (+ (third result) (fourth result)) 1000))
              (assert (>= (third result) 500))
              (assert (= (nth 7 result) 0))
              (assert (= *fn2-meter-calls* (sixth result))))
            (fn2-meter-report "STEADY ECHO TURN CPU profile=CONCRETE-TRACE adapter-faults=NONE"))
        (fn2-meter-restore))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "STEADY ECHO MEASUREMENT FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
