; Scoped steady echo meter: concrete geometry, TRACE on, adapter faults off.
; Clients retain random fragmentation and orderly/random disconnects. The
; sampled region is only fn2-turn, excluding init, clients and all checkers.
(in-package "ACL2")
:q
(handler-case
    (progn
      ; Generate this run's revision before any scenario is loaded.
      (let ((process (sb-ext:run-program "python3" '("fn2/tests/scenario-revision.py")
                       :search t :output "build/scenario-revision.lsp"
                       :if-output-exists :supersede :error *error-output*)))
        (assert (eql (sb-ext:process-exit-code process) 0)))
      ; LD needs LP's loading context; ACL2 errors are returned as values.
      (multiple-value-bind (erp value state)
          (let ((*features* (adjoin :acl2-loop-only *features*)))
            (with-suppression
              (ld '((set-prover-step-limit 300000)
                    (set-cbd "fn2/tests/")
                    (ld "sim-layer-a.lisp" :ld-error-action :error)
                    (set-guard-checking nil)) :ld-error-action :error)))
        (declare (ignore state))
        (assert (and (not erp) (eq value :eof))))
      (load "fn2/tests/turn-meter.lsp")
      (fn2-meter-install)
      (unwind-protect
          (progn
            (fn2-meter-control)
            (let ((result (fn2-sim-run-echo-profile 20261029 1000 *fn2-echo-profile* :none)))
              (assert (eq (car result) :pass))
              (assert (= (second result) 1000))
              (assert (= (+ (third result) (fourth result)) 1000))
              (assert (>= (third result) 500))
              (assert (zerop (fn2-echo-stat :unattributed (nth 7 result))))
              (assert (= (length (nth 8 result)) 26))
              (assert (every (lambda (entry) (zerop (cdr entry))) (nth 8 result)))
              (assert (= *fn2-meter-calls* (sixth result))))
            (fn2-meter-report "STEADY ECHO TURN CPU profile=CONCRETE-TRACE adapter-faults=NONE"))
        (fn2-meter-restore))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "STEADY ECHO MEASUREMENT FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
