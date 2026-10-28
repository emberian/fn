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
                    (ld "sim-fault-controls.lisp" :ld-error-action :error)
                    (ld "sim-replay-controls.lisp" :ld-error-action :error)
                    (set-guard-checking nil)
                    (assert-event (eq (fn2-scenario-controls) :pass))
                    (assert-event (eq (fn2-sim-fault-controls) :pass))
                    (assert-event (eq (fn2-sim-recovery-controls) :pass))
                    (assert-event (fn2-sim-replay-control))
                    (assert-event (mv-let (passes failure)
                                    (fn2-sim-run-pool-scenarios 0 2 *fn2-profile-tiny*)
                                    (and (equal passes 2) (null failure))))
                    (assert-event (mv-let (passes failure)
                                    (fn2-sim-run-pool-scenarios 0 2 *fn2-profile-tiny-near-limit*)
                                    (and (equal passes 2) (null failure))))) :ld-error-action :error)))
        (declare (ignore state))
        (assert (and (not erp) (eq value :eof))))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "SIM-LAYER-A-SMOKE FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
