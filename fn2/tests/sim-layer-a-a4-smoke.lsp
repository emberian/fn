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
      (assert (fn2-client-oracle-control))
      (assert (eq (car (fn2-sim-run-echo 1234 10 *fn2-echo-profile*)) :pass))
      (assert (eq (car (fn2-sim-run-scribe)) :pass))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "A4 SMOKE FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
