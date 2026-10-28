(in-package "ACL2")
(set-prover-step-limit 300000)
(set-cbd "fn2/tests/")
(ld "sim-layer-a.lisp" :ld-error-action :error)
(set-guard-checking nil)
:q
(handler-case
    (progn
      (assert (fn2-client-oracle-control))
      (assert (eq (car (fn2-sim-run-echo 1234 10 *fn2-echo-profile*)) :pass))
      (assert (eq (car (fn2-sim-run-scribe)) :pass))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "A4 SMOKE FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
