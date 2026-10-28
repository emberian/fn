(in-package "ACL2")
:q
(handler-case
    (progn
      ; LD needs LP's loading context; ACL2 errors are returned as values.
      (multiple-value-bind (erp value state)
          (let ((*features* (adjoin :acl2-loop-only *features*)))
            (with-suppression
              (ld '((set-prover-step-limit 300000)
                    (set-cbd "fn2/tests/")
                    (ld "core-allocation.lisp" :ld-error-action :error)) :ld-error-action :error)))
        (declare (ignore state))
        (assert (and (not erp) (eq value :eof))))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "CORE-ALLOCATION-DRIVER FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
