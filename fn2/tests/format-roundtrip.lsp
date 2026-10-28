(in-package "ACL2")
(set-prover-step-limit 300000)
(set-cbd "fn2/tests/")
(ld "format-roundtrip.lisp" :ld-error-action :error)
:q
(handler-case
    (progn (assert (equal (fn2-format-test-all) t)) (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "B2C ROUNDTRIP ERROR: ~A~%" condition)
    (sb-ext:exit :code 1)))
