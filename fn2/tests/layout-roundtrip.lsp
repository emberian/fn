(in-package "ACL2")
(set-prover-step-limit 300000)
(set-cbd "fn2/tests/")
(ld "layout-roundtrip.lisp" :ld-error-action :error)
; Session-only compiled test execution, as in crash-model-differential.lsp.
:q
(handler-case
    (progn (assert (equal (fn2-layout-test-all) t)) (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "B2A ROUNDTRIP ERROR: ~A~%" condition)
    (sb-ext:exit :code 1)))
