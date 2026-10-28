; Run command is in blake3-vectors.lisp; root-relative invocation.
(in-package "ACL2")
(include-book "fn2/books/blake3")
(include-book "fn2/sim/prng")
:q
(load "fn2/tests/blake3-vectors.lisp")
(handler-case
    (progn (fn2-b3-test-all) (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "B2B ACCEPTANCE ERROR: ~A~%" condition)
    (sb-ext:exit :code 1)))
