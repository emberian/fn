(in-package "ACL2")
(include-book "books/merkle")
:q
(load "tests/merkle-random.lisp")
(handler-case (progn (fn2-mk-test-all) (sb-ext:exit :code 0))
 (cl:error (c) (format *error-output* "B2E ACCEPTANCE ERROR: ~A~%" c) (sb-ext:exit :code 1)))
