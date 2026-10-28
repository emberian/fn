(in-package "ACL2")
(include-book "fn2/books/merkle")
:q
(load "fn2/tests/merkle-random.lisp")
(handler-case (progn (fn2-mk-test-all) (sb-ext:exit :code 0))
 (cl:error (c) (format *error-output* "B2E ACCEPTANCE ERROR: ~A~%" c) (sb-ext:exit :code 1)))
