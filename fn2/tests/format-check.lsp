(in-package "ACL2")
(include-book "fn2/tests/format-check-unit")
:q
(handler-case
 (progn (load "fn2/tests/format-check.lisp") (fn2-fc-test-all) (sb-ext:exit :code 0))
 (cl:error (e) (format *error-output* "B2D ACCEPTANCE ERROR: ~A~%" e) (sb-ext:exit :code 1)))
