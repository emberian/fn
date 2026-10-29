; Every command uses FN_ACL2_SLOT_DIR=/tmp/fn2-bh1-acl2-slots FN_ACL2_SLOTS=4.
(in-package "ACL2")
(include-book "fn2/tests/format-check-unit")
(include-book "fn2/books/merkle")
(include-book "fn2/sim/prng")
:q
(handler-case
 (progn
  (load "fn2/tests/blake3-vectors.lisp")
  (load "fn2/tests/format-check.lisp")
  (load "fn2/host/b3-native.lisp")
  (load "fn2/tests/blake3-native.lisp")
  (fn2-bh1-all)
  (sb-ext:exit :code 0))
 (cl:error (c) (format *error-output* "BH1 ACCEPTANCE ERROR: ~A~%" c) (sb-ext:exit :code 1)))
