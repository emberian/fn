; Every command uses FN_ACL2_SLOT_DIR=/tmp/fn2-bh1-acl2-slots FN_ACL2_SLOTS=4.
(in-package "ACL2")
(include-book "tests/format-check-unit")
(include-book "books/merkle")
(include-book "sim/prng")
:q
(handler-case
 (progn
  (load "tests/blake3-vectors.lisp")
  (load "tests/format-check.lisp")
  (load "host/b3-native.lisp")
  (load "tests/blake3-native.lisp")
  (fn2-bh1-all)
  (sb-ext:exit :code 0))
 (cl:error (c) (format *error-output* "BH1 ACCEPTANCE ERROR: ~A~%" c) (sb-ext:exit :code 1)))
