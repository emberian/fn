; Standalone real-fd correspondence test. No listener or service starts.
; Qualification may load these exact source books into one retained world and
; run the raw half there, avoiding a second dependency load.
(in-package "ACL2")
(include-book "tests/native-fence-correspondence" :uncertified-okp nil)
:q
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(load "tests/native-fence-return-raw.lisp")
(handler-case
 (progn
  (assert (fn2-native-fence-return-control))
  (sb-ext:exit :code 0))
 (error (condition)
  (format *error-output* "NATIVE FENCE RETURN FAIL: ~a~%" condition)
  (sb-ext:exit :code 1)))
