; Native launcher loading certified node books; no seeded fixture state.
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(include-book "books/node-profile" :uncertified-okp nil)
; The qualified native attachment also replaces the Merkle compression entry.
(include-book "books/merkle" :uncertified-okp nil)
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
:q
; Qualify native crypto before opening a store or binding a listener.
(handler-case (load "host/b3-native.lisp")
  (error (c)
    (format *error-output* "REFUSED native-crypto: ~A~%" c)
    (sb-ext:exit :code 2)))
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(load "host/native-serve-raw.lisp")
(setf *fn2-nserve-base* *fn2-node-profile*)
(sb-ext:exit :code (fn2-nserve-main))
