; Native launcher loading certified node books; no seeded fixture state.
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(include-book "books/node-profile")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
:q
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(load "host/native-serve-raw.lisp")
(setf *fn2-nserve-base* *fn2-node-profile*)
(sb-ext:exit :code (fn2-nserve-main))
