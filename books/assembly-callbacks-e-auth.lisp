; The Layer E authority requests' continuations (books/authority.lisp), in
; their own leaf section book after the control connection's (fn2-ctl takes
; their rows), so arm-body edits do not invalidate assembly.cert or executor.cert.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")
(include-book "authority")
(fn2-auth-events)
