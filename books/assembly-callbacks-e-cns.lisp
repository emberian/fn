; The Layer E control and consumer continuations (books/cns.lisp), in their
; own leaf section book so arm-body edits do not invalidate assembly.cert or executor.cert.
; After the published grants' exact reads (authority.lisp's
; fn2-auth-read-events): a consumer request's :check calls fn2-cns-authority-allows.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "cns")
(include-book "authority")
(include-book "xfnc-reader")
(include-book "xfnc-view")
(include-book "xfnc-ops")
(include-book "xfnc-request")
(include-book "xfnc-reply")
(fn2-auth-read-events)
(fn2-authority-depend-events)
(fn2-xfnc-view-events)
(fn2-cns-events)
(fn2-xfnc-request-events)
(fn2-xfnc-register-reply-events)
