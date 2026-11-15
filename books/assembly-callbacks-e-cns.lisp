; The Layer E control and consumer continuations (books/cns.lisp), in their
; own leaf section book so arm-body edits do not invalidate assembly.cert or executor.cert.
; After the published grants' exact reads (authority.lisp's
; fn2-auth-read-events): a consumer request's :check calls fn2-cns-authority-allows.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "cns")
(include-book "authority")
(include-book "c-actor-loader")
(include-book "run-physical-readiness-core")
(include-book "checkpoint-live-finish")
(fn2-c-actor-loader-core-events)
(fn2-run-load-readiness-core-events)
(fn2-checkpoint-live-finish-events)
(make-event
 (mv-let (err events) (fn2-run-loader-core-face-events '(fn2-checkpoint-live-replace-finish-op) (w state))
  (if err (er soft 'fn2-checkpoint-live-finish-core-face "~@0" err) (value (cons 'progn events)))))
(fn2-auth-read-events)
(fn2-cns-events)
