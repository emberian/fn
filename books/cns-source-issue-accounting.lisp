; Exact descriptor effects for the actual source issuer. Reuse the same
; typed OPS proof producers as pinned physical I/O; do not redefine the
; metric as attempt/admission credit. This book changes no runtime body.
(in-package "ACL2")
(include-book "cns-source-raw")
(fn2-book-layer :d)
(make-event
 (value (cons 'progn
  (append (fn2-issue-wrapper-effect-events '(fn2-cns-source-issue-children) (w state))
          (fn2-issued-wrapper-events '(fn2-cns-source-issue-children) (w state))))))
