; Exact descriptor effects for the actual source issuer. Reuse the same
; typed OPS proof producers as pinned physical I/O; do not redefine the
; metric as attempt/admission credit. This book changes no runtime body.
(in-package "ACL2")
(include-book "cns-source-raw")
(fn2-book-layer :d)
; The queue/history producer facts already follow the nested block issue.
; Keep admission predicates and column storage opaque while composing them.
(local
 (make-event
  (value (list 'in-theory
          (cadr (fn2-columns-call-guard-hint 'fn2-cns-source-issue-children
                 '(fn2-cns-source-ownerp fn2-op-slotp min
                   fn2-cns-source-heldp fn2-cns-source-data-position-p
                   fn2-pool-workspace-code fn2-pool-truncate fn2-block-read-children)
                 nil (w state)))))))
(make-event
 (value (cons 'progn
  (append (fn2-issue-wrapper-effect-events '(fn2-cns-source-issue-children) (w state))
          (fn2-issued-wrapper-events '(fn2-cns-source-issue-children) (w state))))))
