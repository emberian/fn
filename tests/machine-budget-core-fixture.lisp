; Small real layer-A core for quantitative dispatch/attachment proofs.
; Uses the same registration, access and callback generators as the served core.
(in-package "ACL2")
(include-book "../books/machines-a-run")
(include-book "../books/accounts-core")

(fn2-machine-index-events)
(in-theory (disable fn2-machine-local-id))
(fn2-machine-directory-events)
(fn2-core-events)
(fn2-core-init-events)
(fn2-account-events)
(fn2-machine-access-events)
(fn2-account-request-events)
(fn2-machine-row-events)
(fn2-machine-admission-events)
(fn2-scribe-events)
(fn2-machine-a-events)
