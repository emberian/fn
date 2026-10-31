; Generate machine access to the assembled core.
(in-package "ACL2")
(include-book "core-child-assembly-core")

(fn2-account-events)
(fn2-machine-access-events)
; the ledger's request FIFO and its grant source, as assembly-access.lisp runs
; them (D7 4/n-a): the :principal-reservation defwait names their park op
(fn2-account-request-events)
(fn2-machine-row-events)
