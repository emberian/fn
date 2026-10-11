; The cost of the read-only probe's suffix-scan entries (landing 2a-host):
; the plan over journal/'s names and the fold host/native/heap.lisp
; fnn-heap-log-suffix calls once per record.
(in-package "ACL2")
(include-book "def-cost")
(include-book "store-log-open-scan")

(def-cost fn-lgo-scan-plan)
(def-cost fn-lgo-fold)

(def-cost-check fn-lgo-scan-plan)
(def-cost-check fn-lgo-fold)
