; The cost of the read-only probe's suffix-scan entries (landing 2a-host):
; the plan over journal/'s names, the fold host/native/heap.lisp
; fnn-heap-log-suffix calls once per record, the head's start and the
; settled answer after the walk.
(in-package "ACL2")
(include-book "image-world")
(include-book "def-cost")
(include-book "store-log-open-scan")

(def-cost fn-lgo-fold :unaccounted (fn-lzr-dictsp fn-lgo-add))
(def-cost fn-lgo-scan-plan
  :unaccounted (fn-lgs-indices fn-lgs-max-index fn-lgo-min-index fn-lgs-open-plan))

(def-cost fn-lgo-head-genesis
  :unaccounted (fn-lgl-headed-p fn-lgl-head-index fn-lgl-head-prev))
(def-cost fn-lgo-suffix-settled)

(def-cost-check fn-lgo-scan-plan)
(def-cost-check fn-lgo-fold)
