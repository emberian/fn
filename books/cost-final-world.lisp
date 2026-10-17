; Check every derived cost row against the final image world.  Entry routes
; and callee cost rows are world facts, so rederive after all are present.
(in-package "ACL2")
(include-book "image-world")
(include-book "memory-entry-cost")
(include-book "charged-totals-header-cost")
(include-book "heap-log-extent-cap-cost")
(include-book "reclaim-chunked-cost")
(include-book "runtime-contract-host-lease-cost")
(include-book "store-log-buffer-cost")
(include-book "store-log-open-scan-cost")
(include-book "string-line-cursor-cost")
(include-book "def-cost-lambda-tests")
(include-book "page-read-issue-source-cost")
(include-book "allocation-turn-source-cost")
(include-book "../host/cost-host")

(def-cost-check-all)
