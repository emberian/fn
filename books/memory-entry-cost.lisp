; The derived visit costs of the memory model's dispatched entries (memory
; landings 2 and 3+4a; RED from cost_obligations --check, routed by the
; coordinator 2026-10-10).  Each is `def-cost' with no declared bound: the
; twin is derived from the entry's executed body and the :unaccounted list is
; exactly the derived one (D27: nothing declared, nothing pinned).  The
; unaccounted callees are the list walks the trusted base does not cost
; (true-list-fix under the nine-field totals and the collector
; configuration; fn-mo-skip-blanks, whose twin's measure is not admitted
; outside its consp ruler) and the four heap decisions fn-heap-command-decide
; dispatches to, each its own book's figure.
(in-package "ACL2")
(include-book "def-cost")
(include-book "heap-command")
(include-book "heap-reservation")
(include-book "memory-model")

(def-cost fn-mm-nat :unaccounted (true-list-fix))
(def-cost fn-heap-command-growth)
(def-cost fn-mm-tot-records :unaccounted (true-list-fix))
(def-cost fn-mm-tot-arena :unaccounted (true-list-fix))
(def-cost fn-mm-tot-hcharge :unaccounted (true-list-fix))
(def-cost fn-mm-tot-memberships :unaccounted (true-list-fix))
(def-cost fn-mm-tot-events :unaccounted (true-list-fix))
(def-cost fn-mm-tot-log :unaccounted (true-list-fix))
(def-cost fn-mm-tot-history :unaccounted (true-list-fix))
(def-cost fn-mm-tot-charge :unaccounted (true-list-fix))
(def-cost fn-mm-tot-paged-p :unaccounted (true-list-fix))
(def-cost fn-mm-tot-plus :unaccounted (true-list-fix))
(def-cost fn-mm-observed-tot :unaccounted (true-list-fix))
(def-cost fn-mo-tot-log-at-least :unaccounted (true-list-fix))
(def-cost fn-mo-observed-totals :unaccounted (true-list-fix))
(def-cost fn-mo-prefixp)
(def-cost fn-mo-drop-key)
(def-cost fn-mo-digits)
(def-cost fn-mo-after-line)
(def-cost fn-mo-status-kib-octets :unaccounted (fn-mo-skip-blanks))
(def-cost fn-mo-img-observed :unaccounted (fn-mo-skip-blanks))
(def-cost fn-heap-stack-kib)
(def-cost fn-mm-collector-cfg)
(def-cost fn-mm-cfg-rho :unaccounted (true-list-fix))
(def-cost fn-mm-cfg-trigger :unaccounted (true-list-fix))
(def-cost fn-mm-collector :unaccounted (true-list-fix))
(def-cost fn-mm-collector-due-p :unaccounted (true-list-fix))
(def-cost fn-heap-command-decide :unaccounted (fn-mo-header-decide fn-heap-reserve-operation-decide fn-mo-read-decide fn-mo-offline-adapter-decide))
(def-cost fn-heap-command-line :unaccounted (fn-mo-read-refusal-line fn-heap-reserve-report-line fn-mo-unseen-suffix string-append))

(def-cost-check fn-heap-command-growth)
(def-cost-check fn-mo-observed-totals)
(def-cost-check fn-mo-img-observed)
(def-cost-check fn-heap-stack-kib)
(def-cost-check fn-mm-collector-cfg)
(def-cost-check fn-mm-collector-due-p)
(def-cost-check fn-heap-command-decide)
(def-cost-check fn-heap-command-line)
