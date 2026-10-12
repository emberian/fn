; Visit bounds for the charged-totals header's host-called entries
; (books/charged-totals-header.lisp; tools/cost_obligations.py reads them).
; Each :visits bound is partial over the callees named :unaccounted;
; def-cost checks that list against the executed body's unaccounted set.
(in-package "ACL2")
(include-book "image-world")
(include-book "memory-entry-cost")
(include-book "def-cost")
(include-book "charged-totals-header")

(def-cost fn-cth-status-text
  :visits (+ 64 (* 3 n) l)
  :sizes ((n (len (cadr open)))
          (l (len (fn-cth-status-text open))))
  :unaccounted (fn-cth-status-field true-list-fix fn-nls-text)
  :hints (("Goal" :in-theory (disable fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge
                                    fn-mm-tot-memberships fn-mm-tot-events fn-mm-tot-log
                                    fn-mm-tot-history fn-mm-tot-charge fn-mm-tot-paged-p
                                    fn-cth-status-field fn-nls-text))))

(def-cost fn-cth-table-initial-state :visits 0 :unaccounted (fn-ockp-initial-state update-nth))

(def-cost fn-cth-header-open
  :visits (+ 56 (* 3 n))
  :sizes ((n (len (fn-cth-header-tot (list seg)))))
  :unaccounted (fn-scc-octet-listp fn-cth-segment-bound fn-cth-admit-run fn-cth-header-tot fn-cth-config-cfg
                fn-mm-checkpoint-load-octets fn-scc-parse-header)
  :hints (("Goal" :in-theory (disable fn-cth-segment-bound fn-cth-admit-run fn-cth-header-tot
                                    fn-cth-config-cfg fn-mm-checkpoint-load-octets
                                    fn-scc-parse-header fn-scc-octet-listp))))
