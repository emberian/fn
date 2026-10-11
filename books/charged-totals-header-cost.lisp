; The cost rows of the charged-totals header's host-called entries
; (books/charged-totals-header.lisp; tools/cost_obligations.py reads them):
; each entry's visit twin derived from its executed body, partial over the
; callees named :unaccounted (the record accessors of M's tot, the header's
; admission and decode, the table pipeline's first state), which def-cost
; checks equal to the derived set.  No :visits bound is declared: the claim
; is `derived'.
(in-package "ACL2")
(include-book "def-cost")
(include-book "charged-totals-header")

(def-cost fn-cth-empty-suffix :unaccounted (fn-mm-tot-paged-p))

(def-cost fn-cth-status-text
  :unaccounted (fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                fn-cth-status-field fn-mm-tot-paged-p fn-nls-text))

(def-cost fn-cth-table-initial-state :unaccounted (fn-ockp-initial-state update-nth))

(def-cost fn-cth-header-open
  :unaccounted (fn-cth-segment-bound fn-cth-admit-run fn-cth-header-tot fn-cth-config-cfg
                fn-mm-checkpoint-load-octets fn-scc-parse-header))
