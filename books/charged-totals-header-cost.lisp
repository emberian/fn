; Visit bounds for the charged-totals header's host-called entries
; (books/charged-totals-header.lisp; tools/cost_obligations.py reads them).
; Each :visits bound is partial over the callees named :unaccounted;
; def-cost checks that list against the executed body's unaccounted set.
(in-package "ACL2")
(include-book "image-world")
(include-book "memory-entry-cost")
(include-book "def-cost")
(include-book "charged-totals-header")
(local (in-theory (enable adt-nth-0 adt-nth-1+)))

(local
 (defthm fn-cth-mm-nat-visits-explicit
   (equal (fn-mm-nat-visits i x)
          (+ 1 (nfix i) (fn-cost-unaccounted 'true-list-fix (list x))))
   :hints (("Goal" :in-theory (enable fn-mm-nat-visits)))))
(local
 (defthm fn-cth-mm-paged-visits-explicit
   (implies (fn-mm-tot-p tot)
            (equal (fn-mm-tot-paged-p-visits tot)
                   (+ 10 (fn-cost-unaccounted 'true-list-fix (list tot)))))
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
                       '(fn-mm-tot-p fn-mm-tot-paged-p-visits fn-rtc-true-list-fix-identity))))))

(def-cost fn-cth-status-text
  :visits (+ 106 (* 3 n) l)
  :sizes ((n (len (cadr open)))
          (l (len (fn-cth-status-text open))))
  :unaccounted (fn-cth-status-field true-list-fix fn-nls-text)
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'ground-zero)
            '(fn-cth-status-text fn-cth-status-text-visits
              fn-cth-status-text-route-visits
              fn-mm-tot-records-visits fn-mm-tot-arena-visits
              fn-mm-tot-hcharge-visits fn-mm-tot-memberships-visits
              fn-mm-tot-events-visits fn-mm-tot-log-visits
              fn-mm-tot-history-visits fn-mm-tot-charge-visits
              fn-cth-mm-nat-visits-explicit fn-cth-mm-paged-visits-explicit
              fn-cost-unaccounted-natp fn-rtc-len-append)))))

(def-cost fn-cth-table-initial-state :visits 0 :unaccounted (fn-ockp-initial-state update-nth))

(def-cost fn-cth-header-open
  :visits (+ 56 (* 3 n))
  :sizes ((n (len (fn-cth-header-tot (list seg)))))
  :unaccounted (fn-scc-octet-listp fn-cth-segment-bound fn-cth-admit-run fn-cth-header-tot fn-cth-config-cfg
                fn-mm-checkpoint-load-octets fn-scc-parse-header)
  :hints (("Goal" :in-theory (disable fn-cth-segment-bound fn-cth-admit-run fn-cth-header-tot
                                    fn-cth-config-cfg fn-mm-checkpoint-load-octets
                                    fn-scc-parse-header fn-scc-octet-listp))))
