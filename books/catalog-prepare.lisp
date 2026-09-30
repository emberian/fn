; Exact actual prepare producer, factored without changing its body or guard.
(in-package "ACL2")
(include-book "catalog")
(include-book "catalog-prepared-record")

(defun fn-cat-prepare (w plan reservation fn-octets keyring generation pending
                         fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if pending
      (mv (list :pending) fn-arena)
    (mv-let (held fn-arena)
      (fn-cat-intern w fn-octets keyring generation fn-arena)
      (let ((expected (fn-cat-count fn-cat)))
        (mv (fn-pc-make (cons (nfix (fn-record-txid w)) expected)
                        expected held plan reservation)
            fn-arena)))))
