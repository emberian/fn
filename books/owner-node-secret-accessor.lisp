; Exact unchanged owner accessor, factored for the operational writer.
(in-package "ACL2")
(include-book "acceptance-alloc")

(defun fn-own-node-secret (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr o))))))))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))))))))))))
