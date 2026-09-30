; Exact canonical admission projections, extracted without changing bodies or guards.
(in-package "ACL2")
(include-book "acceptance-alloc")

(defun fn-ocfg-owner (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-own-next-id (o)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr o))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr o))))))

(defun fn-own-store (o)
  (declare (xargs :guard t))
  (mbe :logic (car o) :exec (fn-ag-car o)))
