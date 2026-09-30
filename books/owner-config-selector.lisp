; Exact configuration projection, independent of full owner transition graph.
(in-package "ACL2")
(include-book "acceptance-alloc")
(defun fn-ocfg-config (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
