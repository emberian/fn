; Exact actual Store files projection, no Store transition dependency.
(in-package "ACL2")
(include-book "acceptance-alloc")
(defun fn-sn-files (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (caddr s)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))
(verify-guards fn-sn-files)
