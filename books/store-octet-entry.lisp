; Exact field-string alias extracted from host/store-host.lisp.
(in-package "ACL2")
(include-book "records")
(defun fn-store-octets->string (xs)
  (declare (xargs :guard t))
  (fn-record-octets-string xs))
(in-theory (disable fn-store-octets->string))
