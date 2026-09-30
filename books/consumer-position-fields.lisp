; Unchanged consumer scalar fields shared by pure readout books.
(in-package "ACL2")
(include-book "cbor")

(defun fn-cp-uintp (x)
  (and (natp x) (<= x *fn-cbor-max-uint*)))

(defun fn-cp-nth (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      (if (consp x) (car x) nil)
    (fn-cp-nth (1- n) (if (consp x) (cdr x) nil))))

(verify-guards fn-cp-uintp)
