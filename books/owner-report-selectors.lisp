; Unchanged total positional selectors used by actual report accessors.
(in-package "ACL2")
(include-book "acceptance-alloc")

(defun fn-bp-nth (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (not (and (integerp n) (fn-ag-less 0 n)))
      (fn-ag-car x)
    (fn-bp-nth (1- n) (fn-ag-cdr x))))

(defun fn-frame-item (n xs)
  (declare (xargs :guard (natp n)))
  (if (consp xs)
      (if (zp n) (car xs) (fn-frame-item (- n 1) (cdr xs)))
    nil))
