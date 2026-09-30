; Exact unchanged scalar exposure selectors.
(in-package "ACL2")

(defun fn-exp-at (i x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (consp x)
      (if (or (not (integerp i)) (<= i 0)) (car x) (fn-exp-at (1- i) (cdr x)))
    nil))

(defun fn-exp-nat (i x)
  (declare (xargs :guard t))
  (nfix (fn-exp-at i x)))

(defun fn-exp-lim-steps (l) (declare (xargs :guard t)) (fn-exp-nat 3 l))
