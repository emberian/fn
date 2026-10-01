; Unchanged pure statement item shape, independent of identity/crypto.
(in-package "ACL2")
(include-book "cbor")

(defun fn-stmt-item-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cbor-valuep (car xs))
           (fn-stmt-item-listp (cdr xs)))
    (null xs)))

(defthm fn-stmt-item-listp-implies-true-listp
  (implies (fn-stmt-item-listp xs) (true-listp xs)))

(defthm fn-stmt-item-listp-nth-is-item-or-nil
  (implies (fn-stmt-item-listp xs)
           (or (consp (nth n xs)) (equal (nth n xs) nil)))
  :rule-classes ((:type-prescription :typed-term (nth n xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-valuep fn-cbor-valuep-bounded))))
(in-theory (disable fn-stmt-item-listp-implies-true-listp fn-stmt-item-listp-nth-is-item-or-nil))
