; Unchanged exact item encoder semantic function.
(in-package "ACL2")
(include-book "statement-items-shape")
(local (in-theory (enable fn-cbor-codec-vocabulary)))

(defun fn-stmt-encode-items-impl (items)
  (declare (xargs :guard (fn-stmt-item-listp items)))
  (if (consp items)
      (append (fn-cbor-encode (car items))
              (fn-stmt-encode-items-impl (cdr items)))
    nil))
(in-theory (disable fn-stmt-encode-items-impl))
